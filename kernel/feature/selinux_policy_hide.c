// SPDX-License-Identifier: GPL-2.0-only
/*
 * KernelSU: hide KernelSU/Magisk/LSPosed type names from SELinux policy reads.
 *
 * KernelSU loads its own sepolicy at boot, which introduces type names such as
 * ksu_file, and root/Xposed modules add theirs (magisk_file, xposed_data,
 * xposed_file). All of them end up in the live policydb.
 *
 * /sys/fs/selinux/policy is world readable, so any app can read the binary
 * policy and look for those names. selinux_hide only fakes the status page and
 * the AVC decisions; it never intercepts policy reads, so such checks still
 * succeed.
 *
 * This file hooks sel_policy_ops.read. For app UIDs it serves a freshly
 * generated copy of the policy in which those names are renamed to
 * same-length, OEM looking ones. Same length is required because the policydb
 * string table stores offsets into a single blob. Root and system readers are
 * left untouched, and every failure falls back to the original read.
 */

#include <linux/cred.h>
#include <linux/errno.h>
#include <linux/fs.h>
#include <linux/kernel.h>
#include <linux/mm.h>
#include <linux/mutex.h>
#include <linux/printk.h>
#include <linux/slab.h>
#include <linux/string.h>
#include <linux/types.h>
#include <linux/uaccess.h>
#include <linux/vmalloc.h>

#include "klog.h"
#include "compat/kernel_compat.h"
#include "hook/patch_memory.h"
#include "infra/symbol_resolver.h"

#define KSU_POLICY_HIDE_MIN_UID 10000

typedef int (*ksu_security_read_policy_fn)(void **data, size_t *len);
typedef ssize_t (*ksu_sel_read_policy_fn)(struct file *filp, char __user *buf, size_t count, loff_t *ppos);
typedef int (*ksu_sel_mmap_policy_fn)(struct file *filp, struct vm_area_struct *vma);

struct ksu_policy_rename {
	const char *from;
	const char *to;
	size_t len;
};

/*
 * Every replacement keeps the original length. The policydb string table is a
 * single blob addressed by offsets, so a length change would corrupt it.
 */
static const struct ksu_policy_rename ksu_policy_renames[] = {
	{ "ksu_file", "oem_file", 8 },
	{ "magisk_file", "oem_mg_file", 11 },
	{ "xposed_file", "oem_xp_file", 11 },
	{ "xposed_data", "oem_xp_data", 11 },
	{ "ksu", "oem", 3 },
};

static bool ksu_policy_hide_running;
static void *ksu_policy_hide_blob;
static size_t ksu_policy_hide_blob_len;
static DEFINE_MUTEX(ksu_policy_hide_mutex);

static ksu_security_read_policy_fn ksu_read_policy_fn;
static ksu_sel_read_policy_fn ksu_orig_sel_read_policy;
static ksu_sel_read_policy_fn *ksu_sel_read_policy_slot;
static ksu_sel_mmap_policy_fn ksu_orig_sel_mmap_policy;
static ksu_sel_mmap_policy_fn *ksu_sel_mmap_policy_slot;
static int (*ksu_remap_vmalloc_range)(struct vm_area_struct *vma, void *addr, unsigned long offset);

/*
 * Walk the NUL terminated strings of the blob and rename whole matches. Only
 * strings delimited by NUL on both sides are touched, so the binary sections
 * of the policy can never be hit by accident.
 */
/*
 * Check whether the name at @pos is a whole policydb string table entry.
 *
 * Policy version 33 (what Android 14+ uses) stores the string table as
 * [u32 len][u32 value][u32 ?][u32 ?][name bytes...], so the length prefix of
 * a name sits 16 bytes in front of it (4 bytes in some older layouts).
 * Policies older than version 33 terminate names with NUL instead.
 * Requiring the entry framing keeps bare substrings such as the "ksu" inside
 * "lcm_checksum" from being touched.
 */
static bool ksu_policy_name_at(void *blob, size_t len, size_t pos, size_t name_len)
{
	const unsigned char *p = blob;
	u32 pre;

	if (pos + name_len > len)
		return false;

	if (pos >= 16) {
		memcpy(&pre, p + pos - 16, sizeof(pre));
		if (pre == (u32)name_len)
			return true;
	}
	if (pos >= 4) {
		memcpy(&pre, p + pos - 4, sizeof(pre));
		if (pre == (u32)name_len)
			return true;
	}
	if (pos > 0 && p[pos - 1] == 0 && pos + name_len < len && p[pos + name_len] == 0)
		return true;

	return false;
}

static int ksu_policy_rename_blob(void *blob, size_t len, size_t *out_len)
{
	char *base = blob;
	size_t pos = 0;
	size_t i;
	int renamed = 0;

	if (!len || len < 32)
		return 0;

	/*
	 * Walk every entry of every table that could hold a name. We do not try
	 * to parse the policy: for each byte offset we simply ask whether a
	 * rename target starts there and whether the entry framing around it
	 * matches. Same-length replacement means no offset in the file can
	 * change, so this is safe even if we do not understand a section.
	 */
	for (pos = 0; pos + 1 < len; pos++) {
		for (i = 0; i < ARRAY_SIZE(ksu_policy_renames); i++) {
			const struct ksu_policy_rename *r = &ksu_policy_renames[i];

			if (pos + r->len > len || memcmp(base + pos, r->from, r->len))
				continue;
			if (!ksu_policy_name_at(blob, len, pos, r->len))
				continue;
			memcpy(base + pos, r->to, r->len);
			renamed++;
		}
	}

	*out_len = len;
	return renamed;
}
/* Build a sanitized copy of the live policy, or NULL on any failure. */
static void *ksu_policy_hide_build(size_t *out_len)
{
	void *blob = NULL, *mapped = NULL;
	size_t len = 0;
	int renamed;

	if (!ksu_read_policy_fn)
		return NULL;

	if (ksu_read_policy_fn(&blob, &len) || !blob || len == 0) {
		if (blob)
			kvfree(blob);
		return NULL;
	}

	renamed = ksu_policy_rename_blob(blob, len, out_len);

	/*
	 * Hand the sanitized policy to userspace through a vmalloc_user()
	 * buffer: it can be both read() and remap_vmalloc_range()d, which the
	 * mmap path needs. Cache it even when nothing matched, so a chunked
	 * reader does not make us rebuild a 2 MB policy on every read().
	 */
	mapped = vmalloc_user(len);
	if (mapped) {
		memcpy(mapped, blob, len);
		kvfree(blob);
		blob = mapped;
	}
	*out_len = len;

	pr_info("selinux_policy_hide: cached policy: %zu bytes, %d renames%s\n", len, renamed,
		mapped ? "" : " (not mappable)");
	return blob;
}

/* Shared cache accessor: both the read() and the mmap() path use it. */
static void *ksu_policy_get_blob(size_t *out_len)
{
	void *blob;

	mutex_lock(&ksu_policy_hide_mutex);
	if (!ksu_policy_hide_blob)
		ksu_policy_hide_blob = ksu_policy_hide_build(&ksu_policy_hide_blob_len);
	blob = ksu_policy_hide_blob;
	*out_len = ksu_policy_hide_blob_len;
	mutex_unlock(&ksu_policy_hide_mutex);

	return blob;
}

/*
 * The policy file also exposes mmap(). Without this hook a reader could map
 * the policy and bypass the read() sanitizing entirely, so app UIDs get our
 * sanitized (vmalloc_user) copy mapped instead.
 */
static int ksu_sel_mmap_policy(struct file *filp, struct vm_area_struct *vma)
{
	void *blob;
	size_t len;
	int ret;

	if (!ksu_policy_hide_running || ksu_get_uid_t(current_uid()) < KSU_POLICY_HIDE_MIN_UID)
		return ksu_orig_sel_mmap_policy(filp, vma);

	blob = ksu_policy_get_blob(&len);
	if (!blob || !len || vma->vm_pgoff)
		return ksu_orig_sel_mmap_policy(filp, vma);

	ret = ksu_remap_vmalloc_range(vma, blob, 0);
	if (ret)
		return ksu_orig_sel_mmap_policy(filp, vma);

	return 0;
}

static ssize_t ksu_sel_read_policy(struct file *filp, char __user *buf, size_t count, loff_t *ppos)
{
	void *blob;
	size_t len, n;

	if (!ksu_policy_hide_running || ksu_get_uid_t(current_uid()) < KSU_POLICY_HIDE_MIN_UID)
		return ksu_orig_sel_read_policy(filp, buf, count, ppos);

	blob = ksu_policy_get_blob(&len);

	if (!blob || *ppos < 0)
		return ksu_orig_sel_read_policy(filp, buf, count, ppos);

	if ((size_t)*ppos >= len)
		return 0;

	n = len - (size_t)*ppos;
	if (n > count)
		n = count;
	if (copy_to_user(buf, (char *)blob + *ppos, n))
		return -EFAULT;
	*ppos += n;

	return (ssize_t)n;
}

int ksu_selinux_policy_hide_enable(void)
{
	struct file_operations *ops;
	ksu_sel_read_policy_fn new_fn = ksu_sel_read_policy;
	int ret;

	if (ksu_policy_hide_running)
		return 0;

	if (!ksu_read_policy_fn) {
		ksu_read_policy_fn =
			(ksu_security_read_policy_fn)(unsigned long)find_kernel_symbol_exact("security_read_policy");
		if (!ksu_read_policy_fn) {
			pr_err("selinux_policy_hide: security_read_policy not found\n");
			return -ENOENT;
		}
	}

	ops = (struct file_operations *)(unsigned long)find_kernel_symbol_exact("sel_policy_ops");
	if (!ops || !ops->read) {
		pr_err("selinux_policy_hide: sel_policy_ops or its read op not found\n");
		return -ENOENT;
	}

	ksu_sel_read_policy_slot = &ops->read;
	ksu_orig_sel_read_policy = *ksu_sel_read_policy_slot;
	ret = ksu_patch_text(ksu_sel_read_policy_slot, &new_fn, sizeof(new_fn), KSU_PATCH_TEXT_FLUSH_DCACHE);
	if (ret) {
		pr_err("selinux_policy_hide: patch_text sel_read_policy failed: %d\n", ret);
		ksu_sel_read_policy_slot = NULL;
		ksu_orig_sel_read_policy = NULL;
		return ret;
	}

	/*
	 * The policy file also exposes mmap() on kernels that support policy
	 * mapping. Hook it too, otherwise a reader could map the policy and read
	 * the unmodified type names straight out of the mapping.
	 */
	if (ops->mmap) {
		ksu_remap_vmalloc_range = (int (*)(struct vm_area_struct *, void *, unsigned long))(unsigned long)
			find_kernel_symbol_exact("remap_vmalloc_range");
		if (ksu_remap_vmalloc_range) {
			ksu_sel_mmap_policy_fn new_mmap = ksu_sel_mmap_policy;

			ksu_sel_mmap_policy_slot = &ops->mmap;
			ksu_orig_sel_mmap_policy = *ksu_sel_mmap_policy_slot;
			if (ksu_patch_text(ksu_sel_mmap_policy_slot, &new_mmap, sizeof(new_mmap),
					   KSU_PATCH_TEXT_FLUSH_DCACHE)) {
				pr_warn("selinux_policy_hide: mmap hook not installed\n");
				ksu_sel_mmap_policy_slot = NULL;
				ksu_orig_sel_mmap_policy = NULL;
			}
		}
	} else {
		pr_info("selinux_policy_hide: policy has no mmap op\n");
	}

	ksu_policy_hide_running = true;
	pr_info("selinux_policy_hide: enabled\n");
	return 0;
}

void ksu_selinux_policy_hide_disable(void)
{
	if (!ksu_policy_hide_running)
		return;

	ksu_policy_hide_running = false;

	if (ksu_sel_mmap_policy_slot && ksu_orig_sel_mmap_policy) {
		ksu_sel_mmap_policy_fn orig_mmap = ksu_orig_sel_mmap_policy;

		ksu_patch_text(ksu_sel_mmap_policy_slot, &orig_mmap, sizeof(orig_mmap), KSU_PATCH_TEXT_FLUSH_DCACHE);
		ksu_sel_mmap_policy_slot = NULL;
	}

	if (ksu_sel_read_policy_slot && ksu_orig_sel_read_policy) {
		ksu_sel_read_policy_fn orig = ksu_orig_sel_read_policy;

		ksu_patch_text(ksu_sel_read_policy_slot, &orig, sizeof(orig), KSU_PATCH_TEXT_FLUSH_DCACHE);
		ksu_sel_read_policy_slot = NULL;
	}

	/*
	 * Deliberately do not free ksu_policy_hide_blob here. Another CPU can
	 * already be inside ksu_sel_read_policy() with the pointer copied out of
	 * the mutex, about to copy_to_user() from it; freeing it would be a
	 * use-after-free. The cache is a single policy blob, bounded and reused
	 * if the feature is switched back on. It is a single bounded allocation and is simply kept for the module lifetime.
	 */

	pr_info("selinux_policy_hide: disabled\n");
}
