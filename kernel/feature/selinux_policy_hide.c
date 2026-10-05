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

/*
 * Walk the NUL terminated strings of the blob and rename whole matches. Only
 * strings delimited by NUL on both sides are touched, so the binary sections
 * of the policy can never be hit by accident.
 */
static int ksu_policy_rename_blob(void *blob, size_t len)
{
	char *base = blob;
	size_t pos = 0;
	int renamed = 0;

	while (pos < len) {
		char *s = base + pos;
		size_t slen = strnlen(s, len - pos);
		size_t i;

		if (slen >= len - pos)
			break;

		for (i = 0; i < ARRAY_SIZE(ksu_policy_renames); i++) {
			const struct ksu_policy_rename *r = &ksu_policy_renames[i];

			if (slen != r->len || memcmp(s, r->from, r->len))
				continue;
			memcpy(s, r->to, r->len);
			renamed++;
			break;
		}
		pos += slen + 1;
	}

	return renamed;
}

/* Build a sanitized copy of the live policy, or NULL on any failure. */
static void *ksu_policy_hide_build(size_t *out_len)
{
	void *blob = NULL;
	size_t len = 0;
	int renamed;

	if (!ksu_read_policy_fn)
		return NULL;

	if (ksu_read_policy_fn(&blob, &len) || !blob || len == 0) {
		if (blob)
			kvfree(blob);
		return NULL;
	}

	renamed = ksu_policy_rename_blob(blob, len);
	if (renamed <= 0) {
		/* Nothing to hide, or an unexpected blob: keep the original path. */
		kvfree(blob);
		return NULL;
	}

	pr_info("selinux_policy_hide: built sanitized policy: %zu bytes, %d renames\n", len, renamed);
	*out_len = len;
	return blob;
}

static ssize_t ksu_sel_read_policy(struct file *filp, char __user *buf, size_t count, loff_t *ppos)
{
	void *blob;
	size_t len, n;

	if (!ksu_policy_hide_running || ksu_get_uid_t(current_uid()) < KSU_POLICY_HIDE_MIN_UID)
		return ksu_orig_sel_read_policy(filp, buf, count, ppos);

	mutex_lock(&ksu_policy_hide_mutex);
	if (!ksu_policy_hide_blob)
		ksu_policy_hide_blob = ksu_policy_hide_build(&ksu_policy_hide_blob_len);
	blob = ksu_policy_hide_blob;
	len = ksu_policy_hide_blob_len;
	mutex_unlock(&ksu_policy_hide_mutex);

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

	ksu_policy_hide_running = true;
	pr_info("selinux_policy_hide: enabled\n");
	return 0;
}

void ksu_selinux_policy_hide_disable(void)
{
	if (!ksu_policy_hide_running)
		return;

	ksu_policy_hide_running = false;

	if (ksu_sel_read_policy_slot && ksu_orig_sel_read_policy) {
		ksu_sel_read_policy_fn orig = ksu_orig_sel_read_policy;

		ksu_patch_text(ksu_sel_read_policy_slot, &orig, sizeof(orig), KSU_PATCH_TEXT_FLUSH_DCACHE);
		ksu_sel_read_policy_slot = NULL;
	}

	mutex_lock(&ksu_policy_hide_mutex);
	if (ksu_policy_hide_blob) {
		kvfree(ksu_policy_hide_blob);
		ksu_policy_hide_blob = NULL;
		ksu_policy_hide_blob_len = 0;
	}
	mutex_unlock(&ksu_policy_hide_mutex);

	pr_info("selinux_policy_hide: disabled\n");
}
