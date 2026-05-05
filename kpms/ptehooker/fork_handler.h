/* SPDX-License-Identifier: GPL-2.0 */
/*
 * fork_handler.h - KPM v3 Fork Handler for cold-start hooking
 *
 * Hooks kernel_clone (or _do_fork) to intercept Zygote forks.
 * On each fork: installs ghost pages + shellcode with per-sandbox
 * device identity BEFORE the child executes its first instruction.
 *
 * Combined with proc-patch trampolines inherited via CoW from Zygote,
 * this achieves true T=0 cold-start hooking with zero race conditions.
 */

#ifndef _FORK_HANDLER_H
#define _FORK_HANDLER_H

#include <ktypes.h>

#define FORK_MAX_SLOTS           8   /* keep BSS small for KPM loader */
#define FORK_MAX_WATCHED_PIDS    4
#define FORK_QUEUE_MAX           8
#define FORK_MAX_TARGETS         4

#define FORK_IDENTITY_MODEL_LEN  32
#define FORK_IDENTITY_BRAND_LEN  16
#define FORK_IDENTITY_AID_LEN    17  /* 16 hex + NUL */
#define FORK_IDENTITY_IMEI_LEN   16  /* 15 digits + NUL */
#define FORK_TEMPLATE_MAX     4096   /* max shellcode template bytes (1 page) */
#define FORK_SLOT_DATA_MAX     128   /* per-slot pre-encoded shellcode identity blob */

/* Per-sandbox device identity */
struct sandbox_identity {
    char model[FORK_IDENTITY_MODEL_LEN];
    char brand[FORK_IDENTITY_BRAND_LEN];
    char android_id[FORK_IDENTITY_AID_LEN];
    char imei[FORK_IDENTITY_IMEI_LEN];
    char fingerprint[128];
    int  configured;  /* 1 if this slot has valid identity data */
};

/* Per-child tracking entry */
struct fork_child_slot {
    int           active;
    int           child_pid;
    unsigned long phys_page;     /* physical page backing the ghost */
    unsigned long ghost_kaddr;   /* kernel linear VA for the ghost page */
    int           identity_idx;  /* which sandbox_identity was used */
};

/* Pending queue: Python enqueues slot IDs before launching apps */
struct fork_queue {
    int  slots[FORK_QUEUE_MAX];
    int  head;
    int  tail;
    int  count;
};

/* Main fork handler configuration */
struct fork_handler_state {
    int active;           /* fork hook armed? */
    int hook_installed;   /* kernel_clone hook_wrap installed? */
    int exit_hook_installed; /* do_exit hook installed? */

    /* Parent PIDs to watch (Zygote / Zygote64) */
    int watched_pids[FORK_MAX_WATCHED_PIDS];
    int num_watched;

    /* Ghost page parameters (same VA for all children) */
    unsigned long ghost_va;        /* target VA in child address space */
    int           ghost_order;     /* page alloc order (0=4K, 1=8K, 2=16K) */
    unsigned long ghost_size;      /* total bytes */
    uint64_t      pte_template;    /* PTE bits (from Zygote's exec page) */

    /* Shellcode template */
    uint8_t       code_template[FORK_TEMPLATE_MAX];
    int           code_len;
    int           identity_offset; /* byte offset in template where identity data starts */

    /* Shared passthrough page: one physical page mapped into all un-queued
     * children.  Contains the template with zeroed identity data, so the
     * shellcode sees fake_pattern[0]==0 and skips scanning (pure passthrough).
     * No per-child allocation or tracking needed. */
    unsigned long passthrough_kpage;    /* kernel VA from __get_free_pages */
    unsigned long passthrough_pa;       /* physical address */

    /* ART heap Build.* patching config */
    struct {
        unsigned long model_addr;       /* VA of Build.MODEL String value in Zygote heap */
        unsigned long brand_addr;       /* VA of Build.BRAND String value */
        unsigned long fingerprint_addr; /* VA of Build.FINGERPRINT String value */
        int           string_header_size; /* ART String header bytes before char data */
        int           configured;
    } art_heap;

    /* Per-sandbox identity pool (ASCII, for ART heap patching) */
    struct sandbox_identity identities[FORK_MAX_SLOTS];

    /* Per-slot pre-encoded shellcode identity data (UTF-16LE + UTF-8).
     * Stamped into the template at identity_offset on each fork.
     * Format is defined by the Python deployer to match shellcode layout. */
    uint8_t  slot_data[FORK_MAX_SLOTS][FORK_SLOT_DATA_MAX];
    int      slot_data_len[FORK_MAX_SLOTS];

    /* Pending launch queue */
    struct fork_queue queue;

    /* Active children tracking */
    struct fork_child_slot children[FORK_MAX_SLOTS];
    int num_active_children;

    /* Stats */
    unsigned long forks_intercepted;
    unsigned long forks_skipped;   /* queue empty → pass-through */
    unsigned long children_reaped; /* freed on exit */
};

/* ---------- Property CoW Isolation ---------- */

#define PROP_MAX_CTX        12   /* max property contexts to isolate */
#define PROP_MAX_PAGES_CTX   8   /* max pages per context */
#define PROP_MAX_PAGES      32   /* max total pages per slot (across all contexts) */

struct prop_ctx_info {
    unsigned long va_start;
    int page_indices[PROP_MAX_PAGES_CTX];
    int num_pages;
    int template_base;
};

struct prop_isolation_state {
    struct prop_ctx_info contexts[PROP_MAX_CTX];
    int ctx_count;
    int total_pages;

    /* Template storage: kernel linear addresses of pre-built page content.
     * templates[slot][idx] allocated via __get_free_pages(GFP_KERNEL, 0).
     * Used as source data for access_process_vm writes. */
    unsigned long templates[FORK_MAX_SLOTS][PROP_MAX_PAGES];

    int      ready;

    /* Stats */
    unsigned long installs;
};

/* Queue helpers (inline for kernel context) */
static inline int fork_queue_push(struct fork_queue *q, int slot_id)
{
    if (q->count >= FORK_QUEUE_MAX) return -1;
    q->slots[q->tail] = slot_id;
    q->tail = (q->tail + 1) % FORK_QUEUE_MAX;
    q->count++;
    return 0;
}

static inline int fork_queue_pop(struct fork_queue *q)
{
    int val;
    if (q->count <= 0) return -1;
    val = q->slots[q->head];
    q->head = (q->head + 1) % FORK_QUEUE_MAX;
    q->count--;
    return val;
}

static inline int fork_queue_empty(struct fork_queue *q)
{
    return q->count <= 0;
}

#endif /* _FORK_HANDLER_H */
