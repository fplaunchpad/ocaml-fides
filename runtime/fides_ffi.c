/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*   FIDES software sanitizer: the OCaml/C boundary (Extcall promotion).  */
/*   Rules follow Resources/model.pdf; see Implementation/DECISIONS.md.   */
/*                                                                        */
/**************************************************************************/

/* Trusted runtime code, never instrumented (D30).

   The model's Extcall mints one metadata entry per OCaml block handed to C
   ("promotion", §D.5 p.31), and the entry dies when the call ends. Entries
   belong to the frame that holds them, not to the call's result (D4), so this
   file keeps a stack of *boundary frames*: one per external call, holding the
   indices that call minted.

   `ocamlopt` (asmcomp/cmmgen.ml) wraps every external call:

       d = caml_fides_enter(&fn);
       r = fn(caml_fides_promote(a1), ..., caml_fides_promote(an));
       return caml_fides_leave(d, r);

   and `caml_raise` calls caml_fides_unwind_to_handler for the calls an
   exception abandons. Ending an activation, however it ends, also releases
   the stack-object entries of its C frames that never ran their exits.

   It also keeps the GC roots that sanitized C registers (D12): `CAMLparam`,
   `CAMLlocal` and the global-root functions reach the runtime through the
   `caml_checked_*` functions below, and the collector scans them with
   caml_fides_scan_roots. */

#define CAML_INTERNALS

#include <string.h>

#include "caml/mlvalues.h"
#include "caml/domain_state.h"
#include "caml/memory.h"
#include "caml/misc.h"
#include "caml/roots.h"
#include "caml/fides_ffi.h"

/* Bounds of the sanitized C code, from the section the pass puts it in.
   Weak: a program with no sanitized C leaves them null, and then nothing is
   ever promoted. */
extern char __start_fides_c_text[] __attribute__((weak, visibility("hidden")));
extern char __stop_fides_c_text[] __attribute__((weak, visibility("hidden")));

/* OCaml's static data: the blocks ocamlopt emits into the executable
   (string literals, structured constants, closed top-level closures). The
   model has no static data and assumes every OCaml block is in the heap
   arena (§J.1 p.72); D10 accepts these segments as a second OCaml range,
   readable by C but not writable. caml_data_segments is the per-unit table
   the compiler already emits (asmcomp/cmm_helpers.ml). */
struct segment { char *begin; char *end; };
extern struct segment caml_data_segments[];

static char *static_low, *static_high;   /* fast reject bounds */
static int ranges_ready;

static void init_ranges(void)
{
  if (ranges_ready) return;
  ranges_ready = 1;
  for (int i = 0; caml_data_segments[i].begin != NULL; i++) {
    if (static_low == NULL || caml_data_segments[i].begin < static_low)
      static_low = caml_data_segments[i].begin;
    if (caml_data_segments[i].end > static_high)
      static_high = caml_data_segments[i].end;
  }
}

/* Exact membership: C globals may sit between two OCaml units' segments, so
   the fast reject above is not enough on its own. */
int caml_fides_in_static_data(uintptr_t a)
{
  char *p = (char *)a;
  init_ranges();
  if (p < static_low || p >= static_high) return 0;
  for (int i = 0; caml_data_segments[i].begin != NULL; i++)
    if (p >= caml_data_segments[i].begin && p < caml_data_segments[i].end)
      return 1;
  return 0;
}

static int in_sanitized_c(void *fn)
{
  char *p = (char *)fn;
  return __start_fides_c_text != NULL
         && p >= __start_fides_c_text && p < __stop_fides_c_text;
}

/* ---------------------------------------------------------------------- */
/* Boundary frames                                                        */

#define FIDES_MAX_DEPTH    512
#define FIDES_FRAME_INLINE 8

/* One promoted argument: the entry, and the OCaml value it was minted for.
   The value is a GC root (D12): when the collector moves the block, the
   entry moves with it. */
struct promoted {
  value v;
  uint16_t idx;
};

struct bframe {
  struct promoted inl[FIDES_FRAME_INLINE];
  struct promoted *more;    /* overflow, or NULL */
  int n, cap;
  int promoting;            /* the target is sanitized C */
  void *handler;            /* Caml_state->exn_handler at entry */
  intnat root_base;         /* registered local roots at entry */
  size_t stack_base;        /* stack-object log height at entry */
};

static struct bframe frames[FIDES_MAX_DEPTH];
static intnat depth;

static struct promoted *promoted_of(struct bframe *f)
{
  return f->more != NULL ? f->more : f->inl;
}

static void record(struct bframe *f, uint16_t index, value v)
{
  if (f->n == f->cap) {
    int cap = f->cap * 2;
    struct promoted *more =
      caml_stat_alloc_noexc(cap * sizeof(struct promoted));
    if (more == NULL)
      caml_fatal_error("FIDES: out of memory recording a boundary frame");
    memcpy(more, promoted_of(f), f->n * sizeof(struct promoted));
    caml_stat_free(f->more);
    f->more = more;
    f->cap = cap;
  }
  promoted_of(f)[f->n].idx = index;
  promoted_of(f)[f->n].v = v;
  f->n++;
}

/* ---------------------------------------------------------------------- */
/* Registered roots (D12)                                                 */

/* A registered slot range: [n] values starting at [slot], kept as the
   tagged address C passed, so that the collector's store into it is
   checked against the slot's own entry every time (a slot whose frame or
   block has died traps instead of being written). */
struct root {
  uintptr_t slot;
  intnat n;
};

struct roots {
  struct root *v;
  intnat n, cap;
};

/* Local roots (CAMLparam/CAMLlocal) form a stack; a root frame is a mark,
   the stack height when it was opened. Global roots are an unordered set. */
static struct roots locals, globals;

static void push_root(struct roots *r, uintptr_t slot, intnat n)
{
  if (r->n == r->cap) {
    intnat cap = r->cap == 0 ? 64 : r->cap * 2;
    struct root *v = caml_stat_resize_noexc(r->v, cap * sizeof(struct root));
    if (v == NULL)
      caml_fatal_error("FIDES: out of memory registering a GC root");
    r->v = v;
    r->cap = cap;
  }
  r->v[r->n].slot = slot;
  r->v[r->n].n = n;
  r->n++;
}

/* Registering a slot is a promise that the collector may write it, so the
   slot must be memory C itself may write (D12): the access check and the
   write restriction, on the tagged address C passed. */
static void check_slot(uintptr_t slot, intnat n, const char *action)
{
  uintptr_t a;
  int cause;
  if (n < 0)
    caml_fides_trap(FIDES_ACCESS_BOUNDS, action, slot, 0, NULL);
  cause = caml_fides_store_cause(slot, (size_t)n * sizeof(value), &a);
  if (cause >= 0)
    caml_fides_trap((enum fides_cause)cause, action, slot,
                    (size_t)n * sizeof(value), NULL);
}

/* The lowest mark the current C activation may restore: the roots below it
   belong to an activation suspended in a callback. */
static intnat root_floor(void)
{
  return depth > 0 ? frames[depth - 1].root_base : 0;
}

CAMLexport intnat caml_checked_roots_mark(void)
{
  return locals.n;
}

CAMLexport void caml_checked_roots_register(value *slots, intnat n)
{
  check_slot((uintptr_t)slots, n, "register a local GC root");
  push_root(&locals, (uintptr_t)slots, n);
}

/* CAMLdrop: release every root registered since [mark]. Releasing a frame
   that is not this activation's, or one already released, traps. */
CAMLexport void caml_checked_roots_restore(intnat mark)
{
  if (mark < root_floor() || mark > locals.n)
    caml_fides_trap(FIDES_ROOT_FRAME_UNBALANCED,
                    "release a root frame that is not the caller's",
                    0, 0, NULL);
  locals.n = mark;
}

/* Global roots. The generational and plain variants differ only in how the
   stock collector scans them; these are all scanned at every collection. */

static intnat find_global(uintptr_t addr)
{
  for (intnat i = globals.n - 1; i >= 0; i--)
    if (__fides_decode(globals.v[i].slot) == addr) return i;
  return -1;
}

/* One record per address, as in the stock registry, where registering an
   address that is already there only updates it (skiplist.c:138): one
   removal then unregisters it however often it was registered. The record
   keeps the latest tagged address, in case the memory was freed and
   reallocated in between. */
CAMLexport void caml_checked_register_global_root(value *r)
{
  intnat i;
  check_slot((uintptr_t)r, 1, "register a global GC root");
  i = find_global(__fides_decode((uintptr_t)r));
  if (i >= 0) globals.v[i].slot = (uintptr_t)r;
  else push_root(&globals, (uintptr_t)r, 1);
}

CAMLexport void caml_checked_remove_global_root(value *r)
{
  intnat i = find_global(__fides_decode((uintptr_t)r));
  if (i < 0) return;                  /* as the stock function: no-op */
  globals.v[i] = globals.v[--globals.n];
}

CAMLexport void caml_checked_register_generational_global_root(value *r)
{
  caml_checked_register_global_root(r);
}

CAMLexport void caml_checked_remove_generational_global_root(value *r)
{
  caml_checked_remove_global_root(r);
}

CAMLexport void caml_checked_modify_generational_global_root(value *r,
                                                             value newval)
{
  uintptr_t a;
  int cause = caml_fides_store_cause((uintptr_t)r, sizeof(value), &a);
  if (cause >= 0)
    caml_fides_trap((enum fides_cause)cause, "modify a global GC root",
                    (uintptr_t)r, sizeof(value), NULL);
  /* The root keeps the bare value (D15, the Lean's RootUpdateContract): a
     tagged word would die with the activation that holds its entry, and the
     next collection would trap on it. */
  *(value *)a = caml_fides_demote(newval, "store a value in a global GC root");
}

/* ---------------------------------------------------------------------- */
/* Scanning (D12, D54)                                                    */

/* Several roots can carry the same entry: the boundary frame's promoted
   value, and C slots holding copies of the argument. The first one the scan
   reaches moves the entry and draws its fresh cookie; the others still
   carry the old cookie, so the scan remembers, per entry, what it changed
   in the current pass. */
static uint32_t scan_pass;
static uint32_t moved_pass[FIDES_TABLE_SIZE];
static uint8_t moved_old_cookie[FIDES_TABLE_SIZE];
static uintptr_t moved_old_base[FIDES_TABLE_SIZE];

/* Pass the block [v] (a raw address) to the collector's action and, if the
   collector moved it, move entry [i] too. Returns the block's address
   after the action. */
static value scan_block(scanning_action f, void *fdata, uint32_t i, value v)
{
  value nv = v;
  f(fdata, v, &nv);
  if (nv != v) {
    const struct fides_entry *e = caml_fides_entry(i);
    uintptr_t old_base = e->base;
    uint8_t old_cookie = e->cookie;
    caml_fides_relocate(i, (uintptr_t)(old_base + (nv - v)));
    moved_pass[i] = scan_pass;
    moved_old_cookie[i] = old_cookie;
    moved_old_base[i] = old_base;
  }
  return nv;
}

/* Where in its block the promoted pointer of each OCaml entry points: 0 for
   a block, the infix offset for a function inside a closure (D4 mints over
   the whole closure). Set at promotion; the scan never reads moved memory
   to recover it. */
static uintptr_t promoted_offset[FIDES_TABLE_SIZE];

/* Does a root word at offset [off] into entry [e] name the value the entry
   was minted for? The model's callbackOk requires the block base exactly
   (Step/FFI.lean:229); the infix case is ours, since promotion hands C the
   infix address. Any other offset is an interior pointer the collector
   cannot follow. */
static int names_block(uint32_t i, const struct fides_entry *e, uintptr_t off)
{
  return (e->kind == FIDES_KIND_OCAML || e->kind == FIDES_KIND_OCAML_STATIC)
         && off == promoted_offset[i];
}

/* Is [w] a value sanitized C may hand to the runtime? Immediates and bare
   words pass (bare blocks are accepted until Stage 5). A tagged word must name
   a live entry (accessBounds), carry its cookie (accessCookie), and name the
   value the entry was minted for: an OCaml block, at its promoted offset
   (callbackNotOCamlHeap, the Lean's callbackOk). Returns -1 or the cause; on
   success [*raw] is the bare value. */
int caml_fides_value_cause(value w, value *raw)
{
  uint32_t i = Fides_index((uintptr_t)w);
  *raw = w;
  if (w == 0 || Is_long(w) || i == 0) return -1;
  const struct fides_entry *e = caml_fides_entry(i);
  if (e->cookie == 0) return FIDES_ACCESS_BOUNDS;
  if (e->cookie != Fides_cookie((uintptr_t)w)) return FIDES_ACCESS_COOKIE;
  uintptr_t v = __fides_decode((uintptr_t)w);
  if (v < e->base || !names_block(i, e, v - e->base))
    return FIDES_CALLBACK_NOT_OCAML_HEAP;
  *raw = (value)v;
  return -1;
}

value caml_fides_demote(value w, const char *action)
{
  value raw;
  int cause = caml_fides_value_cause(w, &raw);
  if (cause >= 0)
    caml_fides_trap((enum fides_cause)cause, action, (uintptr_t)w, 0, NULL);
  return raw;
}

/* One registered slot. */
static void scan_slot(scanning_action f, void *fdata, uintptr_t slot)
{
  uintptr_t a, w;
  value v;
  int cause = caml_fides_store_cause(slot, sizeof(value), &a);
  if (cause >= 0)
    caml_fides_trap((enum fides_cause)cause,
                    "collector update of a registered GC root", slot,
                    sizeof(value), NULL);
  w = *(uintptr_t *)a;
  if (w == 0 || Is_long((value)w)) return;
  uint32_t i = Fides_index(w);
  if (i == 0) {                       /* a bare block: the stock root */
    f(fdata, (value)w, (value *)a);
    return;
  }
  const struct fides_entry *e = caml_fides_entry(i);
  if (moved_pass[i] == scan_pass && e->cookie != 0
      && Fides_cookie(w) == moved_old_cookie[i]) {
    /* An earlier root of this pass already moved the entry: this word still
       describes the old location. */
    uintptr_t old = (moved_old_base[i] & ~FIDES_ADDR_MASK) | Fides_low(w);
    uintptr_t off = old - moved_old_base[i];
    if (old < moved_old_base[i] || !names_block(i, e, off))
      caml_fides_trap(FIDES_CALLBACK_NOT_OCAML_HEAP,
                      "collector scan of a GC root", w, 0, NULL);
    *(uintptr_t *)a = Fides_pack(i, e->cookie, e->base + off);
    return;
  }
  /* A root word the collector cannot use (D12). */
  cause = caml_fides_value_cause((value)w, &v);
  if (cause >= 0)
    caml_fides_trap((enum fides_cause)cause, "collector scan of a GC root", w,
                    0, NULL);
  value nv = scan_block(f, fdata, i, v);
  if (nv != v)
    *(uintptr_t *)a = Fides_pack(i, e->cookie, (uintptr_t)nv);
}

static void scan_roots(scanning_action f, void *fdata, struct roots *r)
{
  for (intnat k = 0; k < r->n; k++)
    for (intnat j = 0; j < r->v[k].n; j++)
      scan_slot(f, fdata, r->v[k].slot + j * sizeof(value));
}

/* Called by the collector wherever it scans the domain's local roots
   (roots.c caml_do_roots, minor_gc.c), so on every minor collection, at the
   start of each major marking cycle, and when compaction updates roots. */
void caml_fides_scan_roots(scanning_action f, scanning_action_flags flags,
                           void *fdata)
{
  (void)flags;
  if (++scan_pass == 0) {             /* wrapped: forget every old pass */
    memset(moved_pass, 0, sizeof moved_pass);
    scan_pass = 1;
  }
  /* Promoted arguments first, so that their entries follow their blocks
     even when the stub roots nothing. */
  for (intnat d = 0; d < depth; d++) {
    struct bframe *fr = &frames[d];
    struct promoted *p = promoted_of(fr);
    for (int k = 0; k < fr->n; k++)
      p[k].v = scan_block(f, fdata, p[k].idx, p[k].v);
  }
  scan_roots(f, fdata, &locals);
  scan_roots(f, fdata, &globals);
}

/* ---------------------------------------------------------------------- */
/* Entering and leaving                                                   */

/* Release everything the frame minted (D4: the entries die with the frame). */
static void drop(struct bframe *f)
{
  struct promoted *p = promoted_of(f);
  for (int i = 0; i < f->n; i++) caml_fides_release_index(p[i].idx);
  caml_stat_free(f->more);
  f->more = NULL;
  f->n = 0;
  f->cap = FIDES_FRAME_INLINE;
}

/* Open a boundary frame for a call to [fn]; returns the depth to restore. */
intnat caml_fides_enter(void *fn)
{
  struct bframe *f;
  if (depth >= FIDES_MAX_DEPTH)
    caml_fatal_error("FIDES: FFI nesting deeper than %d", FIDES_MAX_DEPTH);
  f = &frames[depth];
  f->n = 0;
  f->more = NULL;
  f->cap = FIDES_FRAME_INLINE;
  f->promoting = in_sanitized_c(fn);
  f->handler = Caml_state->exn_handler;
  f->root_base = locals.n;
  f->stack_base = caml_fides_stack_height();
  caml_fides_stack_set_floor(f->stack_base);
  return depth++;
}

/* Promotion (§D.5): give C a validating pointer to an OCaml block. Integers
   pass through — the printed extcallOk would refuse them, which is the
   model's one-pointer-argument simplification (DECISIONS.md section 3). */
value caml_fides_promote(value v)
{
  struct bframe *f;
  uintptr_t base, w;
  mlsize_t size;

  if (depth == 0) return v;
  f = &frames[depth - 1];
  if (!f->promoting || !Is_block(v)) return v;

  /* An infix pointer names a function inside a closure block: mint over the
     whole block, and hand C a pointer to the infix address inside it. */
  base = (uintptr_t)v;
  if (Tag_val(v) == Infix_tag) base -= Infix_offset_val(v);
  size = Wosize_val((value)base) * sizeof(value);

  w = caml_fides_mint(base, size,
                      caml_fides_in_static_data(base) ? FIDES_KIND_OCAML_STATIC
                                                      : FIDES_KIND_OCAML);
  record(f, (uint16_t)Fides_index(w), v);
  promoted_offset[Fides_index(w)] = (uintptr_t)v - base;
  return (value)Fides_pack(Fides_index(w), Fides_cookie(w), (uintptr_t)v);
}

/* End the activations above [d]: their promoted entries, and the stack
   objects of any of their C frames that did not run their exits. */
static void unwind_to(intnat d)
{
  if (depth <= d) return;
  caml_fides_stack_unwind(frames[d].stack_base);
  while (depth > d) drop(&frames[--depth]);
  caml_fides_stack_set_floor(d > 0 ? frames[d - 1].stack_base : 0);
}

/* A C activation must release its root frames before it returns (D12):
   otherwise the runtime would keep slots of a frame that no longer exists.
   Stock OCaml leaves this undefined; it traps here. */
static void check_balanced(intnat d)
{
  if (locals.n != frames[d].root_base)
    caml_fides_trap(FIDES_ROOT_FRAME_UNBALANCED,
                    "return to OCaml with GC roots still registered",
                    0, 0, NULL);
}

/* Close the boundary frames down to [d] and hand [res] back to OCaml.
   A tagged result must pass the Lean's callbackOk (Step/FFI.lean:229): its
   entry names an OCaml block and its address is that block (or, for a
   closure, the promoted infix address). Every failure, including a dead
   entry or a wrong cookie, traps callbackNotOCamlHeap, the rule's one
   cause. The result is then demoted (its tag stripped). A bare block still
   passes until Stage 5 (DECISIONS.md D13). Checked before the frames are
   released, while the result's entry is still live. */
value caml_fides_leave(intnat d, value res)
{
  value out;
  check_balanced(d);
  if (caml_fides_value_cause(res, &out) >= 0)
    caml_fides_trap(FIDES_CALLBACK_NOT_OCAML_HEAP, "return a value to OCaml",
                    (uintptr_t)res, 0, NULL);
  unwind_to(d);
  return out;
}

/* Same, for a call whose result is not an OCaml value. */
void caml_fides_unwind(intnat d)
{
  check_balanced(d);
  unwind_to(d);
}

/* The raise path. An exception abandons every call entered since the handler
   that is about to receive it was installed: those frames recorded that
   handler, or a deeper one. Trap pointers live on the fiber stack, which
   grows down, so "deeper" is a lower address. The abandoned activations'
   root frames go with them, as caml_raise does for the stock local roots. */
void caml_fides_unwind_to_handler(void *handler)
{
  intnat d = depth;
  while (d > 0 && (char *)frames[d - 1].handler <= (char *)handler) d--;
  if (d == depth) return;
  locals.n = frames[d].root_base;
  unwind_to(d);
}
