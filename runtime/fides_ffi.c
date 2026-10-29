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
   exception abandons. */

#define CAML_INTERNALS

#include <string.h>

#include "caml/mlvalues.h"
#include "caml/domain_state.h"
#include "caml/memory.h"
#include "caml/misc.h"
#include "caml/fides_ffi.h"

/* Bounds of the sanitized C code, from the section the pass puts it in.
   Weak: a program with no sanitized C leaves them null, and then nothing is
   ever promoted. */
extern char __start_fides_c_text[] __attribute__((weak));
extern char __stop_fides_c_text[] __attribute__((weak));

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

struct bframe {
  uint16_t idx[FIDES_FRAME_INLINE];
  uint16_t *more;           /* overflow, or NULL */
  int n, cap;
  int promoting;            /* the target is sanitized C */
  void *handler;            /* Caml_state->exn_handler at entry */
};

static struct bframe frames[FIDES_MAX_DEPTH];
static intnat depth;

static void record(struct bframe *f, uint16_t index)
{
  if (f->n == f->cap) {
    int cap = f->cap * 2;
    uint16_t *more = caml_stat_alloc_noexc(cap * sizeof(uint16_t));
    if (more == NULL)
      caml_fatal_error("FIDES: out of memory recording a boundary frame");
    memcpy(more, f->more != NULL ? (void *)f->more : (void *)f->idx,
           f->n * sizeof(uint16_t));
    caml_stat_free(f->more);
    f->more = more;
    f->cap = cap;
  }
  (f->more != NULL ? f->more : f->idx)[f->n++] = index;
}

/* Release everything the frame minted (D4: the entries die with the frame). */
static void drop(struct bframe *f)
{
  uint16_t *v = f->more != NULL ? f->more : f->idx;
  for (int i = 0; i < f->n; i++) caml_fides_release_index(v[i]);
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
  record(f, (uint16_t)Fides_index(w));
  return (value)Fides_pack(Fides_index(w), Fides_cookie(w), (uintptr_t)v);
}

static void unwind_to(intnat d)
{
  while (depth > d) drop(&frames[--depth]);
}

/* Close the boundary frames down to [d] and hand [res] back to OCaml.
   A tagged result is demoted (its tag stripped); the full callbackOk check
   is Stage 4, so a bare block still passes. */
value caml_fides_leave(intnat d, value res)
{
  value out = res;
  if (Is_block(res) && Fides_index((uintptr_t)res) != 0) {
    if (!caml_fides_valid((uintptr_t)res))
      caml_fides_trap(FIDES_CALLBACK_NOT_OCAML_HEAP, "return a value to OCaml",
                      (uintptr_t)res, 0, NULL);
    out = (value)__fides_decode((uintptr_t)res);
  }
  unwind_to(d);
  return out;
}

/* Same, for a call whose result is not an OCaml value. */
void caml_fides_unwind(intnat d)
{
  unwind_to(d);
}

/* The raise path. An exception abandons every call entered since the handler
   that is about to receive it was installed: those frames recorded that
   handler, or a deeper one. Trap pointers live on the fiber stack, which
   grows down, so "deeper" is a lower address. */
void caml_fides_unwind_to_handler(void *handler)
{
  while (depth > 0 && (char *)frames[depth - 1].handler <= (char *)handler)
    drop(&frames[--depth]);
}
