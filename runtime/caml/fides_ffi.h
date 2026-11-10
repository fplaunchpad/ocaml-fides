/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*   FIDES software sanitizer: the OCaml/C boundary (Extcall promotion).  */
/*                                                                        */
/**************************************************************************/

/* Separate from caml/fides.h because these take OCaml types, and that header
   must build on its own (the runtime library's unit tests compile it without
   the OCaml headers). */

#ifndef CAML_FIDES_FFI_H
#define CAML_FIDES_FFI_H

#include "caml/fides.h"
#include "caml/mlvalues.h"
#include "caml/roots.h"

#pragma GCC visibility push(hidden)

/* `ocamlopt` (asmcomp/cmmgen.ml) emits calls to these around every external
   call; runtime/fides_ffi.c explains the shape. */
intnat caml_fides_enter(void *fn);
value caml_fides_promote(value v);
value caml_fides_leave(intnat d, value res);
void caml_fides_unwind(intnat d);

/* The raise path: release the frames of the calls an exception abandons. */
void caml_fides_unwind_to_handler(void *handler);

/* The collector's scan of the roots the sanitizer keeps (D12): promoted
   arguments and the slots sanitized C registered. Moves entries with their
   blocks and rewrites the registered slots. */
void caml_fides_scan_roots(scanning_action f, scanning_action_flags flags,
                           void *fdata);

/* Is [w] a value sanitized C may hand to the runtime (immediate, bare, or a
   tagged word naming its promoted block)? -1 or the trap cause; [*raw] is the
   bare value. */
int caml_fides_value_cause(value w, value *raw);

/* The same check for a value a trusted wrapper is handed: traps with
   [action], or returns the bare value. */
value caml_fides_demote(value w, const char *action);

/* The wrappers of the C API (runtime/fides_api.c, caml/fides_api.def). */
struct caml_fides_api_entry {
  void *real;
  void *wrapper;
  const char *name;
};
extern const struct caml_fides_api_entry caml_fides_api_table[];
extern const size_t caml_fides_api_count;

/* Is this address inside OCaml's static data (D10)? */
int caml_fides_in_static_data(uintptr_t a);

#pragma GCC visibility pop

#endif /* CAML_FIDES_FFI_H */
