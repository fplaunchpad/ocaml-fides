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

#pragma GCC visibility push(hidden)

/* `ocamlopt` (asmcomp/cmmgen.ml) emits calls to these around every external
   call; runtime/fides_ffi.c explains the shape. */
intnat caml_fides_enter(void *fn);
value caml_fides_promote(value v);
value caml_fides_leave(intnat d, value res);
void caml_fides_unwind(intnat d);

/* The raise path: release the frames of the calls an exception abandons. */
void caml_fides_unwind_to_handler(void *handler);

/* Is this address inside OCaml's static data (D10)? */
int caml_fides_in_static_data(uintptr_t a);

#pragma GCC visibility pop

#endif /* CAML_FIDES_FFI_H */
