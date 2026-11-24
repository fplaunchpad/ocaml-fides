/**************************************************************************/
/*                                                                        */
/*                                 OCaml                                  */
/*                                                                        */
/*   FIDES software sanitizer: the runtime functions sanitized C may not  */
/*   call (Stage 4). See Implementation/DECISIONS.md D18.                 */
/*                                                                        */
/**************************************************************************/

/* The addresses of the functions in caml/fides_api_deny.def, for the
   run-time check at indirect calls (__fides_wrapper_for, fides_api.c).

   This file includes no OCaml header, so that each name can be declared
   here only as an address. The references are weak: they do not pull
   runtime code into a program that does not otherwise use it, and a
   function that is not linked in reads as null (and cannot be called). */

#include <stddef.h>

#define FIDES_DENY(name) extern char name[] __attribute__((weak));
#include "caml/fides_api_deny.def"

struct caml_fides_api_denied { const void *fn; const char *name; };

#define FIDES_DENY(name) { name, #name },
__attribute__((visibility("hidden")))
const struct caml_fides_api_denied caml_fides_api_deny_table[] = {
#include "caml/fides_api_deny.def"
};

__attribute__((visibility("hidden")))
const size_t caml_fides_api_deny_count =
  sizeof caml_fides_api_deny_table / sizeof caml_fides_api_deny_table[0];
