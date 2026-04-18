# Anvil

Anvil is a small verifier for a restricted C-like language, meant to be banged on by Vulcan.

It can:

- parse and pretty-print a restricted set of C programs in the supported subset;
- instrument contracts into explicit `Assume` and `Assert` checks;
- generate verification conditions with weakest preconditions;
- ask Z3 for a counterexample to the negated VC; and
- report either `Verified.` or a concrete counterexample.

## Requirements

- `ocaml`
- `dune`
- `menhir`
- `z3`

`gcc` is also useful for the translation-based end-to-end tests, but it is not required for `--verify`.

## Building

Build the executable with:

```bash
dune build ./bin/main.exe
```

You can then use either:

```bash
./anvil
```

or:

```bash
./_build/default/bin/main.exe
```

The `./anvil` wrapper will build `./bin/main.exe` automatically unless `ANVIL_SKIP_BUILD=1` is set.

## Command Line

Pretty-print the instrumented program:

```bash
./anvil program.c
```

Verify a program with Z3:

```bash
./anvil --verify program.c
```

Read from standard input:

```bash
cat program.c | ./anvil --verify
```

## What Verification Does

When you run:

```bash
./anvil --verify program.c
```

Anvil:

1. parses the input program;
2. loads function contracts from local `#include "file.h"` headers;
3. loads the same contract syntax from implemented functions in `.c` files;
4. attaches any `@Invariant` comments to the following `while` loop;
5. instruments contracts into `Assume` and `Assert` statements;
6. lowers pointer operations and ghost-heap contract predicates into scalar ghost state when needed;
7. computes weakest preconditions for each function;
8. asks Z3 whether the negation of each VC is satisfiable; and
9. reports success or a counterexample.

If Z3 cannot find a model for the negated VC, the program is reported as verified.

If Z3 can find a model, Anvil prints the failing verification condition and the model values it found.

## Function Contracts

Anvil understands three function contract annotations:

- `@Require`
- `@Guarantee`
- `@Safety`

These can appear either:

- before a declaration in a local header included with `#include "..."`; or
- before a function definition in a `.c` file.

### Example: Contract In A Header

```c
/* @Require x >= 0
 * @Guarantee result > x
 * @Safety x <= 10
 */
int inc(int x);
```

Then use it from a program:

```c
#include "inc.h"
#include <stdlib.h>
#include <stdio.h>

int x;

int main(void) {
  x = inc(1);
  return 0;
}
```

### Example: Contract On An Implemented Function

```c
#include <stdlib.h>
#include <stdio.h>

int x;

/* @Require y >= 0
 * @Guarantee result > y
 * @Safety y >= 0
 */
int inc(int y) {
  return (y + 1);
}

int main(void) {
  x = inc(1);
  return 0;
}
```

### Contract Meaning

At a call to a contracted function, Anvil checks:

- `@Require` as a caller obligation;
- `@Guarantee` as a post-call assumption; and
- `@Safety` as a post-call assumption.

Inside a contracted function body, Anvil treats:

- `@Require` as an entry assumption;
- `@Guarantee` as an assertion at each `return`; and
- `@Safety` as a proof obligation that must hold after every command.

Use `result` inside `@Guarantee` to refer to the returned value.

`@Safety` is intended to describe a state property that is preserved throughout execution.
Operationally, Anvil assumes it after a contracted call, and proves it inside a contracted implementation.
In practice, `@Safety` should be written as a state invariant rather than as a property of `result`.

## Overloading And Type-Directed Dispatch

Anvil now supports a simple form of C++-style overload resolution for free functions and methods.

The current model is intentionally small:

- dispatch is based on the statically inferred argument types;
- overload resolution requires an exact type match on the explicit parameters;
- methods dispatch on the receiver type plus the explicit argument types; and
- overloaded names are lowered to mangled C identifiers in the pretty-printer.

For example, these overloads:

```c
int pick(int value) { return (value + 1); }
int pick(bool high) { return high ? 7 : 3; }
```

are lowered to names like:

- `pick__ol__int`
- `pick__ol__bool`

Unique functions and methods keep their existing names.

This is still static dispatch, not a full virtual-method runtime:

- no inheritance
- no vtables
- no late-bound virtual dispatch
- no implicit numeric conversions during overload selection

## Ghost Heap Interface

Memory reasoning in Anvil is contract-driven rather than automatic.
Instead of treating every pointer operation as a built-in proof obligation, Anvil exposes a small ghost-heap interface that can be used inside `@Require`, `@Guarantee`, and `@Safety`.

The recommended entry point is:

```c
int *p;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = malloc(16);
  *(p + 1) = 7;
  free(p);
  return 0;
}
```

Because `@Safety` is checked after every command inside a contracted implementation, `@Safety heap_ok()` means "no invalid memory action has happened so far on this path."
At a call to a contracted function, that same `@Safety` fact is assumed afterward, just like a guarantee.

Anvil currently uses a fixed `sizeof(int) = 4` byte model for memory.
So `malloc(n)` is interpreted in bytes, `*p` and `*p = v` require 4 readable bytes, and `p + 1` advances by 4 bytes.

When Anvil sees pointer syntax or ghost-heap predicates, it lowers memory into ghost state:

- each pointer global is represented as a `(block, offset)` pair;
- each `malloc` site gets ghost variables for allocation size and liveness;
- loads become uninterpreted `__anvil_load(block, offset)` values; and
- invalid read, write, or `free` operations flip a sticky ghost flag used by `heap_ok()`.

That ghost flag is initialized to true at function entry and is never restored after it becomes false.
This makes `heap_ok()` a convenient summary property for "memory safety has held so far."

### Built-In Ghost Predicates

Anvil currently recognizes these built-in predicate calls in contracts:

- `heap_ok()`: no earlier memory operation on the current path has been marked invalid.
- `valid_read(p, n)`: the range starting at pointer `p` with width `n` bytes lies inside a readable live block.
- `valid_write(p, n)`: currently the same check as `valid_read(p, n)`.
- `allocated(p)`: pointer `p` designates at least one readable `int` cell, currently 4 bytes.
- `live(p)`: the block named by `p` is live. Integer globals are always live.
- `can_free(p)`: `p` is null or the base address of a live allocation.
- `same_block(p, q)`: `p` and `q` refer to the same block.
- `is_null(p)`: `p` is the null pointer.

These predicates are lowered into ordinary scalar formulas before weakest-precondition generation, so they participate in verification just like any other contract formula.

## Arrays

Anvil now supports fixed-size global arrays of scalar element types:

- `int`
- `float`
- `double`
- `char`
- `bool`

The surface syntax includes:

- declarations like `int xs[4];`
- indexed reads like `xs[i]` and `p[i]`
- indexed writes like `xs[i] = e;`
- indexed addresses like `&xs[i]`

Example:

```c
int xs[4];
int *p;

/* @Require 1
 * @Guarantee 1
 * @Safety heap_ok()
 */
int main(void) {
  p = &xs[1];
  xs[0] = 3;
  xs[1] = (xs[0] + 4);
  p[1] = (xs[1] + 1);
  return 0;
}
```

Array accesses are lowered into the same ghost-heap model as pointer arithmetic, so `@Safety heap_ok()` can be used to prove array bounds safety.

Current limitations:

- arrays must be global, fixed-size declarations
- array elements must be scalar (no arrays of pointers or nested arrays yet)
- array parameters and array return types are not supported yet

## Loop Invariants

You can annotate a loop invariant with a comment immediately before a `while`:

```c
/* @Invariant x >= 0 */
while ((x > 0)) {
  x = (x - 1);
}
```

An annotated invariant is used in two checks:

- preservation: if the invariant holds before an iteration and the loop condition is true, it must still hold after the body;
- exit: if the invariant holds and the loop condition is false, the postcondition after the loop must follow.

If no `@Invariant` is supplied, Anvil currently falls back to the optimistic behavior of using the loop postcondition itself as the candidate invariant.

The `@Invariant` comment must attach directly to the following `while`. If some other token appears first, Anvil reports an error.

## Assertions And Assumptions In Source Programs

The surface language does not have dedicated `assert(...)` or `assume(...)` syntax.
Instead, Anvil encodes these as the following C patterns:

Assertion:

```c
if (!(x >= 0)) { abort(); }
```

Assumption:

```c
while (!(x >= 0)) { ; }
```

or in a `void` function:

```c
if (!(x >= 0)) { return; }
```

These are also the forms Anvil emits when it pretty-prints instrumented code.

## Source Language Subset

The accepted language is intentionally small.

Supported today:

- global scalar variables of type `int`, `float`, `double`, `char`, and `bool`
- global pointer variables to those scalar types, such as `int *p;` and `double *q;`
- function-local scalar, pointer, and fixed-size array declarations
- nested block scopes with local-variable shadowing
- scalar-valued functions over `int`, `float`, `double`, `char`, `bool`, plus `void`
- local helper function definitions before `main`
- local header imports with `#include "file.h"`
- integer, float, double, char, and bool literals
- variables
- address-of for scalar globals and local array elements such as `&x` and `&xs[0]`
- pointer dereference reads such as `*p`
- pointer dereference writes such as `*(p + 1) = 7;`
- array reads and writes such as `xs[i]` and `xs[i] = 7;`
- `malloc(n)` and `free(p)`
- function calls
- arithmetic expressions such as `(x + 1)` and `(x - 1)`
- comparisons such as `(x >= 0)` and `(x == y)`
- boolean connectives in conditions and contracts
- `if ... else ...`
- `while`
- `return`

Important syntax note:

- source arithmetic and comparison expressions should be written in the parenthesized style that Anvil prints, for example `x = (x - 1);` and `while ((x > 0))`.
- contract expressions inside comments use the contract parser, which accepts ordinary infix forms like `x >= 0`, `result > y`, and `p != 0 && x < 10`.
- contracts may also use the built-in ghost-heap predicates directly, for example `heap_ok()`, `can_free(p)`, and `same_block(p, &x)`.

## Verification Output

### Verified Program

For a valid program:

```bash
./anvil --verify test/e2e_cases/contract_local_scalar.c
```

Anvil prints:

```text
Verified.
```

### Counterexample

For:

```c
#include <stdlib.h>
#include <stdio.h>

int x;

int main(void) {
  if (!(x >= 0)) { abort(); }
  return 0;
}
```

Anvil prints:

```text
Counterexample at main: entry:
Condition:
  (x >= 0)
Counterexample:
  x = -1
```

## Translation Mode

Without `--verify`, Anvil prints the instrumented C program:

```bash
./anvil program.c > instrumented.c
```

This is useful if you want to inspect the inserted checks directly.

For example, a contracted local function call becomes a sequence like:

- `Assert(@Require)`
- call into a temporary result variable
- `Assume(@Guarantee)`
- `Assume(@Safety)`

## Current Limitations

- Pointer safety support is currently a proof-of-concept for global scalar pointers.
- Pointer parameters and pointer return values in function definitions are currently unsupported.
- Address-of is only supported for scalar globals.
- Memory safety is opt-in through contracts such as `@Safety heap_ok()`. Pointer operations alone do not add user-visible proof obligations.
- Memory contents are not modeled precisely yet: loads become uninterpreted values, while the ghost-heap predicates cover bounds, liveness, null, and invalid free conditions.
- `malloc` uses an allocation-site abstraction rather than a full heap model.
- `float` and `double` are verified with an idealized real-valued encoding rather than IEEE-754 semantics.
- Instrumentation of contracted `void` calls is currently unsupported.
- Instrumented calls inside `&&`, `||`, or `while` conditions are currently unsupported.
- Verification models function calls in formulas as uninterpreted functions in Z3.
- Only local quoted includes are used for contract imports: `#include "file.h"`.

## Examples In This Repository

Useful examples live in `test/e2e_cases/`:

- `contract_import_scalar.c`
- `contract_local_scalar.c`
- `modular_composition_scalar.c`
- `modular_composition_memory.c`
- `memory_safe_int_expression.c`
- `memory_safe_float_expression.c`
- `memory_safe_double_expression.c`
- `memory_safe_char_expression.c`
- `memory_safe_bool_expression.c`
- `memory_unsafe_int_too_small.c`
- `memory_unsafe_float_too_small.c`
- `memory_unsafe_double_too_small.c`
- `memory_unsafe_char_out_of_bounds.c`
- `memory_unsafe_bool_out_of_bounds.c`
- `memory_safe_malloc_store.c`
- `memory_unsafe_dangling_store.c`
- `scalar_loop.c`
- `pointer_address_of_global.c`

The unit and property tests live in `test/test_anvil.ml`.

## Development Checks

Run the OCaml test suite:

```bash
./_build/default/test/test_anvil.exe
```

Run the translation end-to-end cases:

```bash
ANVIL_SKIP_BUILD=1 ./test/run_e2e.sh
```
