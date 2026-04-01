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
6. computes weakest preconditions for each function;
7. asks Z3 whether the negation of each VC is satisfiable; and
8. reports success or a counterexample.

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
Instead, Anvil encodees these as the following C patterns:

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

- global `int` variables such as `int x;`
- `int` and `void` functions
- local helper function definitions before `main`
- local header imports with `#include "file.h"`
- integer literals
- variables
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

- Pointer operations are not supported by the parser today. Programs using `&`, `*`, pointer assignment, or pointer dereference are expected to fail.
- Pointer globals are unsupported.
- Instrumentation of contracted `void` calls is currently unsupported.
- Instrumented calls inside `&&`, `||`, or `while` conditions are currently unsupported.
- Verification models function calls in formulas as uninterpreted functions in Z3.
- Only local quoted includes are used for contract imports: `#include "file.h"`.

## Examples In This Repository

Useful examples live in `test/e2e_cases/`:

- `contract_import_scalar.c`
- `contract_local_scalar.c`
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
