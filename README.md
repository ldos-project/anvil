# Anvil

Anvil is a small verifier for a restricted C / C++-flavored language, meant to be banged on by Vulcan.

It can:

- parse, resolve, and pretty-print a restricted core language plus a small C++-style frontend fragment;
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

Show help:

```bash
./anvil -h
```

Enable the strict memory-free surface fragment:

```bash
./anvil --strict program.c
```

Pretty-print the instrumented program:

```bash
./anvil program.c
```

Verify a program with Z3:

```bash
./anvil --verify program.c
```

Whole-program C++-flavored example with a highlighted scoring hook:

```bash
./anvil --verify examples/vulcan_listener_scoring.cpp
```

Multiple-contract guarded-case example:

```bash
./anvil --verify examples/multi_contract_sign.c
```

Buggy guarded-case example that should produce a counterexample:

```bash
./anvil --verify examples/multi_contract_sign_bad.c
```

Ghost-binding contract example:

```bash
./anvil --verify examples/ghost_contract_sign.c
```

Buggy ghost-binding example that should produce a counterexample:

```bash
./anvil --verify examples/ghost_contract_sign_bad.c
```

Comparator total-order proof example:

```bash
./anvil --verify examples/comparator_total_order.c
```

Quantified contract example:

```bash
./anvil --verify examples/quantified_contract_bump.c
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
2. resolves namespaces, classes, methods, references, and overloads into the core representation;
3. loads function contracts from local `#include "file.h"` headers;
4. loads the same contract syntax from implemented functions in the input source file, whether it is named `.c` or `.cpp`;
5. attaches any `@Invariant` comments to the following `while` loop;
6. instruments contracts into `Assume` and `Assert` statements;
7. lowers pointer, array, and shadow-memory obligations plus ghost-heap predicates into scalar ghost state when needed;
8. computes weakest preconditions for each function;
9. asks Z3 whether the negation of each VC is satisfiable; and
10. reports success or a counterexample.

If Z3 cannot find a model for the negated VC, the program is reported as verified.

If Z3 can find a model, Anvil prints the failing verification condition and the model values it found.

## Highlighting An Evolvable Scoring Hook

The example at `examples/vulcan_listener_scoring.cpp` shows the workflow for a policy-style program where:

- the whole program is verified;
- a scoring helper is visually marked with `EVOLVE-BLOCK-START` / `EVOLVE-BLOCK-END`; and
- the interesting proof obligations are written as contracts on that scoring helper.

Those `EVOLVE-BLOCK` comments are currently documentary only.
They are meant to spotlight the code a synthesis or editing loop would change, while `./anvil --verify` still checks the full file.

## Strict Mode

Pass `--strict` to reject surface syntax that directly manipulates memory.

In strict mode, Anvil rejects:

- pointer types and reference types;
- array types and array indexing;
- address-of, dereference, and `->` syntax; and
- `free`.

Strict mode also requires variables to be explicitly initialized:

- local declarations like `int x;` are rejected; and
- top-level globals are rejected, since the current surface syntax does not support initialized global declarations.

This is a syntactic restriction layer on top of ordinary parsing and verification.
For example, both of these are valid entry points:

```bash
./anvil --strict program.c
./anvil --strict --verify program.c
```

## Function Contracts

Anvil understands five function contract clause kinds:

- `@Ghost`
- `@Require`
- `@Guarantee`
- `@Theorem`
- `@Safety`

Contracts are written in comments with an explicit function target:

- `@Contract function_name`

Multiple contract blocks for the same function are merged conjunctively.
Within those blocks, repeated `@Ghost`, `@Require`, `@Guarantee`, `@Theorem`, and `@Safety` lines are also merged conjunctively.
Each clause kind is optional: if a function has no clauses of a given kind, Anvil adds no obligation or assumption for that kind.

These comments can appear at top level either:

- in a local header included with `#include "..."`; or
- in the current source file, including `.c` and `.cpp` inputs.

When `@Contract function_name` is present, Anvil associates the block with that function by name rather than by physical adjacency.

The older shorthand without `@Contract ...`, placed immediately before the declaration or definition, is still accepted for compatibility.

### Example: Contract In A Header

```c
/* @Contract inc
 * @Ghost int baseline = x
 * @Require x >= 0
 * @Guarantee result > x
 * @Safety baseline <= 10
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

/* @Contract inc
 * @Ghost int baseline = y
 * @Require y >= 0
 * @Guarantee result > y
 * @Safety baseline >= 0
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

- each `@Ghost` binding once at function entry;
- each `@Require` clause as a caller obligation;
- each `@Guarantee` clause as a post-call assumption; and
- imported `@Theorem` clauses on external functions as reusable assumptions; and
- each `@Safety` clause as a post-call assumption.

Inside a contracted function body, Anvil treats:

- each `@Ghost` binding as an immutable verifier-only name fixed at entry;
- each `@Require` clause as an entry assumption;
- each `@Guarantee` clause as an assertion at each `return`; and
- each `@Theorem` clause as a separate global proof obligation for the function; and
- each `@Safety` clause as a proof obligation that must hold after every command.

Use `result` inside `@Guarantee` to refer to the returned value.
Use `@Theorem` for global laws about a function, such as quantified order properties of `compare(x, y)`.
`@Theorem` clauses should not mention `result`; they are about function applications like `f(x)` rather than the current return site.

Example of a split contract:

```c
/* @Contract inc
 * @Ghost int baseline = x
 */
/* @Contract inc
 * @Require x >= 0
 */
/* @Contract inc
 * @Guarantee result >= x
 */
/* @Contract inc
 * @Safety x <= 10
 */
int inc(int x);
```

Example of guarded cases with multiple contract blocks:

```c
/* @Contract signed_from_bit
 * @Guarantee bit ==> result > 0
 */
/* @Contract signed_from_bit
 * @Guarantee (!bit) ==> result < 0
 */
int signed_from_bit(bool bit) {
  if (bit) {
    return 7;
  } else {
    return -3;
  }
}
```

This works because contract clauses are conjunctive.
The first clause says that when `bit` is true the result must be positive, and the second says that when `bit` is false the result must be negative.
Contract comments and loop invariants also accept implication sugar: `premise ==> obligation`.
It is parsed only in annotation syntax and desugars to `!premise || obligation`.
Contract comments also accept either `=` or `==` for equality.

Example with a ghost binding:

```c
/* @Contract signed_from_bit
 * @Ghost bool bit_is_set = bit != 0
 * @Guarantee bit_is_set ==> result > 0
 * @Guarantee (!bit_is_set) ==> result < 0
 */
int signed_from_bit(bool bit) {
  if (bit) {
    return 7;
  } else {
    return -3;
  }
}
```

`@Ghost` bindings are evaluated at function entry and are immutable afterward.
They are useful for naming derived facts once and reusing them across `@Require`, `@Guarantee`, `@Safety`, and loop invariants.
This first implementation supports scalar ghost types: `int`, `float`, `double`, `char`, and `bool`.

Contracts and loop invariants may also use universal quantification.
The syntax is:

```c
forall(int i, int* p). formula
```

Each quantified variable must carry an explicit type annotation.
The current implementation supports scalar binder types `int`, `float`, `double`, `char`, and `bool`, plus pointer binder types such as `int*`, `void*`, and `struct node*`.
Bare record values, arrays, and reference types are not supported as quantified binders.

Example:

```c
/* @Contract bump
 * @Guarantee forall(int i). (((i >= 0) && (i <= x)) ==> (result > i))
 * @Guarantee forall(int* p). (is_null(p) || !is_null(p))
 */
int bump(int x) {
  return (x + 1);
}
```

The first quantified clause says that every integer between `0` and `x` is strictly below the returned value.
The second shows that quantified pointer variables are also allowed, provided they are explicitly typed.

Example of a theorem-style comparator specification:

```c
/* @Contract compare_int
 * @Guarantee (x <= y) ==> (result <= 0)
 * @Guarantee (result <= 0) ==> (x <= y)
 * @Guarantee (y <= x) ==> (result >= 0)
 * @Guarantee (result >= 0) ==> (y <= x)
 * @Guarantee (x == y) ==> (result == 0)
 * @Guarantee (result == 0) ==> (x == y)
 * @Theorem forall(int x). compare_int(x, x) = 0
 * @Theorem forall(int x, int y). (compare_int(x, y) = 0) ==> (x = y)
 * @Theorem forall(int x, int y, int z). (((compare_int(x, y) <= 0) && (compare_int(y, z) <= 0)) ==> (compare_int(x, z) <= 0))
 */
int compare_int(int x, int y) {
  if (x < y) {
    return -1;
  }
  if (y < x) {
    return 1;
  }
  return 0;
}
```

Anvil proves these `@Theorem` clauses from the ordinary `@Guarantee` / `@Safety` summaries of contracted functions.
This is the intended way to write concise quantified laws over calls such as `compare_int(x, y)` without manually building a separate proof harness function.
When a theorem comes from an imported header for a function with no local definition in the current translation unit, Anvil treats it as a trusted modular assumption for the client file.
When the function is defined locally, Anvil instead checks the theorem against that local definition and does not feed it back in as an assumption while verifying the same translation unit.

`@Safety` is intended to describe a state property that is preserved throughout execution.
Operationally, Anvil assumes it after a contracted call, and proves it inside a contracted implementation.
In practice, `@Safety` should be written as a state invariant rather than as a property of `result`.

## Records, Classes, And Namespaces

Anvil supports a small structural-data and C++-flavored frontend fragment:

- `struct` declarations with scalar, pointer, fixed-size array, and nested record fields;
- field access with `x.f` and pointer field access with `p->f`;
- `class` declarations as frontend sugar for a record plus methods; and
- `namespace` blocks with `::` qualified references.

Method calls like `obj.put(7)` and `ptr->get()` are resolved statically before verification.
The pretty-printer emits flattened C rather than the original `class` / `namespace` syntax, so names become forms like `math__ns__Pair` and `Counter__put`.

This is still a minimal C++-style fragment:

- no inheritance
- no constructors or destructors
- no templates
- no virtual dispatch

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

## References

Anvil supports a small C++-style reference fragment for function and method parameters:

- `T&`
- `const T&`

The current surface support is intentionally narrow:

- references are supported in parameters, not in returns, globals, locals, or fields;
- `T` must currently be a scalar type or a record type; and
- temporary lifetime extension is not modeled, so a reference argument must be an addressable lvalue.

Operationally, references are front-end syntax only.
Before the ordinary memory lowering pass runs:

- `T& x` is rewritten to a pointer parameter `T* x`;
- `const T& x` is rewritten to the same pointer representation, but treated as read-only at direct write sites;
- reading `x` is rewritten to `*x`;
- assigning `x = e` is rewritten to a store through that pointer; and
- taking `&x` reuses the underlying pointer alias instead of creating a separate reference cell.

This means reference uses inherit the same side conditions as the pointer model:

- every read through `x` or `x.f` must satisfy the same modeled read-validity check as a dereference;
- every direct write through `x` or `x.f` must satisfy the same modeled write-validity check as a pointer store; and
- passing an argument to a reference parameter requires a syntactic lvalue so Anvil can materialize an address for it.

For `const T&`, Anvil currently rejects direct writes through that alias:

- `x = e`
- `x.f = e`
- passing that same alias to a mutable `T&` parameter

This is a lightweight alias discipline rather than full C++ cv-qualification.
In particular:

- writes through other aliases remain possible; and
- if a const-referenced record contains a pointer-valued field, writing through the pointee of that field is treated as a separate pointer effect rather than as a direct write to the record.

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

Anvil uses a fixed byte-size model for the supported first-order types:

- `int` and `float`: 4 bytes
- `double`: 8 bytes
- `char` and `bool`: 1 byte
- pointers: 8 bytes

Record and array sizes are computed from those modeled field and element sizes.
`malloc(n)` is interpreted in bytes, a read or write through `T*` consumes `sizeof(T)` modeled bytes, and `p + 1` advances by that same modeled object size.

When Anvil sees pointer syntax or ghost-heap predicates, it lowers memory into ghost state:

- each pointer variable is represented as a `(block, offset)` pair;
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
- `allocated(p)`: pointer `p` designates at least one readable cell of its modeled pointee type.
- `live(p)`: the block named by `p` is live. Scalar globals are always live.
- `can_free(p)`: `p` is null or the base address of a live allocation.
- `same_block(p, q)`: `p` and `q` refer to the same block.
- `is_null(p)`: `p` is the null pointer.

These predicates are lowered into ordinary scalar formulas before weakest-precondition generation, so they participate in verification just like any other contract formula.

## Arrays

Anvil supports fixed-size arrays in globals, locals, and record or class fields.

The existing verifier handles scalar element arrays directly, and also supports record-valued arrays when access continues down to scalar leaves, such as `node.leaves[1].value`.

The surface syntax includes:

- declarations like `int xs[4];`
- indexed reads like `xs[i]` and `p[i]`
- indexed writes like `xs[i] = e;`
- indexed addresses like `&xs[i]`; and
- nested field/index combinations like `node.leaves[1].value`

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

- arrays must be fixed-size declarations
- nested arrays are unsupported
- array parameters and array return types are not supported yet
- globals and locals with pointer-element arrays are currently rejected

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

- global scalar, record, pointer, and fixed-size array variables
- function-local scalar, record, pointer, and fixed-size array declarations
- nested block scopes with local-variable shadowing
- `struct` definitions with scalar, pointer, fixed-size array, and nested record fields
- `class` definitions with methods
- `namespace` blocks and `::` qualified names
- scalar-valued and `void` functions and methods
- local helper function definitions before `main`
- local header imports with `#include "file.h"`
- exact-match overload resolution for free functions and methods
- reference parameters `T&` and `const T&`
- integer, float, double, char, and bool literals
- variables
- field access such as `x.f` and pointer field access such as `p->f`
- method calls such as `obj.m(...)` and `ptr->m(...)`
- address-of for addressable lvalues such as `&x`, `&xs[0]`, and `&node.leaf`
- pointer dereference reads such as `*p`
- pointer dereference writes such as `*(p + 1) = 7;`
- array reads and writes such as `xs[i]` and `xs[i] = 7;`
- `malloc(n)` and `free(p)`
- function calls
- compound assignments `+=` and `-=`
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
If the input uses classes, namespaces, references, or overloads, the emitted program is their desugared C form with flattened names and explicit lowered calls.

For example, a contracted local function call becomes a sequence like:

- `Assert(@Require)`
- call into a temporary result variable
- `Assume(@Guarantee)`
- `Assume(@Safety)`

## Current Limitations

- Pointer safety support is currently a shadow-memory proof-of-concept rather than a full symbolic heap.
- Memory safety is opt-in through contracts such as `@Safety heap_ok()`. Pointer operations alone do not add user-visible proof obligations.
- Pointer parameters are supported, but pointer return values are currently unsupported in the verifier's memory lowering.
- Pointer-to-pointer operations, nested arrays, and direct dereference of `void*` are unsupported in the current memory model.
- By-value record parameters, array parameters, and pointer / array / record / reference return types are unsupported in the verifier.
- Reference parameters are supported, but only for scalar and record types.
- General `const` surface syntax is not modeled beyond `const T&`; for example, `const T*` is currently rejected.
- Contracts may mention reference parameters, but post-state reasoning about an arbitrary referenced cell is still limited by the current shadow-memory model.
- Memory contents are not modeled precisely yet: loads become uninterpreted values, while the ghost-heap predicates cover bounds, liveness, null, and invalid free conditions.
- `malloc` uses an allocation-site abstraction rather than a full heap model.
- `float` and `double` are verified with an idealized real-valued encoding rather than IEEE-754 semantics.
- `@Ghost` currently supports only scalar ghost types, and ghost initializers are fixed at function entry rather than being mutable state.
- Instrumentation of contracted `void` calls is currently unsupported.
- Instrumented calls inside quantified formulas, `&&`, `||`, or `while` conditions are currently unsupported.
- Translation mode does not currently lower instrumented quantified assertions and assumptions into compilable C; quantified examples are best used with `--verify`.
- Verification models function calls in formulas as uninterpreted functions in Z3, but contracted functions also contribute universally quantified summary axioms from `@Guarantee` and `@Safety`.
- Imported `@Theorem` clauses are reusable assumptions for external functions, but locally checked `@Theorem` clauses are not currently fed back in as additional assumptions inside the same translation unit.
- Only local quoted includes are used for contract imports: `#include "file.h"`.
- Named `@Contract foo` blocks must resolve to a unique function during contract loading; overloaded same-name targets are currently rejected as ambiguous.

## Examples In This Repository

Useful examples live in `test/e2e_cases/`:

- `contract_import_scalar.c`
- `contract_local_scalar.c`
- `contract_multiple_guards.c`
- `ghost_contract_sign.c`
- `modular_composition_scalar.c`
- `modular_composition_memory.c`
- `modular_theorem_import.c`
- `modular_theorem_local_definition.c`
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

Larger hand-written examples live in `examples/`:

- `comparator_total_order.c`
- `ghost_contract_sign.c`
- `ghost_contract_sign_bad.c`
- `multi_contract_sign.c`
- `multi_contract_sign_bad.c`
- `quantified_contract_bump.c`
- `quantified_contract_bump_bad.c`
- `vulcan_listener_scoring.cpp`
- `policysmith_dispatch_policy.cpp`

## Development Checks

Run the OCaml test suite:

```bash
./_build/default/test/test_anvil.exe
```

Run the translation end-to-end cases:

```bash
ANVIL_SKIP_BUILD=1 ./test/run_e2e.sh
```
