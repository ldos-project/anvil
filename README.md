# Anvil

Anvil is the DSL in which Vulcan writes LLM-generated policies. `anvil --gate` is the main command - it takes an evolve block -- consisting of a listener configuration plus a `scoring_fn` lambda -- and checks whether it parses successfully into the DSL.

This repo (and the `anvil` binary) also contains some solver-based verification modes (`--verify`, `--strict`) which are used by another project and are not directly relevant to `vulcan`.

## Requirements

- `ocaml` (>= 4.08; tested on 4.13.1)
- `dune` **>= 3.21**
- `menhir` (tested on 20210929)

Install dune and menhir:

```bash
opam init && opam install dune menhir
```

or from source:

```bash
curl -sLO https://github.com/ocaml/dune/releases/download/3.21.0/dune-3.21.0.tbz
tar xf dune-3.21.0.tbz && cd dune-3.21.0 && make release
sudo install -m 0755 _boot/dune.exe /usr/local/bin/dune
```

## Building

```bash
dune build ./bin/main.exe
```

Then run either `./anvil` or `./_build/default/bin/main.exe`. The `./anvil` wrapper runs `dune build ./bin/main.exe` for you first, unless `ANVIL_SKIP_BUILD=1` is set.

## Gate Mode

```bash
./anvil --gate candidate.cpp
cat candidate.cpp | ./anvil --gate
```

`anvil --gate` takes a source file and reports the verdict as its exit status: zero prints `Safe.`, and any failure to parse into the DSL exits non-zero and prints `Unsafe: <reason>`. Vulcan scores rejected candidates `-1` and feeds the reason back to the LLM.

An accepted candidate is memory-safe, leak-free, and terminating. Termination holds by construction, which is what makes the accepted subset narrow:

- locals are `int`, `double`, or `bool`. `int64_t` appears only on the scoring function's `obj_id` parameter, so feature reads are converted on the way in: `double v = static_cast<double>(fs.get_latest(...))`.
- the only loop form is a counted `for`: literal init and bound, an `i++`/`i--` step matching the comparison direction, and a body that never assigns to the counter. There is no `while`.
- at most 4096 iterations per loop, and `|endpoint| <= 2^30` so the counter can neither wrap nor lose precision.
- `break` and `continue` are allowed inside a loop.
- no recursion, direct or transitive.
- no pointers, arrays, heap allocation, or `free`.

The same subset is documented for the LLM in `libcachesim/libvulcan/prompts/vulcan_policy_prompt.md` in the `vulcan-usecases` repo.

Run the gate suite in `test/gate_cases/` with `make test`.
