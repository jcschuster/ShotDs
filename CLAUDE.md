# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Commands

```bash
mix deps.get          # install dependencies
mix test              # run all tests
mix test test/shot_ds/parser_test.exs          # run a single test file
mix test test/shot_ds/parser_test.exs:42       # run test at specific line
mix credo --all       # lint (also run by CI)
mix dialyzer          # type checking (also run by CI)
mix format            # format code
mix docs              # generate ExDoc documentation
```

CI runs `mix credo`, `mix dialyzer`, and `mix test` on every push to `main`.

## What This Library Is

**ShotDs** is an Elixir library implementing data structures and algorithms for **Classical Higher-Order Logic (HOL)**, specifically Church's Simple Type Theory (STT) extended to HOL. It provides:

- Efficient term caching via ETS as Directed Acyclic Graphs (DAGs)
- Full βη-normalization with de Bruijn indices for bound variables
- Type inference (Hindley-Milner rank-1 / Algorithm W)
- A DSL for constructing HOL terms in Elixir
- A parser for TPTP's TH0 (and TH1 with polymorphism) formula syntax

## Architecture

### Layer Overview

```
ShotDs.Data.*         ← Core data structs (Type, Declaration, Term, Substitution, Context, Problem)
ShotDs.Stt.*          ← Simple Type Theory engine (term creation, ETS cache, substitution, β-reduction)
ShotDs.Hol.*          ← HOL-level API (logical connectives, DSL operators, sigils, patterns)
ShotDs.Parser         ← TH0/TH1 formula string parser with type inference
ShotDs.Tptp           ← TPTP problem file parser (requires $TPTP_ROOT for library files)
ShotDs.Util.*         ← Formatter, TermTraversal (DAG map combinator), TypeInference, Lexer
ShotDs               ← Facade module delegating to all layers
```

### Term ID System

The most important invariant in this codebase: **terms are identified by integers, not nested structs**.

- `term_id > 0` — global ID, lives in the named ETS table `:term_pool` (owned by `ShotDs.TermPoolOwner` GenServer)
- `term_id < 0` — local/scratchpad ID, lives in a per-process private ETS table
- `term_id == 0` — dummy sentinel (never stored in ETS)

The ETS key for deduplication is the **signature** — all fields of `Term.t` except `:id`. Identical terms always get the same global ID.

### Scratchpad Pattern

Building terms (especially abstractions involving fresh free variables) requires temporary local terms that must be garbage-collected. The pattern is:

```elixir
TF.with_scratchpad!(fn ->
  # work here — memoize() writes to the local scratchpad
  # return a local term_id
end)
# → local IDs are committed to global ETS; scratchpad is cleaned up
```

Functions that call `make_abstr_term!/2` or `make_fresh_var_term/1` should be wrapped with `with_scratchpad!` (or the caller should already have a scratchpad open — the function is idempotent in that case).

### Type Representation

`ShotDs.Data.Type` uses an **uncurried** representation: `α → β → γ` is stored as `%Type{goal: :γ, args: [α, β]}`. The `goal` is the return type; `args` are the argument types left-to-right.

`Type.new(:o, [:i, :i])` = `ι → ι → o` (a binary relation on individuals).

Type variables are Erlang references (`make_ref()`). Concrete base types are atoms (`:o`, `:i`, or user-defined).

### Canonical API Entry Points

| Task | Module |
|---|---|
| Parse TH0 formula string | `ShotDs.Parser.parse!/1` or `~f""` sigil |
| Parse TPTP problem file | `ShotDs.Tptp.parse_tptp_file/2` |
| Build terms programmatically | `ShotDs.Hol.Dsl` (operators `&&&`, `\|\|\|`, `~>`, `<~>`, `lambda/2`, `forall/2`, `exists/2`) |
| Low-level term construction | `ShotDs.Stt.TermFactory` |
| Pretty-print any HOL object | `ShotDs.Util.Formatter.format!/1` or `format!/2` |
| Substitution / β-reduction | `ShotDs.Stt.Semantics.subst/2`, `subst!/2` |

### Error Handling Convention

Every function that can fail has two variants:
- `foo/n` — returns `{:ok, result}` or `{:error, reason}`
- `foo!/n` — returns `result` directly or raises `ArgumentError`

### Key Design Facts

- All constructed terms are always in **βη-normal form**. Application triggers β-reduction automatically in `make_appl_term/2`.
- Bound variables use **de Bruijn indices** (`:bv` declarations with integer `:name`). Free variables carry string or reference names.
- The `:fvars`, `:consts`, `:tvars`, and `:max_num` fields on `Term.t` are denormalized caches for efficiency — they are always computed at construction time, not on demand.
- `ShotDs.Hol.Patterns` provides pattern-matching helpers (e.g., `match_connective/1`) useful when inspecting parsed terms.
- `ShotDs.Stt.Numerals` and `ShotDs.Stt.Booleans` implement Church encodings over type `:i`.

### TPTP Parsing Notes

- `TPTP_ROOT` environment variable must be set to parse files from the TPTP problem library (`:tptp_problem` origin). Not needed for custom files (`:custom` origin).
- `ShotDs.Tptp` handles `include/1` directives recursively.
- TH1 polymorphism is supported: unknown types become type variables (references), with outer type `o` forced when `force_o: true` (the default in the `~f` sigil).
