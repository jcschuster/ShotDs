# Changelog

## v1.3.0

### Breaking

- **Binders now scope over a single `<thf_unit_formula>`, as the TPTP BNF
  prescribes.** A binder body is an atom, a variable, a parenthesised formula,
  another binder, a `~`-prefixed unit formula or an infix (in)equation; an
  application chain or a binary connective that follows the body belongs to the
  enclosing formula:

  - `^ [X: $i] : f @ g` now reads `( ^ [X: $i] : f ) @ g` (the BNF states this
    case explicitly), and `! [X: $o] : $false => p` now reads
    `( ! [X: $o] : $false ) => p`.
  - Formulas that relied on the previous greedy reading must parenthesise their
    body: `! [X: $i] : ( p @ X )`.

  This fixes the family of `Cannot unify …` type errors on TPTP problems that
  pass an unparenthesised binder as an argument, e.g. `SET640^3`'s
  `cartesian_product @ ^ [X: $i] : $true @ ^ [X: $i] : $true`, and lets a binder
  body contain an equation (`^ [X: $i] : ( p @ X ) = ( q @ X )`).

  Unparsing already brackets binder bodies, so output of `ShotDs.Parser.unparse/1`
  and `ShotDs.Tptp.unparse_problem/1` is unaffected and still round-trips.

- Juxtaposition of a quantifier and its predicate (`! p` for `∀ p`) is no longer
  accepted; use the application form `!! @ p`.

### Fixed

- TH1 type arguments are now recognised when written as `<single_quoted>` words,
  matching the other type-parsing sites. Problems whose type names are quoted
  throughout (e.g. everything including `Axioms/MAT001^0.ax`) previously failed
  with `Cannot unify strict function types of different arities`.

- `ShotDs.Parser.unparse/1` no longer drops the name of a bound variable that is
  passed as an argument. Such an argument is stored η-expanded, and collapsing
  the expansion left the head's de Bruijn index pointing past the enclosing
  scope (`(cp @  @ X2)` instead of `(cp @ X1 @ X2)`).

- `ShotDs.Parser.unparse_type/1` renders a mapping type into a user-declared
  base type as `$int > pt` instead of `pt @ $int`. Mapping types and type
  applications share one representation, so the type-application form is now
  used only for names declared with a type-constructor kind; `ShotDs.Tptp`
  registers them from the problem's type declarations while unparsing, and
  `ShotDs.Parser.with_type_constructors/2` exposes this for direct callers.

- TPTP's arithmetic constants (`$less`, `$lesseq`, `$greater`, `$greatereq`,
  `$sum`, `$difference`, `$product`, `$quotient`, `$quotient_e/_t/_f`,
  `$remainder_e/_t/_f`, `$uminus`, `$floor`, `$ceiling`, `$truncate`, `$round`,
  `$is_int`, `$is_rat`, `$to_int`, `$to_rat`, `$to_real`) are ad-hoc polymorphic
  in the numeric sort instead of being fixed to one sort per problem, so a
  formula may compare `$int`s and `$real`s.
