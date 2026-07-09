defmodule ShotDs.Util.LatexFormatterTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Data.{Declaration, Problem, Substitution, Type}
  alias ShotDs.Hol.Definitions
  alias ShotDs.Hol.Dsl
  alias ShotDs.Util.LatexFormatter, as: LF

  ##############################################################################
  # Types
  ##############################################################################

  describe "types" do
    test "base type o" do
      assert LF.format!(Type.new(:o)) == "o"
    end

    test "base type i as \\iota" do
      assert LF.format!(Type.new(:i)) == "\\iota"
    end

    test "user-defined base type wraps in \\mathrm" do
      assert LF.format!(Type.new(:nat)) == "\\mathrm{nat}"
    end

    test "arrow type is right-associative and unparenthesised on the goal side" do
      # ι → ι → o
      assert LF.format!(Type.new(:o, [:i, :i])) == "\\iota \\to \\iota \\to o"
    end

    test "left-side arrow subtype gets parenthesised" do
      # (ι → o) → o
      assert LF.format!(Type.new(:o, Type.new(:o, :i))) == "(\\iota \\to o) \\to o"
    end

    test "math_mode :inline wraps in $…$" do
      assert LF.format!(Type.new(:o), math_mode: :inline) == "$o$"
    end

    test "math_mode :display wraps in $$…$$" do
      assert LF.format!(Type.new(:o), math_mode: :display) == "$$o$$"
    end
  end

  ##############################################################################
  # Declarations
  ##############################################################################

  describe "declarations" do
    test "logical constant renders as LaTeX symbol without type" do
      assert LF.format!(Definitions.and_const()) == "\\wedge"
      assert LF.format!(Definitions.forall_const(Type.new(:i))) == "\\forall"
      assert LF.format!(Definitions.true_const()) == "\\top"
    end

    test "non-logical constant uses \\mathrm with type subscript" do
      c = Declaration.new_const("mortal", Type.new(:o, :i))
      assert LF.format!(c) == "\\mathrm{mortal}_{\\iota \\to o}"
    end

    test "free variable renders with type subscript" do
      v = Declaration.new_free_var("X", Type.new(:i))
      assert LF.format!(v) == "X_{\\iota}"
    end

    test "hide_types omits subscript on non-logical symbols" do
      c = Declaration.new_const("mortal", Type.new(:o, :i))
      assert LF.format!(c, hide_types: true) == "\\mathrm{mortal}"
    end
  end

  ##############################################################################
  # Term rendering — heads, application, connectives
  ##############################################################################

  describe "terms — heads and application" do
    test "a bare constant renders as \\mathrm{name}_{τ}" do
      id = Dsl.const("a", Type.new(:i))
      assert LF.format!(id) == "\\mathrm{a}_{\\iota}"
    end

    test "a bare free variable renders with type subscript" do
      id = Dsl.var("Y", Type.new(:o))
      assert LF.format!(id) == "Y_{o}"
    end

    test "predicate application uses ~ as juxtaposition" do
      # P X where P : ι → o and X : ι
      pred = Dsl.var("P", Type.new(:o, :i))
      x = Dsl.var("X", Type.new(:i))
      id = Dsl.app(pred, x)

      assert LF.format!(id) == "P_{\\iota \\to o}~X_{\\iota}"
    end

    test "multi-argument function application chains ~" do
      # F X Y Z where F : ι → ι → ι → ι
      f = Dsl.var("F", Type.new(:i, [:i, :i, :i]))
      x = Dsl.var("X", Type.new(:i))
      y = Dsl.var("Y", Type.new(:i))
      z = Dsl.var("Z", Type.new(:i))
      id = Dsl.app(f, [x, y, z])

      assert LF.format!(id) ==
               "F_{\\iota \\to \\iota \\to \\iota \\to \\iota}~X_{\\iota}~Y_{\\iota}~Z_{\\iota}"
    end

    test "infix connective uses op with regular spaces, not ~" do
      import Dsl
      p = var("P", Type.new(:o))
      q = var("Q", Type.new(:o))
      id = p &&& q

      assert LF.format!(id) == "P_{o} \\wedge Q_{o}"
    end

    test "negation is prefix with a space" do
      import Dsl
      p = var("P", Type.new(:o))
      id = neg(p)

      assert LF.format!(id) == "\\neg P_{o}"
    end

    test "complex infix arguments are parenthesised" do
      import Dsl
      p = var("P", Type.new(:o))
      q = var("Q", Type.new(:o))
      r = var("R", Type.new(:o))
      id = (p &&& q) ||| r

      assert LF.format!(id) == "(P_{o} \\wedge Q_{o}) \\vee R_{o}"
    end
  end

  ##############################################################################
  # Binder reconstruction, fresh names, superscript disambiguation
  ##############################################################################

  describe "binder reconstruction" do
    test "λ over ι picks 'X' from the individual pool" do
      # λx_ι. x
      id = Dsl.lambda(Type.new(:i), fn x -> x end)
      assert LF.format!(id) == "\\lambda X_{\\iota}.\\,X"
    end

    test "chained λs pick successive pool names" do
      # λx y z. y  (all type ι)
      id =
        Dsl.lambda([Type.new(:i), Type.new(:i), Type.new(:i)], fn _x, y, _z ->
          y
        end)

      # bvars = [X, Y, Z]; body is bound-var #2 → Y
      assert LF.format!(id) == "\\lambda X_{\\iota}\\ Y_{\\iota}\\ Z_{\\iota}.\\,Y"
    end

    test "λ over o picks 'P' from the proposition pool" do
      id = Dsl.lambda(Type.new(:o), fn p -> p end)
      assert LF.format!(id) == "\\lambda P_{o}.\\,P"
    end

    test "λ over ι→o picks 'P' from the predicate pool (η-expanded)" do
      # λ p_(ι→o). p — stored in η-normal form as λ p x. p x.
      pred_type = Type.new(:o, :i)
      id = Dsl.lambda(pred_type, fn p -> p end)

      assert LF.format!(id) ==
               "\\lambda P_{\\iota \\to o}\\ X_{\\iota}.\\,P~X"
    end

    test "λ over ι→ι picks 'F' from the function pool (merged bvars)" do
      # Church numeral-2 style: `λ f c. f (f c)` — outer lambda merges with the
      # inner lambda into a single 2-arg abstraction on the term struct.
      f_type = Type.new(:i, :i)

      id =
        Dsl.lambda(f_type, fn f ->
          Dsl.lambda(Type.new(:i), fn c ->
            Dsl.app(f, Dsl.app(f, c))
          end)
        end)

      assert LF.format!(id) ==
               "\\lambda F_{\\iota \\to \\iota}\\ X_{\\iota}.\\,F~(F~X)"
    end

    test "binder avoids free-variable name (taboo set)" do
      # λ over ι, but a free variable named X already exists in scope;
      # the binder must not shadow it. Use body = f(bound, X).
      x_free = Dsl.var("X", Type.new(:i))
      f = Dsl.var("F", Type.new(:i, [:i, :i]))

      id =
        Dsl.lambda(Type.new(:i), fn bound ->
          Dsl.app(f, [bound, x_free])
        end)

      # X taken → next pool letter Y
      assert LF.format!(id) ==
               "\\lambda Y_{\\iota}.\\,F_{\\iota \\to \\iota \\to \\iota}~Y~X_{\\iota}"
    end

    test "higher-order predicate falls back to the predicate pool (no \\mathcal)" do
      # λ P_((ι→o)→o). ⊤   -- HO predicate: P Q R S; body stays constant.
      ho_pred_type = Type.new(:o, Type.new(:o, :i))
      top = Dsl.const("⊤", Type.new(:o))
      id = Dsl.lambda(ho_pred_type, fn _p -> top end)

      # Renders with plain "P" (not \mathcal{P}) and the special "⊤" symbol.
      rendered = LF.format!(id)
      assert rendered =~ "\\lambda P_"
      refute rendered =~ "\\mathcal"
    end

    test "superscript disambiguation when the entire pool is taboo" do
      # Free variables occupying the full individual pool.
      xs = ~w(X Y Z U V W)
      free_ids = Enum.map(xs, &Dsl.var(&1, Type.new(:i)))

      # Build a nullary body that references all free vars so they land in
      # fvars: f(X, Y, Z, U, V, W)
      f =
        Dsl.var(
          "F",
          Type.new(:o, [:i, :i, :i, :i, :i, :i])
        )

      base = Dsl.app(f, free_ids)

      # Now wrap in λ over ι; expect superscript "X^{1}".
      id = Dsl.lambda(Type.new(:i), fn _b -> base end)
      rendered = LF.format!(id)

      assert String.starts_with?(rendered, "\\lambda X^{1}_{\\iota}")
    end
  end

  ##############################################################################
  # Quantifier merging with binder
  ##############################################################################

  describe "quantifier binder merging" do
    test "∀ (λ x. p x) prints as \\forall X.\\, ..." do
      # ∀ x_ι. p x
      pred = Dsl.var("P", Type.new(:o, :i))
      id = Dsl.forall(Type.new(:i), fn x -> Dsl.app(pred, x) end)

      assert LF.format!(id) == "\\forall X_{\\iota}.\\,P_{\\iota \\to o}~X"
    end

    test "chained ∀∀ merges recursively" do
      rel = Dsl.var("R", Type.new(:o, [:i, :i]))

      id =
        Dsl.forall([Type.new(:i), Type.new(:i)], fn x, y ->
          Dsl.app(rel, [x, y])
        end)

      assert LF.format!(id) ==
               "\\forall X_{\\iota}.\\,\\forall Y_{\\iota}.\\,R_{\\iota \\to \\iota \\to o}~X~Y"
    end

    test "∃ merges the same way" do
      pred = Dsl.var("P", Type.new(:o, :i))
      id = Dsl.exists(Type.new(:i), fn x -> Dsl.app(pred, x) end)

      assert LF.format!(id) == "\\exists X_{\\iota}.\\,P_{\\iota \\to o}~X"
    end

    test "merge_binder: false disables the merge" do
      pred = Dsl.var("P", Type.new(:o, :i))
      id = Dsl.forall(Type.new(:i), fn x -> Dsl.app(pred, x) end)

      assert LF.format!(id, merge_binder: false) ==
               "\\forall~(\\lambda X_{\\iota}.\\,P_{\\iota \\to o}~X)"
    end
  end

  ##############################################################################
  # Raw index mode (reconstruct_names: false)
  ##############################################################################

  describe "raw de Bruijn indices" do
    test "λ x. x renders as \\lambda_{τ}.\\, \\mathtt{1}_{τ}" do
      id = Dsl.lambda(Type.new(:i), fn x -> x end)

      assert LF.format!(id, reconstruct_names: false) ==
               "\\lambda_{\\iota}.\\,\\mathtt{1}_{\\iota}"
    end

    test "nested λs render as separate \\lambda_{τ}\\ \\lambda_{τ}" do
      # λ f c. f (f c) — bvars merged into [F, X], body refs = #2, #1.
      f_type = Type.new(:i, :i)

      id =
        Dsl.lambda(f_type, fn f ->
          Dsl.lambda(Type.new(:i), fn c ->
            Dsl.app(f, Dsl.app(f, c))
          end)
        end)

      assert LF.format!(id, reconstruct_names: false) ==
               "\\lambda_{\\iota \\to \\iota}\\ \\lambda_{\\iota}.\\," <>
                 "\\mathtt{2}_{\\iota \\to \\iota}~" <>
                 "(\\mathtt{2}_{\\iota \\to \\iota}~\\mathtt{1}_{\\iota})"
    end

    test "quantifier merge is disabled to expose raw constructor structure" do
      pred = Dsl.var("P", Type.new(:o, :i))
      id = Dsl.forall(Type.new(:i), fn x -> Dsl.app(pred, x) end)

      assert LF.format!(id, reconstruct_names: false) ==
               "\\forall~(\\lambda_{\\iota}.\\,P_{\\iota \\to o}~\\mathtt{1}_{\\iota})"
    end

    test "hide_types drops the type subscripts on binders and indices" do
      id = Dsl.lambda(Type.new(:i), fn x -> x end)

      assert LF.format!(id, reconstruct_names: false, hide_types: true) ==
               "\\lambda.\\,\\mathtt{1}"
    end
  end

  ##############################################################################
  # Substitutions and problems
  ##############################################################################

  describe "substitutions and problems" do
    test "substitution renders as [term ~/~ var]" do
      fvar = Declaration.new_free_var("X", Type.new(:i))
      term_id = Dsl.const("a", Type.new(:i))
      s = Substitution.new(fvar, term_id)

      assert LF.format!(s) == "[X_{\\iota} \mapsto \\mathrm{a}_{\\iota}]"
    end

    test "empty problem renders a comment header" do
      p = %Problem{}
      out = LF.format!(p)
      assert String.starts_with?(out, "% Problem <unnamed>")
    end
  end

  ##############################################################################
  # Dispatcher error handling
  ##############################################################################

  describe "dispatcher" do
    test "format/2 returns error for unknown argument" do
      assert LF.format(:not_a_thing) == {:error, :unknown_argument}
    end

    test "format/2 with invalid term ID returns error" do
      assert {:error, _} = LF.format(-999_999)
    end

    test "format!/2 with invalid term ID raises" do
      assert_raise ArgumentError, fn -> LF.format!(-999_999) end
    end

    test "format/2 on Type returns {:ok, string}" do
      assert LF.format(Type.new(:o)) == {:ok, "o"}
    end

    test "format/2 on Declaration returns {:ok, string}" do
      d = Declaration.new_free_var("X", Type.new(:i))
      assert LF.format(d) == {:ok, "X_{\\iota}"}
    end

    test "format/2 on Term struct dispatches through id" do
      id = Dsl.const("a", Type.new(:i))
      term = TF.get_term!(id)
      assert LF.format(term) == {:ok, "\\mathrm{a}_{\\iota}"}
    end

    test "format!/2 on Term struct returns the string" do
      id = Dsl.const("a", Type.new(:i))
      term = TF.get_term!(id)
      assert LF.format!(term) == "\\mathrm{a}_{\\iota}"
    end

    test "format/2 on Substitution returns {:ok, string}" do
      fvar = Declaration.new_free_var("X", Type.new(:i))
      term_id = Dsl.const("a", Type.new(:i))
      assert {:ok, str} = LF.format(Substitution.new(fvar, term_id))
      assert str == "[X_{\\iota} \mapsto \\mathrm{a}_{\\iota}]"
    end

    test "format/2 on Problem returns {:ok, string}" do
      assert {:ok, str} = LF.format(%Problem{})
      assert String.starts_with?(str, "% Problem <unnamed>")
    end
  end

  ##############################################################################
  # Skolem constants / anonymous refs
  #
  # These regression-test the crash where `render_decl(:co, ref, ...)` blew up
  # in `to_string(ref)`, and lock in the ^-disambiguator that keeps the type
  # subscript from producing a double-underscore in LaTeX.
  ##############################################################################

  describe "skolem constants (ref-named :co)" do
    test "bare Skolem constant renders as \\mathrm{c}^{shortref}_{τ}" do
      c = Declaration.fresh_const(Type.new(:i))
      short = Formatter.short_ref(c.name)

      assert LF.format!(c) == "\\mathrm{c}^{#{short}}_{\\iota}"
    end

    test "Skolem constant with hide_types drops type subscript" do
      c = Declaration.fresh_const(Type.new(:o, :i))
      short = Formatter.short_ref(c.name)

      assert LF.format!(c, hide_types: true) == "\\mathrm{c}^{#{short}}"
    end

    test "Skolem constant renders inside application spine" do
      ref = make_ref()
      c_id = TF.make_const_term(ref, Type.new(:i))
      p = Dsl.var("P", Type.new(:o, :i))
      id = Dsl.app(p, c_id)
      short = Formatter.short_ref(ref)

      assert LF.format!(id) ==
               "P_{\\iota \\to o}~\\mathrm{c}^{#{short}}_{\\iota}"
    end

    test ":hol_latex_aliases wins and is spliced verbatim as LaTeX" do
      c = Declaration.fresh_const(Type.new(:i))

      out =
        LF.with_latex_aliases(%{c.name => "\\hat{s}_{1}"}, fn ->
          LF.format!(c, hide_types: true)
        end)

      assert out == "\\hat{s}_{1}"
    end

    test ":hol_aliases (plain nickname) is used when no LaTeX alias is set" do
      c = Declaration.fresh_const(Type.new(:i))

      out =
        Formatter.with_aliases(%{c.name => "sko"}, fn ->
          LF.format!(c, hide_types: true)
        end)

      # Plain nicknames go through escape_name; underscores/hashes get escaped.
      assert out == "sko"
    end

    test "plain nickname is escaped when it contains LaTeX-special characters" do
      c = Declaration.fresh_const(Type.new(:i))

      out =
        Formatter.with_aliases(%{c.name => "a_b"}, fn ->
          LF.format!(c, hide_types: true)
        end)

      assert out == "a\\_b"
    end

    test ":hol_latex_aliases overrides :hol_aliases" do
      c = Declaration.fresh_const(Type.new(:i))

      out =
        Formatter.with_aliases(%{c.name => "plain"}, fn ->
          LF.with_latex_aliases(%{c.name => "\\heartsuit"}, fn ->
            LF.format!(c, hide_types: true)
          end)
        end)

      assert out == "\\heartsuit"
    end

    test "with_latex_aliases restores the previous binding on exit (nested)" do
      c = Declaration.fresh_const(Type.new(:i))

      LF.with_latex_aliases(%{c.name => "outer"}, fn ->
        LF.with_latex_aliases(%{c.name => "inner"}, fn ->
          assert LF.format!(c, hide_types: true) == "inner"
        end)

        assert LF.format!(c, hide_types: true) == "outer"
      end)

      # Once out of every scope, we're back to the shortref default.
      short = Formatter.short_ref(c.name)
      assert LF.format!(c, hide_types: true) == "\\mathrm{c}^{#{short}}"
    end
  end

  ##############################################################################
  # Anonymous free variables (ref-named :fv)
  ##############################################################################

  describe "fresh free variables (ref-named :fv)" do
    test "bare fresh var renders as V^{shortref}_{τ}" do
      v = Declaration.fresh_var(Type.new(:i))
      short = Formatter.short_ref(v.name)

      assert LF.format!(v) == "V^{#{short}}_{\\iota}"
    end

    test "fresh var with hide_types drops the type subscript" do
      v = Declaration.fresh_var(Type.new(:o))
      short = Formatter.short_ref(v.name)

      assert LF.format!(v, hide_types: true) == "V^{#{short}}"
    end

    test ":hol_latex_aliases is applied verbatim" do
      v = Declaration.fresh_var(Type.new(:i))

      out =
        LF.with_latex_aliases(%{v.name => "\\hat{Y}"}, fn ->
          LF.format!(v, hide_types: true)
        end)

      assert out == "\\hat{Y}"
    end

    test ":hol_aliases nickname is escaped" do
      v = Declaration.fresh_var(Type.new(:i))

      out =
        Formatter.with_aliases(%{v.name => "y_hat"}, fn ->
          LF.format!(v, hide_types: true)
        end)

      assert out == "y\\_hat"
    end
  end

  ##############################################################################
  # Type variables (ref-typed goals)
  ##############################################################################

  describe "type variables (ref-typed goals)" do
    test "bare type variable renders as \\tau_{shortref}" do
      ref = make_ref()
      short = Formatter.short_ref(ref)

      assert LF.format!(Type.new(ref)) == "\\tau_{#{short}}"
    end

    test ":hol_latex_aliases is applied verbatim to type goals" do
      ref = make_ref()

      out =
        LF.with_latex_aliases(%{ref => "\\alpha"}, fn ->
          LF.format!(Type.new(ref))
        end)

      assert out == "\\alpha"
    end

    test ":hol_aliases plain nickname is used verbatim for type goals" do
      # For type goals the plain-nickname branch does *not* run through
      # escape_name — it's already expected to be a valid LaTeX identifier.
      ref = make_ref()

      out =
        Formatter.with_aliases(%{ref => "alpha"}, fn ->
          LF.format!(Type.new(ref))
        end)

      assert out == "alpha"
    end
  end

  ##############################################################################
  # escape_name: LaTeX-special characters
  ##############################################################################

  describe "escape_name" do
    test "escapes _, #, $, %, &, {, } in constant names" do
      c = Declaration.new_const("a_b#c$d%e&f{g}", Type.new(:i))

      assert LF.format!(c, hide_types: true) ==
               "\\mathrm{a\\_b\\#c\\$d\\%e\\&f\\{g\\}}"
    end

    test "escapes underscores in free-variable names" do
      v = Declaration.new_free_var("x_1", Type.new(:i))
      assert LF.format!(v, hide_types: true) == "x\\_1"
    end
  end

  ##############################################################################
  # Partial applications of logical constants (η-expanded on construction)
  #
  # A partially-applied `∧` or `¬` gets stored in η-long form, so the outer
  # rendered term is `λ Q. P ∧ Q` rather than `∧ P`. These tests document
  # that η-expansion still round-trips through the LaTeX formatter.
  ##############################################################################

  describe "eta-expanded partial applications of logical connectives" do
    test "∧ applied to a single argument round-trips through the binder merge" do
      import Dsl
      p = var("P", Type.new(:o))
      and_head = Definitions.and_const()
      id = app(const(and_head.name, and_head.type), p)

      # η-long form: λ Q. P ∧ Q  — hits the infix branch of render_spine.
      assert LF.format!(id) == "\\lambda Q_{o}.\\,P_{o} \\wedge Q"
    end

    test "bare ¬ eta-expands to λP. ¬P" do
      neg = Definitions.neg_const()
      id = Dsl.const(neg.name, neg.type)

      assert LF.format!(id) == "\\lambda P_{o}.\\,\\neg P"
    end
  end

  ##############################################################################
  # Bound-variable head in raw index mode
  ##############################################################################

  describe "raw-index bound-var head with arguments" do
    test "\\lambda P. P a renders bound head as \\mathtt{1} in raw mode" do
      # λ P_(ι→o). P a
      pred_type = Type.new(:o, :i)
      a_id = Dsl.const("a", Type.new(:i))
      id = Dsl.lambda(pred_type, fn p -> Dsl.app(p, a_id) end)

      assert LF.format!(id, reconstruct_names: false) ==
               "\\lambda_{\\iota \\to o}.\\,\\mathtt{1}_{\\iota \\to o}~\\mathrm{a}_{\\iota}"
    end
  end

  ##############################################################################
  # Math-mode wrapping across shapes
  ##############################################################################

  describe "math_mode wrapping" do
    test "inline mode on a term" do
      id = Dsl.const("a", Type.new(:i))
      assert LF.format!(id, math_mode: :inline) == "$\\mathrm{a}_{\\iota}$"
    end

    test "display mode on a substitution" do
      fvar = Declaration.new_free_var("X", Type.new(:i))
      term_id = Dsl.const("a", Type.new(:i))
      s = Substitution.new(fvar, term_id)

      assert LF.format!(s, math_mode: :display) ==
               "$$[X_{\\iota} \mapsto \\mathrm{a}_{\\iota}]$$"
    end
  end

  ##############################################################################
  # Problem rendering — non-empty sections
  ##############################################################################

  describe "problem rendering" do
    test "path is preserved verbatim in the header" do
      out = LF.format!(%Problem{path: "foo/bar.p"})
      assert String.starts_with?(out, "% Problem foo/bar.p")
    end

    test "includes section lists comma-separated files" do
      p = %Problem{includes: ["Axioms/A.ax", "Axioms/B.ax"]}
      out = LF.format!(p)
      assert out =~ "% includes: Axioms/A.ax, Axioms/B.ax"
    end

    test "types section renders base types and typed symbols" do
      i = Type.new(:i)

      p = %Problem{
        types: [{"nat", :base_type}, {"succ", Type.new(:i, :i)}]
      }

      out = LF.format!(p)
      assert out =~ "\\mathrm{nat}\\text{ (base)}"
      assert out =~ "\\mathrm{succ} : #{"\\iota \\to \\iota"}"
      _ = i
    end

    test "definitions section aligns each defining equation" do
      i = Type.new(:i)
      decl = Declaration.new_const("c", i)
      term_id = Dsl.const("a", i)

      p = %Problem{definitions: [{decl, term_id}]}
      out = LF.format!(p)

      assert out =~ "\\begin{aligned}"
      assert out =~ "\\mathrm{c}_{\\iota} := \\mathrm{a}_{\\iota}"
      assert out =~ "\\end{aligned}"
    end

    test "axioms section renders each named axiom" do
      p_id = Dsl.var("P", Type.new(:o))
      p = %Problem{axioms: [{"ax1", p_id}]}
      out = LF.format!(p)

      assert out =~ "\\text{ax1}:\\ P_{o}"
    end

    test "conjecture section renders the goal with its name" do
      p_id = Dsl.var("P", Type.new(:o))
      p = %Problem{conjecture: {"goal1", p_id}}
      out = LF.format!(p)

      assert out =~ "\\text{Conjecture goal1}:\\ P_{o}"
    end

    test "format/2 on a Problem returns {:ok, string} even with all sections" do
      i = Type.new(:i)
      decl = Declaration.new_const("c", i)
      c_id = Dsl.const("a", i)
      p_id = Dsl.var("P", Type.new(:o))

      p = %Problem{
        path: "demo.p",
        includes: ["Axioms/A.ax"],
        types: [{"nat", :base_type}],
        definitions: [{decl, c_id}],
        axioms: [{"a1", p_id}],
        conjecture: {"g1", p_id}
      }

      assert {:ok, str} = LF.format(p)
      assert String.starts_with?(str, "% Problem demo.p")
      assert str =~ "\\begin{aligned}"
    end
  end
end
