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

      assert LF.format!(s) == "[\\mathrm{a}_{\\iota}~/~X_{\\iota}]"
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
  end
end
