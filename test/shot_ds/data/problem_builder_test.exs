defmodule ShotDs.Data.ProblemBuilderTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Data.{Problem, TypeScheme}
  alias ShotDs.Hol.Dsl
  alias ShotDs.Tptp
  alias ShotDs.Parser

  import ShotDs.Hol.Definitions
  import Dsl, only: [&&&: 2]

  describe "Problem.new/1 with monomorphic terms" do
    test "returns an empty problem when no axioms or conjecture are given" do
      assert {:ok, problem} = Problem.new()
      assert problem.axioms == []
      assert problem.conjecture == nil
      assert problem.types == %{}
      assert problem.path == "memory"
    end

    test "populates types from constants in a single axiom" do
      a = TF.make_const_term("a", type_i())
      p = TF.make_const_term("p", Type.new(:o, :i))
      ax = Dsl.app(p, a)

      assert {:ok, problem} = Problem.new(axioms: [{"ax1", ax}])
      assert problem.axioms == [{"ax1", ax}]

      %TypeScheme{vars: [], body: a_body} = problem.types["a"]
      assert a_body == Type.new(:i)

      %TypeScheme{vars: [], body: p_body} = problem.types["p"]
      assert p_body == Type.new(:o, :i)
    end

    test "populates types from constants in the conjecture" do
      c = TF.make_const_term("c", type_o())

      assert {:ok, problem} = Problem.new(conjecture: {"goal", c})
      assert problem.conjecture == {"goal", c}
      assert %TypeScheme{body: %Type{goal: :o}} = problem.types["c"]
    end

    test "user-defined base type atoms are registered as :base_type" do
      alpha = Type.new(:alpha)
      p = TF.make_const_term("p", Type.new(:o, alpha))
      x = TF.make_free_var_term("X", alpha)
      ax = Dsl.app(p, x)

      assert {:ok, problem} = Problem.new(axioms: [{"ax", ax}])
      assert problem.types["alpha"] == :base_type
      assert %TypeScheme{body: %Type{goal: :o, args: [%Type{goal: :alpha}]}} = problem.types["p"]
    end

    test "ignores :o, :i and :tType — they are not user-defined base types" do
      a = TF.make_const_term("a", type_i())
      assert {:ok, problem} = Problem.new(axioms: [{"ax", a}])
      refute Map.has_key?(problem.types, "i")
      refute Map.has_key?(problem.types, "o")
    end
  end

  describe "Problem.new/1 with polymorphism" do
    test "generalizes a constant used with an unbound type variable in one axiom" do
      alpha = Type.fresh_type_var()
      p = TF.make_const_term("p", Type.new(:o, alpha))
      x = TF.make_free_var_term("X", alpha)
      ax = Dsl.app(p, x)

      assert {:ok, problem} = Problem.new(axioms: [{"ax", ax}])
      scheme = problem.types["p"]
      assert %TypeScheme{vars: [_ | _]} = scheme
      assert length(scheme.vars) == 1
    end

    test "reconciles a polymorphic constant used at different types across axioms" do
      alpha1 = Type.fresh_type_var()
      alpha2 = Type.fresh_type_var()
      p1 = TF.make_const_term("p", Type.new(:o, alpha1))
      p2 = TF.make_const_term("p", Type.new(:o, alpha2))
      x1 = TF.make_free_var_term("X", alpha1)
      x2 = TF.make_free_var_term("Y", alpha2)
      ax1 = Dsl.app(p1, x1)
      ax2 = Dsl.app(p2, x2)

      assert {:ok, problem} = Problem.new(axioms: [{"ax1", ax1}, {"ax2", ax2}])
      scheme = problem.types["p"]
      # After anti-unification the scheme should be ∀α. o(α)
      assert %TypeScheme{vars: [_], body: %Type{goal: :o, args: [%Type{args: []}]}} = scheme
    end

    test "reconciles concrete-vs-variable to a polymorphic scheme" do
      alpha = Type.fresh_type_var()
      # p @ (some_i_val) in one axiom, p @ X (X: α) in another
      p_alpha = TF.make_const_term("p", Type.new(:o, alpha))
      p_int = TF.make_const_term("p", Type.new(:o, :i))
      i_val = TF.make_const_term("a", type_i())
      x = TF.make_free_var_term("X", alpha)
      ax1 = Dsl.app(p_alpha, x)
      ax2 = Dsl.app(p_int, i_val)

      assert {:ok, problem} = Problem.new(axioms: [{"ax1", ax1}, {"ax2", ax2}])
      scheme = problem.types["p"]
      # anti-unify(α > o, i > o) = γ > o
      assert %TypeScheme{vars: [_], body: %Type{goal: :o, args: [%Type{args: []}]}} = scheme
    end
  end

  describe "Problem.new/1 with unnamed entries" do
    test "auto-names bare axiom term_ids as axiom_<n>" do
      a = TF.make_const_term("a", type_o())
      b = TF.make_const_term("b", type_o())

      assert {:ok, problem} = Problem.new(axioms: [a, {"named", b}, a])
      assert Enum.map(problem.axioms, &elem(&1, 0)) == ["axiom_1", "named", "axiom_3"]
      assert Enum.map(problem.axioms, &elem(&1, 1)) == [a, b, a]
    end

    test "auto-names a bare conjecture term_id" do
      c = TF.make_const_term("c", type_o())
      assert {:ok, problem} = Problem.new(conjecture: c)
      assert problem.conjecture == {"conjecture", c}
    end
  end

  describe "Problem.new/1 error handling" do
    test "rejects invalid axiom entries" do
      assert {:error, msg} = Problem.new(axioms: [:bogus])
      assert msg =~ "Invalid axiom entry"
    end

    test "rejects invalid conjecture entries" do
      assert {:error, msg} = Problem.new(conjecture: "not a term")
      assert msg =~ "Invalid :conjecture"
    end

    test "reports lookup failure for unknown term ids" do
      assert {:error, msg} = Problem.new(axioms: [{"ax", 99_999_999}])
      assert msg =~ "lookup failed"
    end
  end

  describe "Problem.new!/1" do
    test "raises on invalid input" do
      assert_raise ArgumentError, fn -> Problem.new!(axioms: [:bogus]) end
    end

    test "returns a problem on success" do
      a = TF.make_const_term("a", type_o())
      assert %Problem{} = Problem.new!(axioms: [{"ax", a}])
    end
  end

  describe "Tptp.unparse_problem/1 on API-built problems" do
    test "produces a THF document with type, axiom and conjecture sections" do
      a = TF.make_const_term("a", type_i())
      p = TF.make_const_term("p", Type.new(:o, :i))
      ax = Dsl.app(p, a)
      goal = Dsl.app(p, a)

      problem = Problem.new!(axioms: [{"ax1", ax}], conjecture: {"cj", goal})

      assert {:ok, out} = Tptp.unparse_problem(problem)
      assert out =~ "thf(a, type,\n    a: $i)."
      assert out =~ "thf(p, type,\n    p: $i > $o)."
      assert out =~ "thf(ax1, axiom,"
      assert out =~ "thf(cj, conjecture,"
    end

    test "declares user-defined base types" do
      alpha = Type.new(:alpha)
      c = TF.make_const_term("c", alpha)
      goal = TF.make_free_var_term("X", type_o())

      problem = Problem.new!(axioms: [{"ax", c}], conjecture: {"cj", goal})
      assert {:ok, out} = Tptp.unparse_problem(problem)
      assert out =~ "thf(alpha, type,\n    alpha: $tType)."
    end

    test "quantifies free variables of a top-level formula" do
      p = TF.make_const_term("p", Type.new(:o, :i))
      x = TF.make_free_var_term("X", type_i())
      ax = Dsl.app(p, x)

      problem = Problem.new!(axioms: [{"ax", ax}])
      assert {:ok, out} = Tptp.unparse_problem(problem)
      assert out =~ "![X: $i]:"
    end

    test "round-trips a monomorphic problem through Tptp.parse_tptp_string/2" do
      a = TF.make_const_term("a", type_i())
      p = TF.make_const_term("p", Type.new(:o, :i))
      ax = Dsl.app(p, a)

      problem = Problem.new!(axioms: [{"ax1", ax}], conjecture: {"cj", ax})
      {:ok, out} = Tptp.unparse_problem(problem)

      assert {:ok, reparsed} = Tptp.parse_tptp_string(out, "roundtrip")
      assert Map.has_key?(reparsed.types, "a")
      assert Map.has_key?(reparsed.types, "p")
      assert length(reparsed.axioms) == 1
      assert {"cj", _} = reparsed.conjecture
    end

    test "renders a polymorphic constant with a !> scheme" do
      alpha = Type.fresh_type_var()
      p = TF.make_const_term("p", Type.new(:o, alpha))
      x = TF.make_free_var_term("X", alpha)
      ax = Dsl.app(p, x)

      problem = Problem.new!(axioms: [{"ax", ax}])
      assert {:ok, out} = Tptp.unparse_problem(problem)
      assert out =~ "!>["
      assert out =~ "$tType"
    end
  end

  describe "Problem.new/1 preserves shared free variables" do
    test "a free variable in a single formula is left alone" do
      p = TF.make_const_term("p", Type.new(:o, :i))
      x = TF.make_free_var_term("X", type_i())
      ax = Dsl.app(p, x)

      problem = Problem.new!(axioms: [{"ax", ax}])
      # No fv_x constant, only p
      assert Map.keys(problem.types) |> Enum.sort() == ["p"]
      # The axiom term still contains X as a free variable.
      %Term{fvars: fvars} = TF.get_term!(elem(hd(problem.axioms), 1))
      assert Enum.any?(fvars, &(&1.name == "X"))
    end

    test "a free variable shared across two axioms is promoted to a constant" do
      p = TF.make_const_term("p", Type.new(:o, :i))
      q = TF.make_const_term("q", Type.new(:o, :i))
      x = TF.make_free_var_term("X", type_i())
      ax1 = Dsl.app(p, x)
      ax2 = Dsl.app(q, x)

      problem = Problem.new!(axioms: [{"a1", ax1}, {"a2", ax2}])

      # X was promoted to fv_x — declared in the types map, no longer an fvar.
      assert Map.has_key?(problem.types, "fv_x")
      assert %TypeScheme{vars: [], body: %Type{goal: :i}} = problem.types["fv_x"]

      for {_name, id} <- problem.axioms do
        %Term{fvars: fvars, consts: consts} = TF.get_term!(id)
        refute Enum.any?(fvars, &(&1.name == "X"))
        assert Enum.any?(consts, &(&1.name == "fv_x"))
      end
    end

    test "a free variable shared between an axiom and the conjecture is promoted" do
      p = TF.make_const_term("p", Type.new(:o, :i))
      q = TF.make_const_term("q", Type.new(:o, :i))
      x = TF.make_free_var_term("X", type_i())
      ax = Dsl.app(p, x)
      goal = Dsl.app(q, x)

      problem = Problem.new!(axioms: [{"a1", ax}], conjecture: {"cj", goal})

      assert Map.has_key?(problem.types, "fv_x")
      %Term{consts: ax_consts} = TF.get_term!(elem(hd(problem.axioms), 1))
      %Term{consts: cj_consts} = TF.get_term!(elem(problem.conjecture, 1))
      assert Enum.any?(ax_consts, &(&1.name == "fv_x"))
      assert Enum.any?(cj_consts, &(&1.name == "fv_x"))
    end

    test "isolated and shared free variables are handled independently" do
      p = TF.make_const_term("p", Type.new(:o, :i))
      q = TF.make_const_term("q", Type.new(:o, :i))
      x = TF.make_free_var_term("X", type_i())
      y = TF.make_free_var_term("Y", type_i())
      # X is shared between a1 and a2; Y appears only in a1.
      ax1 = Dsl.app(p, x) &&& Dsl.app(q, y)
      ax2 = Dsl.app(q, x)

      problem = Problem.new!(axioms: [{"a1", ax1}, {"a2", ax2}])

      # X was promoted; Y was not.
      assert Map.has_key?(problem.types, "fv_x")
      refute Map.has_key?(problem.types, "fv_y")

      %Term{fvars: a1_fvars, consts: a1_consts} = TF.get_term!(elem(hd(problem.axioms), 1))
      assert Enum.any?(a1_fvars, &(&1.name == "Y"))
      assert Enum.any?(a1_consts, &(&1.name == "fv_x"))
    end

    test "promoted-constant naming avoids clashes with existing constants" do
      # A user already has a constant named "fv_x" of a different type.
      fv_x_const = TF.make_const_term("fv_x", type_o())
      p = TF.make_const_term("p", Type.new(:o, :i))
      x = TF.make_free_var_term("X", type_i())
      ax1 = fv_x_const &&& Dsl.app(p, x)
      ax2 = Dsl.app(p, x)

      problem = Problem.new!(axioms: [{"a1", ax1}, {"a2", ax2}])

      # The pre-existing "fv_x" is untouched; the promotion picks "fv_x_1".
      assert Map.has_key?(problem.types, "fv_x")
      assert Map.has_key?(problem.types, "fv_x_1")
      assert %TypeScheme{body: %Type{goal: :o}} = problem.types["fv_x"]
      assert %TypeScheme{body: %Type{goal: :i}} = problem.types["fv_x_1"]
    end

    test "shared-fvar unparse output stays coherent across formulas" do
      p = TF.make_const_term("p", Type.new(:o, :i))
      q = TF.make_const_term("q", Type.new(:o, :i))
      x = TF.make_free_var_term("X", type_i())
      ax = Dsl.app(p, x)
      goal = Dsl.app(q, x)

      problem = Problem.new!(axioms: [{"a1", ax}], conjecture: {"cj", goal})
      assert {:ok, out} = Tptp.unparse_problem(problem)

      # A single constant declaration + both formulas mention `fv_x` verbatim.
      assert out =~ "thf(fv_x, type,\n    fv_x: $i)."
      assert out =~ "p @ fv_x"
      assert out =~ "q @ fv_x"
      # No auto-∀ around the shared variable.
      refute out =~ "![fv_x"
      refute out =~ "![X:"
    end

    test "isolated free variable is still auto-quantified" do
      p = TF.make_const_term("p", Type.new(:o, :i))
      x = TF.make_free_var_term("X", type_i())
      ax = Dsl.app(p, x)

      problem = Problem.new!(axioms: [{"ax", ax}])
      assert {:ok, out} = Tptp.unparse_problem(problem)
      assert out =~ "![X: $i]:"
    end
  end

  describe "Problem.new/1 with reference-named variables and constants" do
    test "an isolated reference-named free variable is preserved (not promoted)" do
      p = TF.make_const_term("p", Type.new(:o, :i))
      x = TF.make_fresh_var_term(type_i())
      ax = Dsl.app(p, x)

      problem = Problem.new!(axioms: [{"ax", ax}])
      # No promoted constant appears — only `p`.
      assert Map.keys(problem.types) |> Enum.sort() == ["p"]

      # Unparsing must not crash on a reference name and must produce a valid
      # TPTP variable identifier `V…` for the binder and body occurrence.
      assert {:ok, out} = Tptp.unparse_problem(problem)
      assert out =~ ~r/!\[V[A-Za-z0-9]+: \$i\]:/
    end

    test "a reference-named free variable shared across formulas is promoted to fv_r…" do
      p = TF.make_const_term("p", Type.new(:o, :i))
      q = TF.make_const_term("q", Type.new(:o, :i))
      x = TF.make_fresh_var_term(type_i())
      ax1 = Dsl.app(p, x)
      ax2 = Dsl.app(q, x)

      problem = Problem.new!(axioms: [{"a1", ax1}, {"a2", ax2}])

      promoted_names =
        problem.types
        |> Map.keys()
        |> Enum.filter(&String.starts_with?(&1, "fv_r"))

      assert length(promoted_names) == 1

      # Same promoted constant appears in both axiom terms.
      %Term{consts: c1} = TF.get_term!(elem(hd(problem.axioms), 1))
      %Term{consts: c2} = TF.get_term!(elem(hd(tl(problem.axioms)), 1))
      names1 = c1 |> MapSet.to_list() |> Enum.map(& &1.name)
      names2 = c2 |> MapSet.to_list() |> Enum.map(& &1.name)
      assert Enum.any?(names1, &String.starts_with?(&1, "fv_r"))
      assert Enum.any?(names2, &String.starts_with?(&1, "fv_r"))

      # Output must not try to render the raw reference as text.
      assert {:ok, out} = Tptp.unparse_problem(problem)
      assert out =~ ~r/thf\(fv_r[A-Za-z0-9]+, type,\s*fv_r[A-Za-z0-9]+: \$i\)\./
    end

    test "a reference-named constant is registered under its hashed key" do
      c_id = TF.make_fresh_const_term(type_i())
      p = TF.make_const_term("p", Type.new(:o, :i))
      ax = Dsl.app(p, c_id)

      problem = Problem.new!(axioms: [{"ax", ax}])

      # Keys of the types map must all be strings; the ref-named constant is
      # keyed by a "c<hash>" identifier.
      assert Enum.all?(Map.keys(problem.types), &is_binary/1)

      const_key =
        problem.types
        |> Map.keys()
        |> Enum.find(&String.starts_with?(&1, "c"))

      refute is_nil(const_key)

      # And the TPTP output uses the same identifier consistently.
      assert {:ok, out} = Tptp.unparse_problem(problem)
      assert out =~ "thf(#{const_key}, type,\n    #{const_key}: $i)."
      assert out =~ "p @ #{const_key}"
    end

    test "promoted fv_r… name is added to the clash-check set based on name_key" do
      # If a ref-named constant already exists under key "fv_r<hash>", the
      # promotion has to pick a distinct name for a shared ref-named fvar.
      # Constructing that exact collision is hard, so we settle for verifying
      # the more general property: given a shared fv AND a distinct existing
      # constant, both remain in the types map with distinct string keys.
      c_id = TF.make_fresh_const_term(type_i())
      p = TF.make_const_term("p", Type.new(:o, :i))
      x = TF.make_fresh_var_term(type_i())
      ax1 = Dsl.app(p, x) &&& Dsl.app(p, c_id)
      ax2 = Dsl.app(p, x)

      problem = Problem.new!(axioms: [{"a1", ax1}, {"a2", ax2}])

      keys = Map.keys(problem.types)
      assert Enum.count(keys, &String.starts_with?(&1, "fv_r")) == 1
      assert Enum.any?(keys, &String.starts_with?(&1, "c"))
      # No duplicates.
      assert length(keys) == length(Enum.uniq(keys))
    end

    test "TPTP output round-trips a problem with a shared reference-named fvar" do
      p = TF.make_const_term("p", Type.new(:o, :i))
      q = TF.make_const_term("q", Type.new(:o, :i))
      x = TF.make_fresh_var_term(type_i())
      ax = Dsl.app(p, x)
      goal = Dsl.app(q, x)

      problem = Problem.new!(axioms: [{"a1", ax}], conjecture: {"cj", goal})
      {:ok, out} = Tptp.unparse_problem(problem)
      assert {:ok, reparsed} = Tptp.parse_tptp_string(out, "roundtrip")

      promoted_key =
        problem.types |> Map.keys() |> Enum.find(&String.starts_with?(&1, "fv_r"))

      # Same promoted constant is declared and used in the reparsed problem.
      assert Map.has_key?(reparsed.types, promoted_key)
      assert length(reparsed.axioms) == 1
      assert {"cj", _} = reparsed.conjecture
    end
  end

  describe "Parser.unparse_type_scheme/1 through a generalized monotype" do
    test "renders a monotype scheme without the !> prefix" do
      scheme = TypeScheme.generalize(Type.new(:i), MapSet.new())
      assert Parser.unparse_type_scheme(scheme) == "$i"
    end

    test "renders a polymorphic scheme with the !> prefix" do
      alpha = Type.fresh_type_var()
      scheme = TypeScheme.generalize(Type.new(:o, alpha), MapSet.new())
      out = Parser.unparse_type_scheme(scheme)
      assert out =~ "!>["
      assert out =~ "$tType"
      assert out =~ "$o"
    end
  end
end
