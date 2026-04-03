defmodule ShotDs.Hol.PatternsTest do
  use ShotDs.TermFactoryCase
  use ShotDs.Hol.Patterns

  import ShotDs.Hol.Dsl

  describe "nullary constant patterns" do
    test "truth/0 matches only the truth term" do
      truth_term = Definitions.true_term() |> term!()
      falsity_term = Definitions.false_term() |> term!()

      assert match?(truth(), truth_term)
      refute match?(truth(), falsity_term)
    end

    test "falsity/0 matches only the falsity term" do
      truth_term = Definitions.true_term() |> term!()
      falsity_term = Definitions.false_term() |> term!()

      assert match?(falsity(), falsity_term)
      refute match?(falsity(), truth_term)
    end
  end

  describe "connective patterns" do
    test "negated/1 matches unary negation" do
      p = TF.make_free_var_term("P", Type.new(:o))
      q = TF.make_free_var_term("Q", Type.new(:o))

      neg_term = neg(p) |> term!()
      disj_term = (p ||| q) |> term!()

      assert match?(negated(_), neg_term)
      refute match?(negated(_), disj_term)
    end

    test "disjunction/2 matches binary disjunction" do
      p = TF.make_free_var_term("P", Type.new(:o))
      q = TF.make_free_var_term("Q", Type.new(:o))

      disj_term = (p ||| q) |> term!()
      conj_term = (p &&& q) |> term!()

      assert match?(disjunction(_, _), disj_term)
      refute match?(disjunction(_, _), conj_term)
    end

    test "conjunction/2 matches binary conjunction" do
      p = TF.make_free_var_term("P", Type.new(:o))
      q = TF.make_free_var_term("Q", Type.new(:o))

      disj_term = (p ||| q) |> term!()
      conj_term = (p &&& q) |> term!()

      assert match?(conjunction(_, _), conj_term)
      refute match?(conjunction(_, _), disj_term)
    end

    test "implication/2 matches binary implication" do
      p = TF.make_free_var_term("P", Type.new(:o))
      q = TF.make_free_var_term("Q", Type.new(:o))

      imp_term = p ~> q |> term!()
      eqv_term = p <~> q |> term!()

      assert match?(implication(_, _), imp_term)
      refute match?(implication(_, _), eqv_term)
    end

    test "equivalence/2 matches binary equivalence" do
      p = TF.make_free_var_term("P", Type.new(:o))
      q = TF.make_free_var_term("Q", Type.new(:o))

      imp_term = p ~> q |> term!()
      eqv_term = p <~> q |> term!()

      assert match?(equivalence(_, _), eqv_term)
      refute match?(equivalence(_, _), imp_term)
    end
  end

  describe "equality patterns" do
    test "equality/2 matches polymorphic equality" do
      i = Type.new(:i)
      x = TF.make_free_var_term("X", i)
      y = TF.make_free_var_term("Y", i)

      eq_term = eq(x, y) |> term!()
      neq_term = neq(x, y) |> term!()

      assert match?(equality(_, _), eq_term)
      refute match?(equality(_, _), neq_term)
    end

    test "typed_equality/3 restricts the argument type" do
      i = Type.new(:i)
      o = Type.new(:o)

      x = TF.make_free_var_term("X", i)
      y = TF.make_free_var_term("Y", i)

      eq_term = eq(x, y) |> term!()

      assert match?(typed_equality(_, _, i), eq_term)
      refute match?(typed_equality(_, _, ^o), eq_term)
    end
  end

  describe "quantifier patterns" do
    test "universal_quantification/1 matches forall terms" do
      term =
        forall(Type.new(:i), fn x ->
          eq(x, x)
        end)
        |> term!()

      assert match?(universal_quantification(_), term)
    end

    test "existential_quantification/1 matches exists terms" do
      term =
        exists(Type.new(:i), fn x ->
          eq(x, x)
        end)
        |> term!()

      assert match?(existential_quantification(_), term)
    end
  end
end
