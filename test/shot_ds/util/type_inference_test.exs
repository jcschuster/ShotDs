defmodule ShotDs.Util.TypeInferenceTest do
  use ExUnit.Case, async: true

  alias ShotDs.Data.Type
  alias ShotDs.Util.TypeInference, as: TI

  test "solve/1 unifies a fresh variable with a concrete type" do
    tvar = Type.fresh_type_var()

    subst = TI.solve([{tvar, Type.new(:o)}])

    assert TI.apply_subst(tvar, subst) == Type.new(:o)
    assert Map.get(subst, tvar.goal) == :o
  end

  test "solve/1 supports partial application unification" do
    ref = make_ref()
    short = Type.new(ref, :i)
    long = Type.new(:o, [:i, :i])

    subst = TI.solve([{short, long}])

    assert TI.apply_subst(Type.new(ref), subst) == Type.new(:o, :i)
    assert TI.apply_subst(short, subst) == long
  end

  test "apply_subst/2 resolves chained references transitively" do
    r1 = make_ref()
    r2 = make_ref()

    subst = %{r1 => r2, r2 => :i}
    type = Type.new(:o, [Type.new(r1), Type.new(r2)])

    assert TI.apply_subst(type, subst) == Type.new(:o, [:i, :i])
  end

  test "solve/1 raises on incompatible concrete goals" do
    assert_raise RuntimeError, ~r/Cannot unify concrete goals/, fn ->
      TI.solve([{Type.new(:o), Type.new(:i)}])
    end
  end

  test "solve/1 raises on recursive types via occurs check" do
    ref = make_ref()

    assert_raise RuntimeError, ~r/Occurs check/, fn ->
      TI.solve([{Type.new(ref), Type.new(:o, Type.new(ref))}])
    end
  end

  test "solve/1 chains multiple constraints correctly" do
    r1 = make_ref()
    r2 = make_ref()

    constraints = [
      {Type.new(r1), Type.new(:i)},
      {Type.new(r2), Type.new(r1)},
      {Type.new(:o, Type.new(r2)), Type.new(:o, :i)}
    ]

    subst = TI.solve(constraints)

    assert TI.apply_subst(Type.new(r1), subst) == Type.new(:i)
    assert TI.apply_subst(Type.new(r2), subst) == Type.new(:i)
  end

  test "solve/1 handles bidirectional unification" do
    ref = make_ref()

    # ref should unify with :o in both directions
    subst1 = TI.solve([{Type.new(ref), Type.new(:o)}])
    subst2 = TI.solve([{Type.new(:o), Type.new(ref)}])

    assert TI.apply_subst(Type.new(ref), subst1) == Type.new(:o)
    assert TI.apply_subst(Type.new(ref), subst2) == Type.new(:o)
  end

  test "apply_subst/2 handles deeply nested types" do
    r = make_ref()
    nested = Type.new(:o, [Type.new(r, :i), Type.new(r)])

    subst = %{r => :i}
    result = TI.apply_subst(nested, subst)

    assert result == Type.new(:o, [Type.new(:i, :i), Type.new(:i)])
  end

  test "solve/1 handles partial application constraints" do
    ref = make_ref()
    short_type = Type.new(ref, :i)
    long_type = Type.new(:o, [:i, :i])

    subst = TI.solve([{short_type, long_type}])

    # ref should unify to something that, when applied to i, gives o
    resolved = TI.apply_subst(Type.new(ref), subst)
    assert resolved == Type.new(:o, :i)
  end

  test "apply_subst/2 with cyclic reference structure" do
    r1 = make_ref()
    r2 = make_ref()

    # Create a substitution chain: r1 -> r2 -> :i
    subst = %{r1 => Type.new(r2), r2 => Type.new(:i)}

    result = TI.apply_subst(Type.new(r1), subst)
    assert result == Type.new(:i)
  end

  test "solve/1 with empty constraints returns empty substitution" do
    subst = TI.solve([])

    assert subst == %{}
  end

  test "apply_subst/2 with no matching substitutions" do
    result = TI.apply_subst(Type.new(:o), %{})

    assert result == Type.new(:o)
  end

  test "solve/1 respects arity during partial application" do
    ref = make_ref()

    # ref with 1 arg should unify with o with 2 args
    subst = TI.solve([{Type.new(ref, [:i]), Type.new(:o, [:i, :i])}])

    # ref should become o with an extra i argument
    resolved = TI.apply_subst(Type.new(ref), subst)
    assert %Type{goal: :o, args: [_]} = resolved
  end
end
