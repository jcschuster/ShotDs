defmodule ShotDs.Util.TypeInferenceAdvancedTest do
  use ExUnit.Case, async: true

  alias ShotDs.Data.Type
  alias ShotDs.Util.TypeInference, as: TI

  test "solve/1 with multiple type variables" do
    r1 = make_ref()
    r2 = make_ref()
    r3 = make_ref()

    constraints = [
      {Type.new(r1), Type.new(:i)},
      {Type.new(r2), Type.new(r1)},
      {Type.new(r3), Type.new(r2)}
    ]

    subst = TI.solve(constraints)

    assert TI.apply_subst(Type.new(r3), subst) == Type.new(:i)
  end

  test "solve/1 with function type constraints" do
    r1 = make_ref()
    r2 = make_ref()

    constraints = [
      {Type.new(r1, [r2]), Type.new(:o, [:i])}
    ]

    subst = TI.solve(constraints)

    # After solving, r1 should resolve to o and r2 should resolve to i
    resolved_r1 = TI.apply_subst(Type.new(r1), subst)
    resolved_r2 = TI.apply_subst(Type.new(r2), subst)

    assert resolved_r1 == Type.new(:o)
    assert resolved_r2 == Type.new(:i)
  end

  test "apply_subst/2 doesn't change concrete types" do
    concrete = Type.new(:o, [:i, :i])
    subst = %{make_ref() => Type.new(:i)}

    assert TI.apply_subst(concrete, subst) == concrete
  end

  test "solve/1 with constraint redundancy" do
    ref = make_ref()

    constraints = [
      {Type.new(ref), Type.new(:i)},
      {Type.new(ref), Type.new(:i)},
      {Type.new(ref), Type.new(:i)}
    ]

    subst = TI.solve(constraints)

    assert TI.apply_subst(Type.new(ref), subst) == Type.new(:i)
  end

  test "solve/1 with mixed concrete and variable constraints" do
    r = make_ref()

    constraints = [
      {Type.new(:o, Type.new(r)), Type.new(:o, Type.new(:i))},
      {Type.new(r), Type.new(:i)}
    ]

    subst = TI.solve(constraints)

    # r should map to :i (the atom, not wrapped)
    assert Map.get(subst, r) == :i
  end

  test "apply_subst/2 with unused substitutions" do
    r_used = make_ref()
    r_unused = make_ref()

    type = Type.new(r_used)
    subst = %{r_used => Type.new(:i), r_unused => Type.new(:o)}

    result = TI.apply_subst(type, subst)

    assert result == Type.new(:i)
  end

  test "solve/1 with identical left and right types" do
    type = Type.new(:o, :i)

    subst = TI.solve([{type, type}])

    assert subst == %{}
  end

  test "apply_subst/2 on raw atoms and references" do
    assert TI.apply_subst(:i, %{}) == :i
    assert TI.apply_subst(:o, %{}) == :o

    ref = make_ref()
    subst = %{ref => :i}

    assert TI.apply_subst(ref, subst) == :i
  end

  test "solve/1 with function type arguments different" do
    r1 = make_ref()
    r2 = make_ref()

    # Two different variables can unify to different types no problem
    subst =
      TI.solve([
        {Type.new(r1), Type.new(:i)},
        {Type.new(r2), Type.new(:o)}
      ])

    assert TI.apply_subst(Type.new(r1), subst) == Type.new(:i)
    assert TI.apply_subst(Type.new(r2), subst) == Type.new(:o)
  end

  test "apply_subst/2 preserves argument order" do
    r = make_ref()
    type = Type.new(:o, [Type.new(r), Type.new(:i), Type.new(r)])
    subst = %{r => Type.new(:o)}

    result = TI.apply_subst(type, subst)

    assert result == Type.new(:o, [Type.new(:o), Type.new(:i), Type.new(:o)])
  end

  test "solve/1 with nested function types" do
    r1 = make_ref()

    # Nested: (r1->i)->o should match (i->i)->o
    constraints = [
      {Type.new(:o, Type.new(r1, :i)), Type.new(:o, Type.new(:i, :i))}
    ]

    subst = TI.solve(constraints)

    assert TI.apply_subst(Type.new(r1), subst) == Type.new(:i)
  end

  test "apply_subst/2 with long substitution chains" do
    r1 = make_ref()
    r2 = make_ref()
    r3 = make_ref()
    r4 = make_ref()

    subst = %{
      r1 => Type.new(r2),
      r2 => Type.new(r3),
      r3 => Type.new(r4),
      r4 => Type.new(:i)
    }

    result = TI.apply_subst(Type.new(r1), subst)

    assert result == Type.new(:i)
  end

  test "solve/1 type variable equality" do
    r1 = make_ref()
    r2 = make_ref()

    # r1 and r2 should unify with the same type
    constraints = [
      {Type.new(r1), Type.new(r2)},
      {Type.new(r2), Type.new(:i)}
    ]

    subst = TI.solve(constraints)

    assert TI.apply_subst(Type.new(r1), subst) == Type.new(:i)
    assert TI.apply_subst(Type.new(r2), subst) == Type.new(:i)
  end

  test "apply_subst/2 is idempotent" do
    r = make_ref()
    type = Type.new(r)
    subst = %{r => Type.new(:i)}

    result1 = TI.apply_subst(type, subst)
    result2 = TI.apply_subst(result1, subst)

    assert result1 == result2
  end

  test "solve/1 wide variety of constraints" do
    refs = Enum.map(1..5, fn _ -> make_ref() end)
    [r1, r2, r3, r4, r5] = refs

    constraints = [
      {Type.new(r1), Type.new(:o)},
      {Type.new(r2, r1), Type.new(:i, :o)},
      {Type.new(r3), Type.new(r2)},
      {Type.new(r4, [r5, r1]), Type.new(:i, [:o, :o])}
    ]

    subst = TI.solve(constraints)

    assert TI.apply_subst(Type.new(r1), subst) == Type.new(:o)
    # r3 should resolve to :i (what r2 resolves to)
    assert TI.apply_subst(Type.new(r3), subst) == Type.new(:i)
  end
end
