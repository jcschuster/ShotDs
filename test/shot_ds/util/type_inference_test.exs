defmodule ShotDs.Util.TypeInferenceTest do
  use ExUnit.Case, async: true

  alias ShotDs.Data.Type
  alias ShotDs.Util.TypeInference, as: TI

  test "apply_subst/2 resolves chained references transitively" do
    r1 = make_ref()
    r2 = make_ref()

    subst = %{r1 => r2, r2 => :i}
    type = Type.new(:o, [Type.new(r1), Type.new(r2)])

    assert TI.apply_subst(type, subst) == Type.new(:o, [:i, :i])
  end

  test "apply_subst/2 handles deeply nested types" do
    r = make_ref()
    nested = Type.new(:o, [Type.new(r, :i), Type.new(r)])

    subst = %{r => :i}
    result = TI.apply_subst(nested, subst)

    assert result == Type.new(:o, [Type.new(:i, :i), Type.new(:i)])
  end

  test "apply_subst/2 with cyclic reference structure" do
    r1 = make_ref()
    r2 = make_ref()

    # Create a substitution chain: r1 -> r2 -> :i
    subst = %{r1 => Type.new(r2), r2 => Type.new(:i)}

    result = TI.apply_subst(Type.new(r1), subst)
    assert result == Type.new(:i)
  end

  test "apply_subst/2 with no matching substitutions" do
    result = TI.apply_subst(Type.new(:o), %{})

    assert result == Type.new(:o)
  end
end
