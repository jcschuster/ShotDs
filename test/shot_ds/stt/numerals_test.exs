defmodule ShotDs.NumeralsTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Stt.Numerals

  test "num/1 encodes zero as lambda s z. z" do
    zero_id = Numerals.num(0)

    assert Numerals.numeral?(zero_id)
    assert church_value(zero_id) == 0
  end

  test "num/1 encodes positive numbers as n-fold successor application" do
    two_id = Numerals.num(2)
    four_id = Numerals.num(4)

    assert Numerals.numeral?(two_id)
    assert Numerals.numeral?(four_id)
    assert church_value(two_id) == 2
    assert church_value(four_id) == 4
  end

  test "num/1 rejects negative numbers" do
    assert_raise RuntimeError, ~r/only defined for natural numbers/, fn ->
      Numerals.num(-1)
    end
  end

  test "numeral?/1 returns false for non-numeral terms" do
    const_id = TF.make_const_term("a", Type.new(:i))

    refute Numerals.numeral?(const_id)
  end

  test "succ/1 preserves numeral encoding and increments value" do
    two_id = Numerals.num(2)
    three_id = Numerals.succ(two_id)

    assert Numerals.numeral?(three_id)
    assert church_value(three_id) == 3
  end

  test "plus/2 preserves numeral encoding and adds values" do
    two_id = Numerals.num(2)
    three_id = Numerals.num(3)

    sum_id = Numerals.plus(two_id, three_id)

    assert Numerals.numeral?(sum_id)
    assert church_value(sum_id) == 5
  end

  test "mult/2 preserves numeral encoding and multiplies values" do
    two_id = Numerals.num(2)
    three_id = Numerals.num(3)

    product_id = Numerals.mult(two_id, three_id)

    assert Numerals.numeral?(product_id)
    assert church_value(product_id) == 6
  end

  defp church_value(term_id) do
    %Term{bvars: [s, z]} = term = TF.get_term(term_id)

    count_apps(%Term{term | bvars: []}, s, z)
  end

  defp count_apps(%Term{bvars: [], head: head, args: []}, _s, z) when head == z, do: 0

  defp count_apps(%Term{bvars: [], head: head, args: [inner_id]}, s, z) when head == s do
    1 + count_apps(TF.get_term(inner_id), s, z)
  end

  defp count_apps(term, _s, _z) do
    flunk("Unexpected Church numeral body shape: #{inspect(term)}")
  end
end
