defmodule ShotDs.Stt.BooleansTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Data.Type
  alias ShotDs.Stt.Booleans

  test "b_type/0 returns correct type structure" do
    bool_type = Booleans.b_type()

    assert %Type{goal: :i, args: [%Type{goal: :i}, %Type{goal: :i}]} = bool_type
  end

  test "tt/0 creates a valid lambda term for true" do
    tt_id = Booleans.tt()

    assert is_integer(tt_id)
    assert tt_id > 0

    # Verify it's a lambda term with two parameters
    tt_term = term!(tt_id)
    assert tt_term.bvars |> length() == 2
    assert tt_term.type == Booleans.b_type()
  end

  test "ff/0 creates a valid lambda term for false" do
    ff_id = Booleans.ff()

    assert is_integer(ff_id)
    assert ff_id > 0

    # Verify it's a lambda term with two parameters
    ff_term = term!(ff_id)
    assert ff_term.bvars |> length() == 2
    assert ff_term.type == Booleans.b_type()
  end

  test "b_var/1 creates a term with boolean type" do
    bool_var_id = Booleans.b_var("p")

    assert is_integer(bool_var_id)

    bool_var = term!(bool_var_id)
    assert bool_var.type == Booleans.b_type()
  end

  test "b_var/1 accepts both binary and reference names" do
    # Binary name
    var_from_binary = Booleans.b_var("p")
    assert is_integer(var_from_binary)

    # Reference name
    ref = make_ref()
    var_from_ref = Booleans.b_var(ref)
    assert is_integer(var_from_ref)
  end

  test "tt/0 and ff/0 are distinct terms" do
    tt_id = Booleans.tt()
    ff_id = Booleans.ff()

    assert tt_id != ff_id
  end

  test "Church boolean selectors are valid lambda terms" do
    # Both tt and ff should be valid lambda terms that can be used as selectors
    tt_id = Booleans.tt()
    ff_id = Booleans.ff()

    tt = term!(tt_id)
    ff = term!(ff_id)

    # Both should have 2 bvars (parameters for true and false values)
    assert length(tt.bvars) == 2
    assert length(ff.bvars) == 2

    # Both should have boolean type
    assert tt.type == Booleans.b_type()
    assert ff.type == Booleans.b_type()
  end

  test "boolean type is consistent across functions" do
    bool_type = Booleans.b_type()

    tt = term!(Booleans.tt())
    ff = term!(Booleans.ff())
    b_var = term!(Booleans.b_var("x"))

    assert tt.type == bool_type
    assert ff.type == bool_type
    assert b_var.type == bool_type
  end

  test "multiple boolean variables can be created" do
    p_id = Booleans.b_var("p")
    q_id = Booleans.b_var("q")
    r_id = Booleans.b_var("r")

    assert is_integer(p_id)
    assert is_integer(q_id)
    assert is_integer(r_id)

    # All should be distinct
    assert p_id != q_id
    assert q_id != r_id
    assert p_id != r_id
  end

  test "tt and ff return valid integer IDs" do
    # All operations should return integer IDs
    assert is_integer(Booleans.tt())
    assert is_integer(Booleans.ff())
  end

  test "b_var names produce distinct terms" do
    # Same name
    x1 = Booleans.b_var("x")
    x2 = Booleans.b_var("x")

    # Both have boolean type
    assert term!(x1).type == Booleans.b_type()
    assert term!(x2).type == Booleans.b_type()

    # Different names
    y = Booleans.b_var("y")
    assert term!(y).type == Booleans.b_type()
  end
end
