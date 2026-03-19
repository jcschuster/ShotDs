defmodule ShotDs.Data.DeclarationContextSubstitutionTest do
  use ExUnit.Case, async: true

  alias ShotDs.Data.{Context, Declaration, Substitution, Term, Type}

  test "declaration constructors create typed free vars, bound vars and constants" do
    i = Type.new(:i)

    fv = Declaration.new_free_var("X", i)
    bv = Declaration.new_bound_var(1, i)
    co = Declaration.new_const("c", i)

    assert fv.kind == :fv
    assert bv.kind == :bv
    assert co.kind == :co
    assert fv.type == i
    assert bv.type == i
    assert co.type == i
  end

  test "fresh constructors produce references and formatted prefixes" do
    i = Type.new(:i)

    fv = Declaration.fresh_var(i)
    co = Declaration.fresh_const(i)

    assert is_reference(fv.name)
    assert is_reference(co.name)
    assert String.starts_with?(Declaration.format(fv), "V[")
    assert String.starts_with?(Declaration.format(co), "C[")
  end

  test "format/2 and String.Chars can hide types" do
    decl = Declaration.new_free_var("X", Type.new(:o))

    assert Declaration.format(decl, false) == "X_o"
    assert Declaration.format(decl, true) == "X"
    assert to_string(decl) == "X"
  end

  test "context stores vars, consts and constraints" do
    i = Type.new(:i)
    o = Type.new(:o)

    ctx =
      Context.new()
      |> Context.put_var("X", i)
      |> Context.put_const("p", Type.new(:o, :i))
      |> Context.add_constraint(i, o)
      |> Context.add_constraint(i, o)

    assert Context.get_type(ctx, "X") == i
    assert Context.get_type(ctx, "p") == Type.new(:o, :i)
    assert MapSet.size(ctx.constraints) == 1
  end

  test "context get_type/2 supports reference names" do
    ref_name = make_ref()
    type = Type.new(:o)

    ctx = Context.new() |> Context.put_var(ref_name, type)

    assert Context.get_type(ctx, ref_name) == type
  end

  test "substitution constructor stores fvar and term id" do
    fvar = Declaration.new_free_var("X", Type.new(:i))
    term_id = Term.dummy_id()

    subst = Substitution.new(fvar, term_id)

    assert subst.fvar == fvar
    assert subst.term_id == term_id
  end
end

