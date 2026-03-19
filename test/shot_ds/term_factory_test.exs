defmodule ShotDs.TermFactoryTest do
  use ShotDs.TermFactoryCase

  test "memoize/1 deduplicates equal term signatures" do
    type = Type.new(:o)
    decl = Declaration.new_const("c", type)

    draft = %Term{id: Term.dummy_id(), head: decl, type: type}

    id1 = TF.memoize(draft)
    id2 = TF.memoize(%Term{draft | id: <<1::256>>})

    assert id1 == id2
  end

  test "get_term/1 raises for unknown ids" do
    assert_raise RuntimeError,
                 ~r/Terms should only be constructed via the TermFactory module/,
                 fn ->
                   TF.get_term(<<255::256>>)
                 end
  end

  test "make_free_var_term/2 creates a variable term" do
    id = TF.make_free_var_term("X", Type.new(:i))

    assert %Term{
             head: %Declaration{kind: :fv, name: "X"},
             args: [],
             type: %Type{goal: :i, args: []},
             max_num: 0,
             fvars: [%Declaration{kind: :fv, name: "X"}]
           } = TF.get_term(id)
  end

  test "make_const_term/2 eta-expands higher-order constants" do
    id = TF.make_const_term("f", Type.new(:o, :i))

    assert %Term{type: %Type{goal: :o, args: [%Type{goal: :i}]}, bvars: [bv], args: [arg_id]} =
             TF.get_term(id)

    assert %Declaration{kind: :bv, type: %Type{goal: :i}} = bv

    arg_term = TF.get_term(arg_id)
    assert %Declaration{kind: :bv, type: %Type{goal: :i}} = arg_term.head
  end

  test "make_const_term/2 for base type does not eta-expand" do
    id = TF.make_const_term("a", Type.new(:i))

    assert %Term{bvars: [], args: [], type: %Type{goal: :i}} = TF.get_term(id)
  end
end
