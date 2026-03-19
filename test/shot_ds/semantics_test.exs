defmodule ShotDs.SemanticsTest do
  use ShotDs.TermFactoryCase

  test "subst/2 replaces a free variable with the replacement term" do
    i = Type.new(:i)
    x = Declaration.new_free_var("X", i)
    x_id = TF.make_term(x)
    y_id = TF.make_free_var_term("Y", i)

    subst = Substitution.new(x, y_id)

    assert Semantics.subst(subst, x_id) == y_id
  end

  test "subst/2 applies substitutions left-to-right for lists" do
    i = Type.new(:i)

    x = Declaration.new_free_var("X", i)
    y = Declaration.new_free_var("Y", i)

    x_id = TF.make_term(x)
    y_id = TF.make_term(y)
    c_id = TF.make_const_term("c", i)

    s1 = Substitution.new(x, y_id)
    s2 = Substitution.new(y, c_id)

    assert Semantics.subst([s1, s2], x_id) == c_id
  end

  test "add_subst/3 prepends substitution and rewrites existing entries" do
    i = Type.new(:i)

    x = Declaration.new_free_var("X", i)
    z = Declaration.new_free_var("Z", i)

    x_id = TF.make_term(x)
    c_id = TF.make_const_term("c", i)

    old_substs = [Substitution.new(z, x_id)]
    new_subst = Substitution.new(x, c_id)

    [head | rest] = Semantics.add_subst(old_substs, new_subst)

    assert head == new_subst
    assert Enum.map(rest, & &1.term_id) == [c_id]
  end

  test "add_subst/3 honors tuple-tag blacklist" do
    i = Type.new(:i)

    existing = [Substitution.new(Declaration.new_free_var("A", i), TF.make_const_term("a", i))]

    blocked = %Substitution{
      fvar: %Declaration{kind: :fv, name: {:tmp, :skolem}, type: i},
      term_id: TF.make_const_term("b", i)
    }

    result = Semantics.add_subst(existing, blocked, [:skolem])

    assert result == existing
  end

  test "make_abstr_term/2 binds occurrences of a free variable" do
    i = Type.new(:i)
    x = Declaration.new_free_var("X", i)

    x_id = TF.make_term(x)
    abs_id = Semantics.make_abstr_term(x_id, x)

    assert %Term{bvars: [bv], fvars: [], type: type, head: %Declaration{kind: :bv}} =
             TF.get_term(abs_id)

    assert %Declaration{kind: :bv, type: ^i} = bv
    assert to_string(type) == "i>i"
  end

  test "make_appl_term/2 beta-reduces abstractions" do
    i = Type.new(:i)

    x = Declaration.new_free_var("X", i)
    x_id = TF.make_term(x)
    abs_id = Semantics.make_abstr_term(x_id, x)

    a_id = TF.make_const_term("a", i)

    assert Semantics.make_appl_term(abs_id, a_id) == a_id
  end

  test "make_appl_term/2 raises on type mismatch" do
    f_id = TF.make_const_term("f", Type.new(:o, :i))
    wrong_arg = TF.make_const_term("p", Type.new(:o))

    assert_raise MatchError, fn ->
      Semantics.make_appl_term(f_id, wrong_arg)
    end
  end

  test "fold_apply/2 matches nested make_appl_term/2" do
    i = Type.new(:i)

    f = TF.make_const_term("f", Type.new(:o, [i, i]))
    a = TF.make_const_term("a", i)
    b = TF.make_const_term("b", i)

    folded = Semantics.fold_apply(f, [a, b])
    nested = Semantics.make_appl_term(Semantics.make_appl_term(f, a), b)

    assert folded == nested
    assert %Term{type: %Type{goal: :o, args: []}} = TF.get_term(folded)
  end

  test "shift/4 and instantiate/4 manipulate de Bruijn indices" do
    i = Type.new(:i)

    bv1 = Declaration.new_bound_var(1, i)
    term1 = %Term{id: Term.dummy_id(), head: bv1, type: i, max_num: 1}
    id1 = TF.memoize(term1)

    {shifted_id, _} = Semantics.shift(id1, 2, 0)
    assert %Term{head: %Declaration{kind: :bv, name: 3}, max_num: 3} = TF.get_term(shifted_id)

    replacement = TF.make_const_term("c", i)
    {instantiated_id, _} = Semantics.instantiate(id1, 1, replacement)
    assert instantiated_id == replacement

    bv2 = Declaration.new_bound_var(2, i)
    term2 = %Term{id: Term.dummy_id(), head: bv2, type: i, max_num: 2}
    id2 = TF.memoize(term2)

    {decremented_id, _} = Semantics.instantiate(id2, 1, replacement)
    assert %Term{head: %Declaration{kind: :bv, name: 1}, max_num: 1} = TF.get_term(decremented_id)
  end
end
