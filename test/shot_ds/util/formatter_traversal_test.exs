defmodule ShotDs.Util.FormatterTraversalTest do
  use ShotDs.TermFactoryCase

  alias ShotDs.Parser
  alias ShotDs.Util.TermTraversal

  test "format_term/2 prints connectives with readable symbols" do
    term_id = Parser.parse("$true & ~ $false")

    rendered = Formatter.format_term(term_id)

    assert String.contains?(rendered, "∧")
    assert String.contains?(rendered, "¬")
    assert String.contains?(rendered, "_o")
  end

  test "format_term/2 works for term structs and hide_types" do
    term_id = Parser.parse("$true | $false")
    term = TF.get_term(term_id)

    assert Formatter.format_term(term, false) == Formatter.format_term(term_id, false)
    refute String.contains?(Formatter.format_term(term_id, true), "_")
  end

  test "format_substitution/2 renders replacement slash variable" do
    i = Type.new(:i)
    x = Declaration.new_free_var("X", i)

    _x_id = TF.make_term(x)
    a_id = TF.make_const_term("a", i)
    subst = Substitution.new(x, a_id)

    rendered = Formatter.format_substitution(subst)

    assert String.contains?(rendered, " /")
    assert String.contains?(rendered, "a")
    assert String.contains?(rendered, "X")
  end

  test "short_ref/1 returns compact string" do
    short = Formatter.short_ref(make_ref())

    assert is_binary(short)
    assert byte_size(short) > 0
  end

  test "TermTraversal.map_term/6 supports short-circuiting" do
    term_id = TF.make_const_term("a", Type.new(:i))

    {mapped_id, _cache} =
      TermTraversal.map_term(
        term_id,
        :env,
        fn _term, env -> env end,
        fn _term, _new_args, _env, _cache ->
          flunk("transform should not run when branch is short-circuited")
        end,
        fn _term, _env -> true end
      )

    assert mapped_id == term_id
  end

  test "TermTraversal.map_term/6 caches repeated subterms in DAGs" do
    i = Type.new(:i)

    x_id =
      TF.memoize(%Term{
        id: 0,
        head: Declaration.new_const("x", i),
        type: i
      })

    root_id =
      TF.memoize(%Term{
        id: 0,
        head: Declaration.new_const("f", i),
        args: [x_id, x_id],
        type: i
      })

    Process.put(:transform_calls, 0)

    {_mapped_id, _cache} =
      TermTraversal.map_term(
        root_id,
        :env,
        fn _term, env -> env end,
        fn %Term{} = term, new_args, _env, cache ->
          Process.put(:transform_calls, Process.get(:transform_calls, 0) + 1)
          {TF.memoize(%Term{term | args: new_args}), cache}
        end
      )

    assert Process.get(:transform_calls) == 2

    node_count =
      TermTraversal.fold_term(root_id, fn _term, child_counts -> 1 + Enum.sum(child_counts) end)

    assert node_count == 3
  end
end
