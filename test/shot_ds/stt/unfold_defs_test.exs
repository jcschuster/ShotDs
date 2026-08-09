defmodule ShotDs.Stt.UnfoldDefsTest do
  use ShotDs.TermFactoryCase
  import ShotDs.Hol.Dsl

  @i %Type{goal: :i, args: []}
  @io %Type{goal: :o, args: [@i]}
  @ii %Type{goal: :i, args: [@i]}
  @iio %Type{goal: :o, args: [@i, @i]}

  # λx λy. ∀p. p x ⊃ p y, declared as `leibniz : α → α → o`
  defp leibniz_defs do
    alpha = Type.fresh_type_var()
    decl = Declaration.new_const("leibniz", Type.new(:o, [alpha, alpha]))

    body =
      lambda([alpha, alpha], fn x, y ->
        forall(Type.new(:o, alpha), fn p -> app(p, x) ~> app(p, y) end)
      end)

    {decl, %{decl => body}}
  end

  defp leibniz_at(type, left, right) do
    forall(Type.new(:o, type), fn p -> app(p, left) ~> app(p, right) end)
  end

  describe "unfold_defs/2" do
    test "returns the target unchanged when there is nothing to unfold" do
      target = app(const("p", @io), var("a", @i))

      assert Semantics.unfold_defs(target, %{}) == {:ok, target}
    end

    test "unfolds a monomorphic definition" do
      decl = Declaration.new_const("nonempty", Type.new(:o, [@io]))
      body = lambda(@io, fn s -> exists(@i, fn x -> app(s, x) end) end)

      target = app(const("nonempty", Type.new(:o, [@io])), const("p", @io))
      expected = exists(@i, fn x -> app(const("p", @io), x) end)

      assert Semantics.unfold_defs!(target, %{decl => body}) == expected
    end

    test "unfolds occurrences underneath binders" do
      decl = Declaration.new_const("refl", Type.new(:o, [@i]))
      body = lambda(@i, fn x -> app(const("r", @iio), [x, x]) end)

      target = forall(@i, fn y -> app(const("refl", Type.new(:o, [@i])), y) end)
      expected = forall(@i, fn y -> app(const("r", @iio), [y, y]) end)

      assert Semantics.unfold_defs!(target, %{decl => body}) == expected
    end

    test "unfolds chained definitions to a fixpoint" do
      outer = Declaration.new_const("c1", Type.new(:o, [@i]))
      outer_body = lambda(@i, fn x -> app(const("c2", Type.new(:o, [@i])), x) end)

      inner = Declaration.new_const("c2", Type.new(:o, [@i]))
      inner_body = lambda(@i, fn x -> app(const("p", @io), x) end)

      target = app(const("c1", Type.new(:o, [@i])), var("a", @i))
      expected = app(const("p", @io), var("a", @i))

      assert Semantics.unfold_defs!(target, %{outer => outer_body, inner => inner_body}) ==
               expected
    end
  end

  describe "unfold_defs/2 with polymorphic declarations" do
    test "instantiates the scheme at a base type" do
      {_decl, defs} = leibniz_defs()

      target = app(const("leibniz", @iio), [var("a", @i), var("b", @i)])

      assert Semantics.unfold_defs!(target, defs) ==
               leibniz_at(@i, var("a", @i), var("b", @i))
    end

    test "instantiates the scheme at a function type, restoring η-long form" do
      {_decl, defs} = leibniz_defs()

      target = app(const("leibniz", Type.new(:o, [@ii, @ii])), [var("f", @ii), var("g", @ii)])

      assert Semantics.unfold_defs!(target, defs) ==
               leibniz_at(@ii, var("f", @ii), var("g", @ii))
    end

    test "instantiates two occurrences at different types independently" do
      {_decl, defs} = leibniz_defs()
      bool = Type.new(:o)

      target =
        app(const("leibniz", @iio), [var("a", @i), var("b", @i)]) &&&
          app(const("leibniz", Type.new(:o, [bool, bool])), [var("P", bool), var("Q", bool)])

      expected =
        leibniz_at(@i, var("a", @i), var("b", @i)) &&&
          leibniz_at(bool, var("P", bool), var("Q", bool))

      assert Semantics.unfold_defs!(target, defs) == expected
    end
  end

  describe "unfold_defs/2 with non-ground occurrence types" do
    test "instantiates the scheme at a rigid type variable" do
      {_decl, defs} = leibniz_defs()
      gamma = Type.fresh_type_var()

      target =
        app(const("leibniz", Type.new(:o, [gamma, gamma])), [var("X", gamma), var("Y", gamma)])

      assert Semantics.unfold_defs!(target, defs) ==
               leibniz_at(gamma, var("X", gamma), var("Y", gamma))
    end

    test "unfolds when the occurrence's type mentions the scheme's own type variable" do
      alpha = Type.fresh_type_var()
      decl = Declaration.new_const("holds", Type.new(:o, [alpha]))
      body = lambda(alpha, fn x -> app(const("p", Type.new(:o, [alpha])), x) end)

      # α → α, built from the very reference the declaration quantifies over
      endo = Type.new(alpha.goal, [alpha])
      target = app(const("holds", Type.new(:o, [endo])), var("F", endo))

      assert Semantics.unfold_defs!(target, %{decl => body}) ==
               app(const("p", Type.new(:o, [endo])), var("F", endo))
    end

    test "reports a mismatch rather than instantiating the scheme inconsistently" do
      {_decl, defs} = leibniz_defs()
      gamma = Type.fresh_type_var()

      # α → α → o cannot be used at γ → ι → o: γ is rigid, so α is over-constrained
      target = app(const("leibniz", Type.new(:o, [gamma, @i])), [var("X", gamma), var("a", @i)])

      assert {:error, "Type Error: Cannot match" <> _} = Semantics.unfold_defs(target, defs)
    end

    test "rejects an occurrence more general than the declaration" do
      beta = Type.fresh_type_var()
      gamma = Type.fresh_type_var()

      decl = Declaration.new_const("some", Type.new(:o, [Type.new(:o, beta)]))
      body = lambda(Type.new(:o, beta), fn s -> app(s, var("w", beta)) end)

      # the declaration wants a predicate, the occurrence supplies a rigid variable
      target = app(const("some", Type.new(:o, [gamma])), var("S", gamma))

      assert {:error, "Type Error: Cannot match" <> _} =
               Semantics.unfold_defs(target, %{decl => body})
    end
  end

  describe "unfold_defs/2 denormalized caches" do
    test "drops free variables that the definition discards" do
      decl = Declaration.new_const("triv", Type.new(:o, [@i]))
      body = lambda(@i, fn _x -> app(const("p", @io), const("c", @i)) end)

      target = app(const("triv", Type.new(:o, [@i])), var("Y", @i))
      result = Semantics.unfold_defs!(target, %{decl => body})

      assert term!(result).fvars == MapSet.new()
      # the exact :fvars set keeps the result shared with the directly built term
      assert result == app(const("p", @io), const("c", @i))
    end

    test "keeps free variables that the definition retains" do
      decl = Declaration.new_const("twice", Type.new(:o, [@i]))
      body = lambda(@i, fn x -> app(const("r", @iio), [x, x]) end)

      target = app(const("twice", Type.new(:o, [@i])), var("Y", @i))
      result = Semantics.unfold_defs!(target, %{decl => body})

      assert term!(result).fvars == MapSet.new([Declaration.new_free_var("Y", @i)])
      assert result == app(const("r", @iio), [var("Y", @i), var("Y", @i)])
    end
  end
end
