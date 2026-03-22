defmodule ShotDs.Stt.SemanticsTest do
  use ExUnit.Case, async: false
  alias ShotDs.Data.{Type, Declaration}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Stt.Semantics

  @i %Type{goal: :i, args: []}

  setup_all do
    if :ets.info(:term_pool) == :undefined do
      :ets.new(:term_pool, [:set, :public, :named_table])
      :ets.insert(:term_pool, {:id_counter, 0})
    end

    :ok
  end

  describe "Shift Engine" do
    test "shifts outer bound variables transparently through binders" do
      # Create an outer bound variable (e.g., De Bruijn index 2)
      outer_bv = Declaration.new_bound_var(2, @i)
      body_id = TF.make_term(outer_bv)

      # Wrap it in a dummy lambda
      dummy_fv = Declaration.new_free_var("dummy", @i)
      lambda_id = TF.make_abstr_term(body_id, dummy_fv)

      # Shift by +1 above cutoff 0
      {shifted_id, _} = Semantics.shift(lambda_id, 1, 0)

      term = TF.get_term(shifted_id)
      # Because ShotDs evaluates head at the parent environment,
      # it correctly recognizes 2 > 0 and shifts it to 3!
      assert term.head.name == 3
    end
  end

  describe "Substitution & Beta Reduction" do
    test "safely substitutes and beta-reduces simple applications" do
      # 1. Build identity: λx. x
      bv_decl = Declaration.new_bound_var(1, @i)
      identity_id = TF.make_abstr_term(TF.make_term(bv_decl), bv_decl)

      # 2. Build argument: A
      a_decl = Declaration.new_free_var("A", @i)
      a_id = TF.make_term(a_decl)

      # 3. Apply (λx. x) A
      app_id = TF.make_appl_term(identity_id, a_id)

      # make_appl_term naturally calls Semantics.instantiate
      result_term = TF.get_term(app_id)

      # The result should perfectly reduce to 'A'
      assert result_term.head == a_decl
      assert result_term.args == []
      assert result_term.bvars == []
    end
  end
end
