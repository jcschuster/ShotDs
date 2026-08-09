defmodule ShotDs.Stt.SemanticsTest do
  use ShotDs.TermFactoryCase
  alias ShotDs.Data.{Type, Declaration}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Stt.Semantics

  @i %Type{goal: :i, args: []}

  describe "Shift Engine" do
    test "shifts outer bound variables transparently through binders" do
      # Create an outer bound variable (e.g., De Bruijn index 2)
      outer_bv = Declaration.new_bound_var(2, @i)
      body_id = TF.make_term(outer_bv)

      # Wrap it in a dummy lambda
      dummy_fv = Declaration.new_free_var("dummy", @i)
      lambda_id = TF.make_abstr_term(body_id, dummy_fv) |> ok!()

      # Shift by +1 above cutoff 0
      {shifted_id, _} = Semantics.shift!(lambda_id, 1, 0)

      term = TF.get_term!(shifted_id)
      # Because ShotDs evaluates head at the parent environment,
      # it correctly recognizes 2 > 0 and shifts it to 3!
      assert term.head.name == 3
    end
  end

  describe "Substitution & Beta Reduction" do
    test "safely substitutes and beta-reduces simple applications" do
      # 1. Build identity: λx. x
      bv_decl = Declaration.new_bound_var(1, @i)
      identity_id = TF.make_abstr_term(TF.make_term(bv_decl), bv_decl) |> ok!()

      # 2. Build argument: A
      a_decl = Declaration.new_free_var("A", @i)
      a_id = TF.make_term(a_decl)

      # 3. Apply (λx. x) A
      app_id = TF.make_appl_term(identity_id, a_id) |> ok!()

      # make_appl_term naturally calls Semantics.instantiate
      result_term = TF.get_term!(app_id)

      # The result should perfectly reduce to 'A'
      assert result_term.head == a_decl
      assert result_term.args == []
      assert result_term.bvars == []
    end

    test "drops free variables that the replacement discards" do
      io = %Type{goal: :o, args: [@i]}

      # F Y, where F is replaced by the constant function λx. p c
      f_decl = Declaration.new_free_var("F", io)
      target_id = TF.make_appl_term(TF.make_term(f_decl), TF.make_free_var_term("Y", @i)) |> ok!()

      body_id =
        TF.make_appl_term(TF.make_const_term("p", io), TF.make_const_term("c", @i)) |> ok!()

      replacement_id = TF.make_abstr_term(body_id, Declaration.fresh_var(@i)) |> ok!()

      result_id =
        Semantics.subst!(%Substitution{fvar: f_decl, term_id: replacement_id}, target_id)

      # Y is gone along with the discarded argument, so the result is shared
      # with the identically shaped term built directly.
      assert TF.get_term!(result_id).fvars == MapSet.new()
      assert result_id == body_id
    end
  end
end
