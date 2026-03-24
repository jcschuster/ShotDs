defmodule ShotDs.Stt.TermFactoryTest do
  use ExUnit.Case, async: false
  alias ShotDs.Data.{Type, Declaration, Term}
  alias ShotDs.Stt.TermFactory, as: TF
  import ShotDs.Hol.Dsl

  @i %Type{goal: :i, args: []}
  @i_to_i %Type{goal: :i, args: [@i]}

  setup_all do
    # Ensure the ETS table is started for isolated test environments
    if :ets.info(:term_pool) == :undefined do
      :ets.new(:term_pool, [:set, :public, :named_table])
      :ets.insert(:term_pool, {:id_counter, 0})
    end

    :ok
  end

  describe "with_local_cleanup/1" do
    test "deletes unreferenced intermediate terms while keeping the final DAG" do
      safe_type = Type.new(:o)
      pre_existing_id = TF.make_fresh_var_term(safe_type)

      parent = self()

      final_id =
        TF.with_local_cleanup(fn ->
          garbage_id = TF.make_fresh_var_term(Type.new(:i))
          send(parent, {:garbage_id, garbage_id})

          kept_id = TF.make_fresh_var_term(Type.new(:i))
          kept_id
        end)

      assert_receive {:garbage_id, garbage_id}

      assert %Term{} = TF.get_term(pre_existing_id)
      assert %Term{} = TF.get_term(final_id)

      assert_raise RuntimeError,
                   "Terms should only be constructed via the TermFactory module, not via struct initialization!",
                   fn ->
                     TF.get_term(garbage_id)
                   end

      assert [] = :ets.match_object(:term_pool, {garbage_id, :_})
    end
  end

  describe "Term Construction and Memoization" do
    test "memoizes basic terms properly" do
      decl = Declaration.new_free_var("X", @i)
      id1 = TF.make_term(decl)
      id2 = TF.make_term(decl)

      # IDs should be strictly identical due to hash-consing
      assert id1 == id2

      term = TF.get_term(id1)
      assert term.head == decl
      assert term.type == @i
      assert term.fvars == [decl]
    end

    test "automatically eta-expands function types" do
      decl = Declaration.new_free_var("F", @i_to_i)
      id = TF.make_term(decl)
      term = TF.get_term(id)

      # Should be wrapped in 1 binder: λv1. F(v1)
      assert length(term.bvars) == 1
      assert term.type == @i_to_i

      # The internal head should be the free variable F
      assert term.head == decl

      # It should be applied to 1 argument (the bound variable)
      assert length(term.args) == 1
      arg_term = TF.get_term(hd(term.args))
      assert arg_term.head.kind == :bv
      # De Bruijn index 1
      assert arg_term.head.name == 1
    end
  end

  describe "Application Gatekeeper" do
    test "safely applies matching types" do
      f_decl = Declaration.new_free_var("F", @i_to_i)
      x_decl = Declaration.new_free_var("X", @i)

      f_id = TF.make_term(f_decl)
      x_id = TF.make_term(x_decl)

      # Applying F (i -> i) to X (i) should return a term of type (i)
      app_id = TF.make_appl_term(f_id, x_id)
      app_term = TF.get_term(app_id)

      assert app_term.type == @i
    end

    test "violently rejects invalid applications (Type Check)" do
      x_decl = Declaration.new_free_var("X", @i)
      y_decl = Declaration.new_free_var("Y", @i)

      x_id = TF.make_term(x_decl)
      y_id = TF.make_term(y_decl)

      # X has type :i (expects 0 args). Applying Y should trigger a MatchError
      assert_raise MatchError, fn ->
        TF.make_appl_term(x_id, y_id)
      end
    end
  end
end
