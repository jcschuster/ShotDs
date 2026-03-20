ExUnit.start()
{:ok, _started_apps} = Application.ensure_all_started(:shot_ds)

defmodule ShotDs.TermFactoryCase do
  use ExUnit.CaseTemplate

  using do
    quote do
      use ExUnit.Case, async: false

      alias ShotDs.Data.{Context, Declaration, Substitution, Term, Type}
      alias ShotDs.Hol.Definitions
      alias ShotDs.Stt.Semantics
      alias ShotDs.Stt.TermFactory, as: TF
      alias ShotDs.Util.{Formatter, Lexer, TypeInference}
    end
  end

  setup do
    if :ets.whereis(:term_pool) == :undefined do
      :ets.new(:term_pool, [
        :set,
        :public,
        :named_table,
        read_concurrency: true,
        write_concurrency: true
      ])
    end

    :ets.delete_all_objects(:term_pool)
    :ets.insert(:term_pool, {:id_counter, 0})
    :ok
  end
end
