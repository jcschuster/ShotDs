ExUnit.start()

case :ets.whereis(:term_pool) do
  :undefined -> ShotDs.TermFactory.init()
  _ -> :ok
end

defmodule ShotDs.TermFactoryCase do
  use ExUnit.CaseTemplate

  using do
    quote do
      use ExUnit.Case, async: false

      alias ShotDs.Data.{Context, Declaration, Substitution, Term, Type}
      alias ShotDs.Hol.Definitions
      alias ShotDs.Semantics
      alias ShotDs.TermFactory, as: TF
      alias ShotDs.Util.{Builder, Formatter, Lexer, TypeInference}
    end
  end

  setup do
    case :ets.whereis(:term_pool) do
      :undefined -> ShotDs.TermFactory.init()
      _ -> :ok
    end

    :ets.delete_all_objects(:term_pool)
    :ok
  end
end

