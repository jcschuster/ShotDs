defmodule ShotDs.Hol.Sigils do
  @moduledoc """
  Provides a custom Elixir sigil for inline TH0 formula parsing and a wrapper
  for handling context.
  """

  alias ShotDs.Parser
  alias ShotDs.Data.{Term, Context}

  @doc """
  Handles the `~THF` sigil for parsing TH0 formulas.

  Returns the assigned global or local term ID. Raises a
  `ShotDs.Parser.ParseError` if the syntax is invalid.
  """
  @spec sigil_THF(String.t(), [char()]) :: Term.term_id()
  def sigil_THF(string, []) do
    ctx = Process.get(:hol_context) || Context.new()
    Parser.parse!(string, ctx)
  end

  @doc """
  Provides a wrapper for the `~THF` sigil to consider some type environment.
  """
  @spec with_context(Context.t(), (-> res)) :: res
        when res: any()
  def with_context(ctx, fun) do
    old_ctx = Process.get(:hol_context)
    Process.put(:hol_context, ctx)

    try do
      fun.()
    after
      if old_ctx, do: Process.put(:hol_context, old_ctx), else: Process.delete(:hol_context)
    end
  end
end
