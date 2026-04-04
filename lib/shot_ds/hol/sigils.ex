defmodule ShotDs.Hol.Sigils do
  @moduledoc """
  Provides custom Elixir sigils for inline TH0 formula parsing, TPTP problem
  file parsing, context parsing and a wrapper for handling context.
  """

  alias ShotDs.Parser
  alias ShotDs.Tptp
  alias ShotDs.Data.{Term, Context}

  @doc """
  Handles the `~f` sigil for parsing TH0 formulas.

  Returns the assigned global or local term ID. Raises a
  `ShotDs.Parser.ParseError` if the syntax is invalid.
  """
  @spec sigil_f(String.t(), [char()]) :: Term.term_id()
  def sigil_f(string, []) do
    ctx = Process.get(:hol_context) || Context.new()
    Parser.parse!(string, ctx)
  end

  @doc """
  Handles the `~p` sigil for parsing TPTP strings describing a TPTP proof
  problem with `thf(...)` components.

  Returns a `ShotDs.Data.Problem` struct describing the proof problem, raising
  on errors.
  """
  def sigil_p(string, []), do: Tptp.parse_tptp_string!(string)

  @doc """
  Handles the `~e` sigil for parsing type environment (context).

  Returns a `ShotDs.Data.Context` struct, raising on errors.
  """
  def sigil_e(string, []), do: Parser.parse_context!(string)

  @doc """
  Provides a wrapper for the `~f` sigil to consider some type environment.
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
