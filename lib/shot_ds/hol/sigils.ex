defmodule ShotDs.Hol.Sigils do
  @moduledoc ~s"""
  Provides custom [Elixir sigils](`e:elixir:sigils.html`) for inline simple
  type, TH0 formula parsing, TPTP problem file parsing, context parsing and a
  wrapper for handling context.

  > #### Note {: .info}
  >
  > Sigils support 8 different delimiters: `//`, `||`, `""`, `''`, `()`, `[]`,
  > `{}`, `<>`. It is also possible to escape (lowercase) sigils, e.g., for
  > injecting strings.
  """

  alias ShotDs.Parser
  alias ShotDs.Tptp
  alias ShotDs.Data.{Type, Term, Context}

  @doc """
  Handles the `~t` sigil for parsing types in TPTP syntax.

  Returns the parsed `ShotDs.Data.Type` struct. Raises a
  `ShotDs.Parser.ParseError` if the syntax is invalid.

  ## Example:

      iex> ~t"($i>e)>$o"
      %ShotDs.Data.Type{
        goal: :o,
        args: [
          %ShotDs.Data.Type{goal: :e, args: [%ShotDs.Data.Type{goal: :i, args: []}]}
        ]
      }
  """
  @spec sigil_t(String.t(), [char()]) :: Type.t()
  def sigil_t(string, []), do: Parser.parse_type!(string)

  @doc """
  Handles the `~f` sigil for parsing THF formulas. If the term's type is
  polymorphic, instantiates this outer polytype with type o.

  Returns the assigned global or local term ID. Raises a
  `ShotDs.Parser.ParseError` if the syntax is invalid.

  ## Example:

      iex> ~f<P @ X> |> ShotDs.Util.Formatter.format!(false)
      "(P_T[XRRVQ]>o X_T[XRRVQ])_o"
  """
  @spec sigil_f(String.t(), [char()]) :: Term.term_id()
  def sigil_f(string, []) do
    ctx = Process.get(:hol_context) || Context.new()
    Parser.parse!(string, force_o: true, ctx: ctx)
  end

  @doc """
  Handles the `~g` sigil for parsing THF formulas. Keeps outer type variables
  polymorphic.

  Returns the assigned global or local term ID. Raises a
  `ShotDs.Parser.ParseError` if the syntax is invalid.

  ## Example:

      iex> ~g<P @ X> |> ShotDs.Util.Formatter.format!(false)
      "(P_T[201F47]>T[1XMEC7] X_T[201F47])_T[1XMEC7]"
  """
  @spec sigil_g(String.t(), [char()]) :: Term.term_id()
  def sigil_g(string, []) do
    ctx = Process.get(:hol_context) || Context.new()
    Parser.parse!(string, ctx: ctx)
  end

  @doc ~S'''
  Handles the `~p` sigil for parsing TPTP strings describing a TPTP proof
  problem with `thf(...)` components.

  Returns a `ShotDs.Data.Problem` struct describing the proof problem, raising
  on errors.

  ## Example:

  ```elixir
  iex> ~p"""
  ...> thf(my_conj,conjecture,
  ...>     $false => $true).
  ...> """
  ```
  '''
  def sigil_p(string, []), do: Tptp.parse_tptp_string!(string)

  @doc """
  Handles the `~e` sigil for parsing type environment (context).

  Returns a `ShotDs.Data.Context` struct, raising on errors. Constants are
  stored as type schemes (see `ShotDs.Data.TypeScheme`); a bare monotype
  declaration like `p: $i>$o` is recorded as a trivial scheme with no quantified
  variables.

  ## Example:

      iex> ~e[X : $i, p: $i>$o]
      %ShotDs.Data.Context{
        vars: %{"X" => %ShotDs.Data.Type{goal: :i, args: []}},
        consts: %{
          "p" => %ShotDs.Data.TypeScheme{
            body: %ShotDs.Data.Type{
              goal: :o,
              args: [%ShotDs.Data.Type{goal: :i, args: []}]
            },
            vars: []
          }
        }
      }
  """
  def sigil_e(string, []), do: Parser.parse_context!(string)

  @doc """
  Provides a wrapper for parsing to consider some type environment.

  ## Example:

      iex> term_id = with_context(~e[p: $i>$o], fn -> ~f(p @ X) end)
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
