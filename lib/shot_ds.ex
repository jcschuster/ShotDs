defmodule ShotDs do
  @moduledoc """
  This module collects the most important functions from the library. These
  include parsing functions as well as simple term construction.
  """

  alias ShotDs.Data.{Context, Declaration, Problem, Substitution, Term, Type}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Parser
  alias ShotDs.Tptp
  alias ShotDs.Hol.Dsl
  alias ShotDs.Util.Formatter

  @doc """
  Parses a given string representing a formula in TH0 syntax with full type
  inference. Types which can't be inferred are assigned type variables.
  Variables on the outermost level are identified with type o. Returns the
  assigned ID of the created term.

  Delegates the function call to `ShotDs.Parser.parse/1`.

  ## Examples:

      iex> parse("X & a") |> format_term(true)
      "X ∧ a"

      iex> parse("X @ Y") |> format_term()
      "(X_T[OUFDH]>o Y_T[OUFDH])_o"
  """
  @spec parse(String.t()) :: Term.term_id()
  defdelegate parse(formula_str), to: Parser

  @doc """
  Parses a given string representing a formula in TH0 syntax with full type
  inference. Types which can't be inferred are assigned type variables.
  Variables on the outermost level are identified with type o. Returns the
  assigned ID of the created term. The given `ShotDs.Data.Context` struct
  defines a type environment for resolving unknown types.

  Delegates the function call to `ShotDs.Parser.parse/2`.

  ## Example:

      iex> alias ShotDs.Data.Context
      iex> import ShotDs.Hol.Definitions
      iex> ctx = Context.new() |> Context.put_var("X", type_ii()) |> Context.put_var("Y", type_i())
      iex> parse("X @ Y", ctx) |> format_term()
      "(X_i>i Y_i)_i""
  """
  @spec parse(String.t(), Context.t()) :: Term.term_id()
  defdelegate parse(formula_str, context), to: Parser

  @doc """
  Parses a HOL type from TPTP syntax into a `ShotDs.Data.Type` struct.

  Delegates the function call to `ShotDs.Parser.parse_type/1`.

  ## Example:

      iex> parse_type("$i")
      %ShotDs.Data.Type{goal: :i, args: []}
  """
  @spec parse_type(String.t()) :: Type.t()
  defdelegate parse_type(type_str), to: Parser

  @doc """
  Parses a TPTP file in TH0 syntax at the provided path into a
  `ShotDs.Data.Problem` struct. Returns `{:error, reason}` if a problem
  occurred.

  Delegates the function call to `ShotDs.Tptp.parse_tptp_file/1`.
  """
  @spec parse_tptp_file(String.t()) :: {:ok, Problem.t()} | {:error, String.t()}
  defdelegate parse_tptp_file(path), to: Tptp

  @doc """
  Parses a TPTP file in TH0 syntax at the provided path into a
  `ShotDs.Data.Problem` struct. Returns `{:error, reason}` if a problem
  occurred.

  `is_tptp` indicates whether it is a file from the TPTP problem library and
  can be accessed via the environment variable `TPTP_ROOT` pointing to the root
  directory of the TPTP library.

  Delegates the function call to `ShotDs.Tptp.parse_tptp_file/1`.
  """
  @spec parse_tptp_file(String.t(), boolean()) :: {:ok, Problem.t()} | {:error, String.t()}
  defdelegate parse_tptp_file(path, is_tptp), to: Tptp

  @doc """
  Parses a string representing a full problem file in TPTP's TH0 syntax into a
  `ShotDs.Data.Problem` struct.

  Delegates the function call to `ShotDs.Tptp.parse_tptp_string/1`.
  """
  @spec parse_tptp_string(String.t()) :: {:ok, Problem.t()} | {:error, String.t()}
  defdelegate parse_tptp_string(content), to: Tptp

  @doc """
  Basic construction of a free variable with the corresponding name and type
  and returns the ID for its term representation. While unique variables can be
  created by giving an Erlang reference as name, it is recommended to use
  `ShotDs.Stt.TermFactory.make_fresh_var_term/1` instead for that purpose.

  Delegates the function call to `ShotDs.Stt.TermFactory.make_free_var_term/2`.

  ## Example:

      iex> import ShotDs.Hol.Definitions # shorthand type defs etc.
      iex> make_free_var_term("X", type_o())
  """
  @spec make_free_var_term(String.t() | reference(), Type.t()) :: Term.term_id()
  defdelegate make_free_var_term(name, type), to: TF

  @doc """
  Basic construction of a constant with the corresponding name and type and
  returns the ID for its term representation. While unique constants can be
  created by giving an Erlang reference as name, it is recommended to use
  `ShotDs.Stt.TermFactory.make_fresh_const_term/1` instead for that purpose.

  Delegates the function call to `ShotDs.Stt.TermFactory.make_const_term/2`.

  ## Example:

      iex> import ShotDs.Hol.Definitions # shorthand type defs etc.
      iex> make_const_term("f", type_io())
  """
  @spec make_const_term(String.t() | reference(), Type.t()) :: Term.term_id()
  defdelegate make_const_term(name, type), to: TF

  @doc """
  Constructs a lambda abstraction over a list of variable types. Temporary
  fresh free variables will be generated corresponding to the types. Passes the
  generated variable term IDs to the provided `body_fn`. The arity of `body_fn`
  must correspond to the number of given variables.

  Delegates the function call to `ShotDs.Util.Builder.lambda/2`.

  ## Examples:

      iex> lambda(Type.new(:i), fn x -> ... end)

      iex> lambda([Type.new(:o), Type.new(:o), Type.new(:o)], fn x, y, z -> ... end)
  """
  @spec lambda([Type.t()] | Type.t(), (... -> Term.term_id())) :: Term.term_id()
  defdelegate lambda(var_types, body_fn), to: Dsl

  @doc """
  Applies a term to a single argument term or list of argument terms.

  Delegates the function call to `ShotDs.Util.Builder.app/2`.
  """
  @spec app(Term.term_id(), [Term.term_id()] | Term.term_id()) :: Term.term_id()
  defdelegate app(head_id, arg_ids), to: Dsl

  @doc """
  Pretty-prints the given HOL object taking the ETS cache into accout for
  recursively traversing term DAGs. This is implemented for singular types,
  declarations, terms and substitutions.

  Delegates the function call to `ShotDs.Util.Formatter.format/1`.
  """
  @spec format(Type.t() | Declaration.t() | Term.t() | Substitution.t()) :: String.t()
  defdelegate format(hol_object), to: Formatter

  @doc """
  Pretty-prints the given HOL object taking the ETS cache into accout for
  recursively traversing term DAGs. This is implemented for singular types,
  declarations, terms and substitutions. Type annotations can be hidden for
  better readability by setting `true` as second argument.

  Delegates the function call to `ShotDs.Util.Formatter.format/1`.
  """
  @spec format(Type.t() | Declaration.t() | Term.t() | Substitution.t(), boolean()) :: String.t()
  defdelegate format(hol_object, hide_types), to: Formatter
end
