defmodule ShotDs.Parser do
  @moduledoc """
  Contains functionality to parse a formula in THF syntax with full type
  inference. The algorithm uses Hindley-Milner rank-1 polymorphism and
  implements algorithm W for type inference. The resulting constraints are
  resolved via Robinson's first-order unification algorithm. A context can be
  specified to clear up unknown types. If terms still have unknown/polymorphic
  type after parsing, it can be specified to unify their type with type o. The
  main entry point is the `parse/2` function.

  The parser follows standard TH0 precedence rules. The binding strength is
  listed below from **strongest (tightest binding)** to **weakest**.

      (Strongest)   @                   [Application]
                    =, !=               [Equality]
                    ~                   [Negation]
                    &, ~&               [Conjunction]
                    |, ~|               [Disjunction]
                    =>, <=, <=>, <~>    [Implication]
      (Weakest)     !, ?, !!, ??,  ^    [Quantors/Binders]

  The TH0 syntax is specified in https://doi.org/10.1007/s10817-017-9407-7 for
  reference.

  Note that the usage of binders requires special care when using parentheses.
  If the body of the term starts with a parenthesis, the range of the binder is
  limited to the next closing parenthesis.

  For example, the following parses as `"![X : $o]: ($false => (X => $true))"`:

      iex> parse "![X : $o]: $false => (X => $true)"

  While this will be parsed as `"(![X : $o]: (f @ X)) | (g @ X)"`:

      iex> parse "![X : $o]: (f @ X) | (g @ X)"

  > #### Note {: .info}
  >
  > There are also custom sigils available for most parsing functions. These are
  > defined in the module `ShotDs.Hol.Sigils`.
  """

  alias ShotDs.Data.{Type, TypeScheme, Declaration, Term, Context}
  alias ShotDs.Hol.Definitions
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.Lexer
  alias ShotDs.Util.TypeInference, as: TI

  defmodule ParseError do
    @moduledoc """
    An exception raised when parsing fails.
    """
    defexception message: "parse error"
  end

  @doc """
  Safely parses a given string representing a formula in TH0 syntax with full
  type inference. Types which can't be inferred are assigned type variables.
  Variables on the outermost level are identified with type o. Returns the
  assigned ID of the created term.

  Returns `{:ok, term_id}` or `{:error, reason}`

  ## Options:

  - `ctx`: a `ShotDs.Data.Context` struct for providing type information
  - `force_o?`: identify type variables on the outermost level type o

  ## Example:

      iex> match?({:ok, _parsed}, parse("X & a"))
      true

      iex> match?({:ok, _parsed}, parse("X &"))
      false
  """
  @spec parse(String.t(), Keyword.t()) :: {:ok, Term.term_id()} | {:error, String.t()}
  def parse(formula_str, opts \\ []) do
    case Lexer.tokenize(formula_str) do
      {:ok, tokens, "", _, _, _} ->
        parse_tokens(tokens, opts) |> decorate_with_line_col(formula_str)

      {:ok, _, unparsed, _, _, _} ->
        {:error, "Lexer stopped early. Unparsed content: #{unparsed}"}
    end
  end

  @doc """
  Parses a given string representing a formula in TH0 syntax with full type
  inference, raising a `ShotDs.Parser.ParseError` if invalid. Types which can't
  be inferred are assigned type variables. Variables on the outermost level are
  identified with type o. Returns the assigned ID of the created term.

  ## Options:

  - `ctx`: a `ShotDs.Data.Context` struct for providing type information
  - `force_o`: identify type variables on the outermost level type o

  ## Example:

      iex> parse!("X & a") |> format_term!()
      "X ∧ a"

      iex> parse!("X @ Y", force_o: true) |> format_term!(_hide_types = false)
      "(X_T[OUFDH]>o Y_T[OUFDH])_o"

      iex> parse!("X @ Y", ctx: ~e(X:$i>$i, Y:$i)) |> format_term!(false)
      "(X_i>i Y_i)_i"
  """
  @spec parse!(String.t(), Keyword.t() | Context.t()) :: Term.term_id()
  def parse!(formula_str, opts \\ []) do
    case parse(formula_str, opts) do
      {:ok, term_id} -> term_id
      {:error, msg} -> raise ParseError, message: msg
    end
  end

  @doc """
  Safely parses a given list of tokens with full type inference. Types which
  can't be inferred are assigned type variables. Returns the assigned ID of the
  created term.

  ## Options:

  - `ctx`: a `ShotDs.Data.Context` struct for providing type information
  - `force_o`: identify type variables on the outermost level type o

  Returns `{:ok, term_id}` or `{:error, reason}`.
  """
  @spec parse_tokens(Lexer.tokens(), Keyword.t() | Context.t()) ::
          {:ok, Term.term_id()} | {:error, String.t()}
  def parse_tokens(tokens, opts \\ []) do
    context = Keyword.get(opts, :ctx, Context.new())
    force_o = Keyword.get(opts, :force_o, false)

    with {:ok, {pre_term, [], _ctx, subst}} <- parse_formula(tokens, context, %{}),
         root_type = get_pre_type(pre_term),
         resolved_root = TI.apply_subst(root_type, subst),
         {:ok, final_subst} <-
           if(Type.type_var?(resolved_root) and force_o,
             do: TI.unify(resolved_root, Definitions.type_o(), subst),
             else: {:ok, subst}
           ) do
      {:ok, build_term(pre_term, final_subst)}
    else
      {:ok, {_, remaining, _, _}} ->
        {:error, "Unexpected tokens remaining: #{inspect(remaining)}"}

      {:error, reason} ->
        {:error, reason}
    end
  end

  @doc """
  Parses a given list of tokens with full type inference. Types which can't be
  inferred are assigned type variables. Returns the assigned ID of the created
  term.

  ## Options:

  - `ctx`: a `ShotDs.Data.Context` struct for providing type information
  - `force_o`: identify type variables on the outermost level type o

  ## Example:

      iex> {:ok, tokens, _, _, _, _} = Lexer.tokenize("$false")
      iex> parse_tokens!(tokens) |> format_term!()
      "⊥"
  """
  @spec parse_tokens!(Lexer.tokens(), Keyword.t()) :: Term.term_id()
  def parse_tokens!(tokens, opts \\ []) do
    case parse_tokens(tokens, opts) do
      {:ok, term_id} -> term_id
      {:error, msg} -> raise ParseError, message: msg
    end
  end

  ################################### TYPES ####################################

  @doc """
  Parses a HOL type from TPTP syntax into a `ShotDs.Data.Type` struct. Returns
  a tuple `{:ok, result}` or `{:error, reason}`.

  ## Example:

      iex> parse_type("$i")
      {:ok, %ShotDs.Data.Type{goal: :i, args: []}}
  """
  @spec parse_type(String.t()) :: {:ok, Type.t()} | {:error, String.t()}
  def parse_type(type_str) do
    with {:ok, tokens, "", _, _, _} <- Lexer.tokenize(type_str),
         {:ok, {type, []}} <- parse_type_tokens(tokens) do
      {:ok, type}
    else
      {:ok, _, unparsed, _, _, _} ->
        {:error, "Lexer stopped early. Unparsed content: #{unparsed}"}

      {:ok, {_, remaining}} ->
        {:error, "Failed to parse #{inspect(remaining)} into a type struct"}

      {:error, reason} ->
        {:error, "Failed to parse type: #{reason}"}
    end
  end

  @doc """
  Parses a HOL type from TPTP syntax into a `ShotDs.Data.Type` struct, raising
  on errors.

  ## Example:

      iex> parse_type!("$i")
      %ShotDs.Data.Type{goal: :i, args: []}
  """
  @spec parse_type!(String.t()) :: Type.t()
  def parse_type!(type_str) do
    case parse_type(type_str) do
      {:ok, type} -> type
      {:error, msg} -> raise ParseError, message: msg
    end
  end

  @doc """
  Parses a HOL type from a list of tokens into a `ShotDs.Data.Type` struct.
  Returns a tuple `{:ok, result}` containing the constructed type as well as the
  remaining tokens or `{:error, reason}`.
  """
  @spec parse_type_tokens(Lexer.tokens()) ::
          {:ok, {Type.t(), Lexer.tokens()}} | {:error, String.t()}
  def parse_type_tokens(tokens) do
    case parse_atomic_type(tokens) do
      {:ok, {lhs, [{:arrow, _, _} | rest]}} ->
        with {:ok, {rhs, rest2}} <- parse_type_tokens(rest),
             do: {:ok, {Type.new(rhs, lhs), rest2}}

      {:ok, {type, rest}} ->
        {:ok, {type, rest}}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp parse_atomic_type([{:system, "$i", _} | rest]), do: {:ok, {Type.new(:i), rest}}
  defp parse_atomic_type([{:system, "$o", _} | rest]), do: {:ok, {Type.new(:o), rest}}

  defp parse_atomic_type([{:system, name, _} | rest]),
    do: {:ok, {Type.new(name |> String.trim_leading("$") |> String.to_atom()), rest}}

  defp parse_atomic_type([{:atom, name, _} | rest]),
    do: {:ok, {Type.new(String.to_atom(name)), rest}}

  defp parse_atomic_type([{:distinct, name, _} | rest]) do
    name
    |> String.trim("'")
    |> String.to_atom()
    |> Type.new()
    |> then(&{:ok, {&1, rest}})
  end

  defp parse_atomic_type([{:lparen, _, _} | rest]) do
    case parse_type_tokens(rest) do
      {:ok, {type, [{:rparen, _, _} | rest2]}} -> {:ok, {type, rest2}}
      {:ok, {_, other}} -> {:error, "Expected ')', found #{inspect(other)}"}
      {:error, _} = err -> err
    end
  end

  defp parse_atomic_type([other | _rest]),
    do: {:error, "#{inspect(other)} is not a valid type token."}

  defp parse_atomic_type([]), do: {:error, "Cannot parse empty tokens to type."}

  ################################ TYPE SCHEMES ################################

  @doc """
  Parses a TPTP TH1 type scheme from a string.

  Two forms are accepted:

  - **Explicit (TH1):** `!>[A:$tType, B:$tType]: t` — every type variable in
    the body must be declared in the binder list. The kind annotation
    `:$tType` is also accepted-without (extension).
  - **Implicit:** `t` — every uppercase identifier in `t` is treated as an
    implicitly universally-quantified type variable.

  Returns `{:ok, scheme}` or `{:error, reason}`.

  ## Examples

      iex> match?({:ok, %ShotDs.Data.TypeScheme{vars: [_]}},
      ...>   parse_type_scheme("!>[A:$tType]: (A > A)"))
      true

      iex> match?({:ok, %ShotDs.Data.TypeScheme{vars: [_]}},
      ...>   parse_type_scheme("A > A"))
      true

      iex> match?({:ok, %ShotDs.Data.TypeScheme{vars: []}},
      ...>   parse_type_scheme("$i > $o"))
      true
  """
  @spec parse_type_scheme(String.t()) :: {:ok, TypeScheme.t()} | {:error, String.t()}
  def parse_type_scheme(scheme_str) do
    with {:ok, tokens, "", _, _, _} <- Lexer.tokenize(scheme_str),
         {:ok, {scheme, []}} <- parse_type_scheme_tokens(tokens) do
      {:ok, scheme}
    else
      {:ok, _, unparsed, _, _, _} ->
        {:error, "Lexer stopped early. Unparsed content: #{unparsed}"}

      {:ok, {_, remaining}} ->
        {:error, "Failed to parse #{inspect(remaining)} into a type scheme"}

      {:error, reason} ->
        {:error, "Failed to parse type scheme: #{reason}"}
    end
  end

  @doc """
  Parses a TPTP TH1 type scheme from a string, raising on errors. See
  `parse_type_scheme/1` for the accepted syntax.
  """
  @spec parse_type_scheme!(String.t()) :: TypeScheme.t()
  def parse_type_scheme!(scheme_str) do
    case parse_type_scheme(scheme_str) do
      {:ok, scheme} -> scheme
      {:error, msg} -> raise ParseError, message: msg
    end
  end

  @doc """
  Parses a type scheme from a list of tokens. Returns the constructed
  `TypeScheme` along with the remaining tokens, or `{:error, reason}`.
  """
  @spec parse_type_scheme_tokens(Lexer.tokens()) ::
          {:ok, {TypeScheme.t(), Lexer.tokens()}} | {:error, String.t()}
  def parse_type_scheme_tokens([{:forall_type, _, _}, {:lbracket, _, _} | rest]) do
    with {:ok, {bound_vars, rest_after_binder, env}} <- parse_th1_binder(rest, %{}, []),
         [{:colon, _, _} | body_tokens] <- rest_after_binder,
         {:ok, {body_type, rest_after_body, final_env}} <-
           parse_poly_type_tokens(body_tokens, env) do
      declared = MapSet.new(bound_vars)
      body_vars = Type.free_type_vars(body_type)
      unbound = MapSet.difference(body_vars, declared)
      names_by_ref = Map.new(final_env, fn {name, ref} -> {ref, name} end)

      if MapSet.size(unbound) == 0 do
        {:ok, {TypeScheme.new(bound_vars, body_type), rest_after_body}}
      else
        unbound_names =
          unbound
          |> MapSet.to_list()
          |> Enum.map(&Map.get(names_by_ref, &1, "?"))
          |> Enum.sort()

        {:error,
         "Type Error: type variable(s) #{Enum.join(unbound_names, ", ")} appear in !> body " <>
           "but are not declared in the binder."}
      end
    else
      {:error, _} = err ->
        err

      tokens when is_list(tokens) ->
        {:error, "Syntax Error: expected ':' after !> binder list, got #{inspect(tokens)}"}
    end
  end

  def parse_type_scheme_tokens(tokens) do
    with {:ok, {body_type, rest, _env}} <- parse_poly_type_tokens(tokens, %{}) do
      {:ok, {TypeScheme.generalize(body_type, MapSet.new()), rest}}
    end
  end

  @spec parse_th1_binder(Lexer.tokens(), %{String.t() => reference()}, [reference()]) ::
          {:ok, {[reference()], Lexer.tokens(), %{String.t() => reference()}}}
          | {:error, String.t()}
  defp parse_th1_binder(tokens, env, acc) do
    case tokens do
      [{:var, name, _}, {:colon, _, _}, {:system, "$tType", _} | rest] ->
        {ref, env2} = ensure_type_var_ref(name, env)
        continue_th1_binder(rest, env2, [ref | acc])

      [{:var, name, _} | rest] ->
        {ref, env2} = ensure_type_var_ref(name, env)
        continue_th1_binder(rest, env2, [ref | acc])

      other ->
        {:error, "Syntax Error: expected type variable in !> binder, got #{inspect(other)}"}
    end
  end

  defp continue_th1_binder([{:comma, _, _} | rest], env, acc),
    do: parse_th1_binder(rest, env, acc)

  defp continue_th1_binder([{:rbracket, _, _} | rest], env, acc),
    do: {:ok, {Enum.reverse(acc), rest, env}}

  defp continue_th1_binder(other, _env, _acc),
    do: {:error, "Syntax Error: expected ',' or ']' in !> binder, got #{inspect(other)}"}

  defp ensure_type_var_ref(name, env) do
    case Map.fetch(env, name) do
      {:ok, ref} ->
        {ref, env}

      :error ->
        ref = make_ref()
        {ref, Map.put(env, name, ref)}
    end
  end

  ########################## POLY TYPE PARSERS #################################

  @spec parse_poly_type_tokens(Lexer.tokens(), %{String.t() => reference()}) ::
          {:ok, {Type.t(), Lexer.tokens(), %{String.t() => reference()}}}
          | {:error, String.t()}
  defp parse_poly_type_tokens(tokens, env) do
    with {:ok, {lhs, rest, env2}} <- parse_atomic_type_with_app(tokens, env) do
      case rest do
        [{:arrow, _, _} | rest2] ->
          with {:ok, {rhs, rest3, env3}} <- parse_poly_type_tokens(rest2, env2),
               do: {:ok, {Type.new(rhs, lhs), rest3, env3}}

        _ ->
          {:ok, {lhs, rest, env2}}
      end
    end
  end

  # Parses an atomic poly type followed by zero or more `@ arg` applications
  # (left-associative type-constructor application, e.g. `set @ A`).
  defp parse_atomic_type_with_app(tokens, env) do
    with {:ok, {base, rest, env2}} <- parse_atomic_poly_type(tokens, env) do
      parse_type_app_chain(base, rest, env2)
    end
  end

  defp parse_type_app_chain(%Type{} = acc, [{:app, _, _} | rest], env) do
    with {:ok, {arg, rest2, env2}} <- parse_atomic_poly_type(rest, env) do
      parse_type_app_chain(%Type{acc | args: acc.args ++ [arg]}, rest2, env2)
    end
  end

  defp parse_type_app_chain(acc, tokens, env), do: {:ok, {acc, tokens, env}}

  defp parse_atomic_poly_type([{:system, "$i", _} | rest], env),
    do: {:ok, {Type.new(:i), rest, env}}

  defp parse_atomic_poly_type([{:system, "$o", _} | rest], env),
    do: {:ok, {Type.new(:o), rest, env}}

  defp parse_atomic_poly_type([{:system, name, _} | rest], env),
    do: {:ok, {Type.new(name |> String.trim_leading("$") |> String.to_atom()), rest, env}}

  defp parse_atomic_poly_type([{:atom, name, _} | rest], env),
    do: {:ok, {Type.new(String.to_atom(name)), rest, env}}

  defp parse_atomic_poly_type([{:distinct, name, _} | rest], env) do
    name |> String.trim("'") |> String.to_atom() |> Type.new() |> then(&{:ok, {&1, rest, env}})
  end

  defp parse_atomic_poly_type([{:var, name, _} | rest], env) do
    {ref, env2} = ensure_type_var_ref(name, env)
    {:ok, {Type.new(ref), rest, env2}}
  end

  defp parse_atomic_poly_type([{:lparen, _, _} | rest], env) do
    case parse_poly_type_tokens(rest, env) do
      {:ok, {type, [{:rparen, _, _} | rest2], env2}} -> {:ok, {type, rest2, env2}}
      {:ok, {_, other, _}} -> {:error, "Expected ')', found #{inspect(other)}"}
      {:error, _} = err -> err
    end
  end

  defp parse_atomic_poly_type([other | _rest], _env),
    do: {:error, "#{inspect(other)} is not a valid type token."}

  defp parse_atomic_poly_type([], _env),
    do: {:error, "Cannot parse empty tokens to type."}

  ################################## CONTEXT ###################################

  @doc """
  Parses a string into a `ShotDs.Data.Context` struct. Returns `{:ok, ctx}` or
  `{:error, reason}`.

  ## Example

      iex> parse_context("X:$i, c:$o>$o")
  """
  @spec parse_context(String.t()) :: {:ok, Context.t()} | {:error, String.t()}
  def parse_context(context_str) do
    initial_ctx = Context.new()

    if context_str == "" do
      {:ok, initial_ctx}
    else
      with {:ok, tokens, "", _, _, _} <- Lexer.tokenize(context_str),
           {:ok, ctx} <- parse_context_tokens(tokens, initial_ctx) do
        {:ok, ctx}
      else
        {:ok, _, unparsed, _, _, _} ->
          {:error, "Lexer stopped early. Unparsed content: #{unparsed}"}

        {:error, reason} ->
          {:error, reason}
      end
    end
  end

  @doc """
  Parses a string into a `ShotDs.Data.Context` struct, raising on errors.

  ## Example

      iex> parse_context!("X : $i, c: $o>$o")
  """
  @spec parse_context!(String.t()) :: Context.t()
  def parse_context!(context_str) do
    case parse_context(context_str) do
      {:ok, ctx} -> ctx
      {:error, msg} -> raise ParseError, message: msg
    end
  end

  @spec parse_context_tokens(Lexer.tokens(), Context.t()) ::
          {:ok, Context.t()} | {:error, String.t()}
  defp parse_context_tokens(tokens, ctx)

  defp parse_context_tokens([{:var, name, _}, {:colon, ":", _} | rest], ctx) do
    with {:ok, {type, rest2, _env}} <- parse_poly_type_tokens(rest, %{}) do
      ctx2 = Context.put_var(ctx, name, type)
      finalize_context_tokens(rest2, ctx2)
    end
  end

  defp parse_context_tokens([{:atom, name, _}, {:colon, ":", _} | rest], ctx) do
    with {:ok, {scheme, rest2}} <- parse_type_scheme_tokens(rest) do
      ctx2 = Context.put_const(ctx, name, scheme)
      finalize_context_tokens(rest2, ctx2)
    end
  end

  defp parse_context_tokens(other, _ctx),
    do: {:error, "Could not parse #{inspect(other)} into a context struct."}

  defp finalize_context_tokens([], ctx), do: {:ok, ctx}

  defp finalize_context_tokens([{:comma, ",", _} | rest], ctx),
    do: parse_context_tokens(rest, ctx)

  defp finalize_context_tokens([other | _], _ctx),
    do: {:error, "Could not parse context token #{inspect(other)}."}

  ##############################################################################
  # TERM BUILDER
  ##############################################################################

  defp build_term({:pre_const_poly, name, type, _remaining}, subst),
    do: build_term({:pre_const, name, type}, subst)

  defp build_term({:pre_app, f, arg, _type}, subst) do
    TF.make_appl_term!(build_term(f, subst), build_term(arg, subst))
  end

  defp build_term({:pre_abs, name, var_type, body, _type}, subst) do
    concrete_var_type = TI.apply_subst(var_type, subst)
    decl = Declaration.new_free_var(name, concrete_var_type)

    body_id = build_term(body, subst)
    TF.make_abstr_term!(body_id, decl)
  end

  defp build_term({:pre_var, name, type}, subst) do
    TF.make_free_var_term(name, TI.apply_subst(type, subst))
  end

  defp build_term({:pre_const, "$true", _}, _), do: Definitions.true_term()
  defp build_term({:pre_const, "$false", _}, _), do: Definitions.false_term()
  defp build_term({:pre_const, "~", _}, _), do: Definitions.neg_term()
  defp build_term({:pre_const, "|", _}, _), do: Definitions.or_term()
  defp build_term({:pre_const, "&", _}, _), do: Definitions.and_term()
  defp build_term({:pre_const, "=>", _}, _), do: Definitions.implies_term()
  defp build_term({:pre_const, "<=>", _}, _), do: Definitions.equivalent_term()

  defp build_term({:pre_const, "<~>", _}, _), do: Definitions.xor_term()
  defp build_term({:pre_const, "<=", _}, _), do: Definitions.implied_by_term()
  defp build_term({:pre_const, "~|", _}, _), do: Definitions.nor_term()
  defp build_term({:pre_const, "~&", _}, _), do: Definitions.nand_term()

  defp build_term({:pre_const, "=", type}, subst) do
    %Type{args: [alpha, alpha]} = TI.apply_subst(type, subst)
    Definitions.equals_term(alpha)
  end

  defp build_term({:pre_const, "!=", type}, subst) do
    %Type{args: [alpha, alpha]} = TI.apply_subst(type, subst)
    Definitions.not_equals_term(alpha)
  end

  defp build_term({:pre_const, "∀", type}, subst) do
    %Type{args: [%Type{args: [alpha]}]} = TI.apply_subst(type, subst)
    Definitions.forall_term(alpha)
  end

  defp build_term({:pre_const, "∃", type}, subst) do
    %Type{args: [%Type{args: [alpha]}]} = TI.apply_subst(type, subst)
    Definitions.exists_term(alpha)
  end

  defp build_term({:pre_const, name, type}, subst) do
    TF.make_const_term(name, TI.apply_subst(type, subst))
  end

  ##############################################################################
  # PARSING LOGIC
  ##############################################################################

  defp decorate_with_line_col({:ok, _} = ok, _source), do: ok

  defp decorate_with_line_col({:error, msg}, source) when is_binary(msg) do
    decorated =
      Regex.replace(~r/\[byte:(\d+)\]/, msg, fn _full, n_str ->
        {n, _} = Integer.parse(n_str)
        {line, col} = Lexer.byte_offset_to_line_col(source, n)
        "[line #{line}, column #{col}]"
      end)

    {:error, decorated}
  end

  defp unify_at(t1, t2, subst, offset) do
    case TI.unify(t1, t2, subst) do
      {:ok, new_subst} -> {:ok, new_subst}
      {:error, reason} -> {:error, "[byte:#{offset}] #{reason}"}
    end
  end

  # Specific clauses before the general tuple-arity patterns.
  defp get_pre_type({:pre_const_poly, _, type, _}), do: type
  defp get_pre_type({:pre_type_arg, type}), do: type
  defp get_pre_type({_, _, _, type}), do: type
  defp get_pre_type({_, _, _, _, type}), do: type
  defp get_pre_type({_, _, type}), do: type

  defp peek_offset([{_, _, off} | _]), do: off
  defp peek_offset(_), do: 0

  # Level 1: <, >, <=, =>, <=>, <~>

  defp parse_formula(tokens, ctx, subst) do
    with {:ok, {lhs, rest, ctx2, subst2}} <- parse_disjunction(tokens, ctx, subst) do
      parse_formula_op(lhs, rest, ctx2, subst2)
    end
  end

  defp parse_formula_op(lhs, [{:equiv, _, off} | rest], ctx, subst) do
    with {:ok, {rhs, rest2, ctx2, s1}} <- parse_formula(rest, ctx, subst),
         {:ok, s2} <- unify_at(get_pre_type(lhs), Definitions.type_o(), s1, off),
         {:ok, s3} <- unify_at(get_pre_type(rhs), Definitions.type_o(), s2, off) do
      term =
        {:pre_app,
         {:pre_app, {:pre_const, "<=>", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
         Definitions.type_o()}

      {:ok, {term, rest2, ctx2, s3}}
    end
  end

  defp parse_formula_op(lhs, [{:implies, _, off} | rest], ctx, subst) do
    with {:ok, {rhs, rest2, ctx2, s1}} <- parse_formula(rest, ctx, subst),
         {:ok, s2} <- unify_at(get_pre_type(lhs), Definitions.type_o(), s1, off),
         {:ok, s3} <- unify_at(get_pre_type(rhs), Definitions.type_o(), s2, off) do
      term =
        {:pre_app,
         {:pre_app, {:pre_const, "=>", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
         Definitions.type_o()}

      {:ok, {term, rest2, ctx2, s3}}
    end
  end

  defp parse_formula_op(lhs, [{:implied_by, _, off} | rest], ctx, subst) do
    with {:ok, {rhs, rest2, ctx2, s1}} <- parse_formula(rest, ctx, subst),
         {:ok, s2} <- unify_at(get_pre_type(lhs), Definitions.type_o(), s1, off),
         {:ok, s3} <- unify_at(get_pre_type(rhs), Definitions.type_o(), s2, off) do
      term =
        {:pre_app,
         {:pre_app, {:pre_const, "=>", Definitions.type_ooo()}, rhs, Definitions.type_oo()}, lhs,
         Definitions.type_o()}

      {:ok, {term, rest2, ctx2, s3}}
    end
  end

  defp parse_formula_op(lhs, [{:xor, _, off} | rest], ctx, subst) do
    with {:ok, {rhs, rest2, ctx2, s1}} <- parse_formula(rest, ctx, subst),
         {:ok, s2} <- unify_at(get_pre_type(lhs), Definitions.type_o(), s1, off),
         {:ok, s3} <- unify_at(get_pre_type(rhs), Definitions.type_o(), s2, off) do
      term =
        {:pre_app, {:pre_const, "~", Definitions.type_oo()},
         {:pre_app,
          {:pre_app, {:pre_const, "<=>", Definitions.type_ooo()}, lhs, Definitions.type_oo()},
          rhs, Definitions.type_o()}, Definitions.type_o()}

      {:ok, {term, rest2, ctx2, s3}}
    end
  end

  defp parse_formula_op(lhs, tokens, ctx, subst), do: {:ok, {lhs, tokens, ctx, subst}}

  defp parse_disjunction(tokens, ctx, subst) do
    with {:ok, {lhs, rest, ctx2, subst2}} <- parse_conjunction(tokens, ctx, subst) do
      parse_disjunction_op(lhs, rest, ctx2, subst2)
    end
  end

  defp parse_disjunction_op(lhs, [{:or, _, off} | rest], ctx, subst) do
    with {:ok, {rhs, rest2, ctx2, s1}} <- parse_conjunction(rest, ctx, subst),
         {:ok, s2} <- unify_at(get_pre_type(lhs), Definitions.type_o(), s1, off),
         {:ok, s3} <- unify_at(get_pre_type(rhs), Definitions.type_o(), s2, off) do
      term =
        {:pre_app,
         {:pre_app, {:pre_const, "|", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
         Definitions.type_o()}

      parse_disjunction_op(term, rest2, ctx2, s3)
    end
  end

  defp parse_disjunction_op(lhs, [{:nor, _, off} | rest], ctx, subst) do
    with {:ok, {rhs, rest2, ctx2, s1}} <- parse_conjunction(rest, ctx, subst),
         {:ok, s2} <- unify_at(get_pre_type(lhs), Definitions.type_o(), s1, off),
         {:ok, s3} <- unify_at(get_pre_type(rhs), Definitions.type_o(), s2, off) do
      term =
        {:pre_app, {:pre_const, "~", Definitions.type_oo()},
         {:pre_app,
          {:pre_app, {:pre_const, "|", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
          Definitions.type_o()}, Definitions.type_o()}

      parse_disjunction_op(term, rest2, ctx2, s3)
    end
  end

  defp parse_disjunction_op(lhs, tokens, ctx, subst), do: {:ok, {lhs, tokens, ctx, subst}}

  defp parse_conjunction(tokens, ctx, subst) do
    with {:ok, {lhs, rest, ctx2, subst2}} <- parse_unitary(tokens, ctx, subst) do
      parse_conjunction_op(lhs, rest, ctx2, subst2)
    end
  end

  defp parse_conjunction_op(lhs, [{:and, _, off} | rest], ctx, subst) do
    with {:ok, {rhs, rest2, ctx2, s1}} <- parse_unitary(rest, ctx, subst),
         {:ok, s2} <- unify_at(get_pre_type(lhs), Definitions.type_o(), s1, off),
         {:ok, s3} <- unify_at(get_pre_type(rhs), Definitions.type_o(), s2, off) do
      term =
        {:pre_app,
         {:pre_app, {:pre_const, "&", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
         Definitions.type_o()}

      parse_conjunction_op(term, rest2, ctx2, s3)
    end
  end

  defp parse_conjunction_op(lhs, [{:nand, _, off} | rest], ctx, subst) do
    with {:ok, {rhs, rest2, ctx2, s1}} <- parse_unitary(rest, ctx, subst),
         {:ok, s2} <- unify_at(get_pre_type(lhs), Definitions.type_o(), s1, off),
         {:ok, s3} <- unify_at(get_pre_type(rhs), Definitions.type_o(), s2, off) do
      term =
        {:pre_app, {:pre_const, "~", Definitions.type_oo()},
         {:pre_app,
          {:pre_app, {:pre_const, "&", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
          Definitions.type_o()}, Definitions.type_o()}

      parse_conjunction_op(term, rest2, ctx2, s3)
    end
  end

  defp parse_conjunction_op(lhs, tokens, ctx, subst), do: {:ok, {lhs, tokens, ctx, subst}}

  # Level 3: Unitary (~), Quantifiers (!, ?), Equality (=), Application (@)

  defp parse_unitary([{:not, _, _} | [{:app, _, _} | _]] = tokens, ctx, subst),
    do: parse_equality(tokens, ctx, subst)

  defp parse_unitary([{:not, _, _} | [{:rparen, _, _} | _]] = tokens, ctx, subst),
    do: parse_equality(tokens, ctx, subst)

  defp parse_unitary([{:not, _, _} | []] = tokens, ctx, subst),
    do: parse_equality(tokens, ctx, subst)

  defp parse_unitary([{:not, _, off} | rest], ctx, subst) do
    with {:ok, {term, rest2, ctx2, s1}} <- parse_unitary(rest, ctx, subst),
         {:ok, s2} <- unify_at(get_pre_type(term), Definitions.type_o(), s1, off) do
      {:ok,
       {{:pre_app, {:pre_const, "~", Definitions.type_oo()}, term, Definitions.type_o()}, rest2,
        ctx2, s2}}
    end
  end

  defp parse_unitary([{:forall, _, _} | rest], ctx, subst),
    do: parse_quantifier(:forall, rest, ctx, subst)

  defp parse_unitary([{:exists, _, _} | rest], ctx, subst),
    do: parse_quantifier(:exists, rest, ctx, subst)

  defp parse_unitary([{:lambda, _, _} | rest], ctx, subst),
    do: parse_lambda(rest, ctx, subst)

  defp parse_unitary(tokens, ctx, subst), do: parse_equality(tokens, ctx, subst)

  defp parse_equality(tokens, ctx, subst) do
    case parse_application(tokens, ctx, subst) do
      {:ok, {lhs, [{:eq, _, off} | rest], ctx2, subst2}} ->
        with {:ok, {rhs, rest2, ctx3, s1}} <- parse_application(rest, ctx2, subst2),
             {:ok, s2} <- unify_at(get_pre_type(lhs), get_pre_type(rhs), s1, off) do
          lhs_type = get_pre_type(lhs)
          eq_type = Type.new(:o, [lhs_type, lhs_type])

          term =
            {:pre_app, {:pre_app, {:pre_const, "=", eq_type}, lhs, Type.new(:o, [lhs_type])}, rhs,
             Definitions.type_o()}

          {:ok, {term, rest2, ctx3, s2}}
        end

      {:ok, {lhs, [{:neq, _, off} | rest], ctx2, subst2}} ->
        with {:ok, {rhs, rest2, ctx3, s1}} <- parse_application(rest, ctx2, subst2),
             {:ok, s2} <- unify_at(get_pre_type(lhs), get_pre_type(rhs), s1, off) do
          lhs_type = get_pre_type(lhs)
          eq_type = Type.new(:o, [lhs_type, lhs_type])

          term =
            {:pre_app, {:pre_const, "~", Definitions.type_oo()},
             {:pre_app, {:pre_app, {:pre_const, "=", eq_type}, lhs, Type.new(:o, [lhs_type])},
              rhs, Definitions.type_o()}, Definitions.type_o()}

          {:ok, {term, rest2, ctx3, s2}}
        end

      {:ok, {lhs, rest, ctx2, subst2}} ->
        {:ok, {lhs, rest, ctx2, subst2}}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp parse_application(tokens, ctx, subst) do
    with {:ok, {lhs, rest, ctx2, subst2}} <- parse_atomic(tokens, ctx, subst) do
      parse_app_chain(lhs, rest, ctx2, subst2)
    end
  end

  # Type application (TH1): polymorphic constant with pending type-param refs.
  # The next @ argument is a type, not a term. We do type erasure: unify the
  # pending ref with the provided type and skip building an app node.
  defp parse_app_chain(
         {:pre_const_poly, name, type, [next_ref | remaining]},
         [{:app, _, _} | rest],
         ctx,
         subst
       ) do
    case parse_type_arg(rest, ctx) do
      {:ok, {type_arg, rest2}} ->
        subst2 = Map.put(subst, next_ref, type_arg)

        updated_lhs =
          if remaining == [],
            do: {:pre_const, name, type},
            else: {:pre_const_poly, name, type, remaining}

        parse_app_chain(updated_lhs, rest2, ctx, subst2)

      {:error, _} = err ->
        err
    end
  end

  defp parse_app_chain(lhs, [{:app, _, off} | rest], ctx, subst) do
    with {:ok, {rhs, rest2, ctx2, s1}} <- parse_atomic(rest, ctx, subst) do
      t_f = get_pre_type(lhs)
      t_x = get_pre_type(rhs)
      t_ret = Type.fresh_type_var()
      arrow_type = Type.new(t_ret, [t_x])

      with {:ok, s2} <- unify_at(t_f, arrow_type, s1, off) do
        term = {:pre_app, lhs, rhs, t_ret}
        parse_app_chain(term, rest2, ctx2, s2)
      end
    end
  end

  defp parse_app_chain(lhs, tokens, ctx, subst), do: {:ok, {lhs, tokens, ctx, subst}}

  # Parses a single type argument for TH1 type erasure. Handles:
  #   - bare type-variable name (uppercase, from ctx.type_vars)
  #   - parenthesized type expression `(set @ A)`
  #   - bare atom or system type
  defp parse_type_arg([{:var, name, _} | rest], ctx) do
    case Map.fetch(ctx.type_vars, name) do
      {:ok, ref} -> {:ok, {%Type{goal: ref, args: []}, rest}}
      :error -> {:error, "TH1: '#{name}' is not a type variable in scope"}
    end
  end

  defp parse_type_arg([{:lparen, _, _} | rest], ctx) do
    case parse_poly_type_tokens(rest, ctx.type_vars) do
      {:ok, {type, [{:rparen, _, _} | rest2], _env}} -> {:ok, {type, rest2}}
      {:ok, {_, remaining, _}} -> {:error, "TH1: expected ')' after type arg, found #{inspect(remaining)}"}
      {:error, _} = err -> err
    end
  end

  defp parse_type_arg([{:atom, name, _} | rest], _ctx),
    do: {:ok, {Type.new(String.to_atom(name)), rest}}

  defp parse_type_arg([{:system, name, _} | rest], _ctx),
    do: {:ok, {Type.new(name |> String.trim_leading("$") |> String.to_atom()), rest}}

  defp parse_type_arg(tokens, _ctx),
    do: {:error, "TH1: expected type argument, found #{inspect(tokens)}"}

  defp parse_quantifier(type_key, [{:lbracket, _, off} | rest], ctx, subst) do
    with {:ok, {vars, updated_tvar_env, [{:rbracket, _, _}, {:colon, _, _} | body_tokens]}} <-
           parse_typed_vars_with_inference(rest, ctx.type_vars),
         inner_ctx =
           vars
           |> Enum.reduce(%{ctx | type_vars: updated_tvar_env}, fn {name, type}, acc ->
             Context.put_var(acc, name, type)
           end),
         {:ok, {body_pre_term, rest_tokens, _body_ctx, subst2}} <-
           (case body_tokens do
              [{:lparen, _, _} | _] -> parse_atomic(body_tokens, inner_ctx, subst)
              _ -> parse_formula(body_tokens, inner_ctx, subst)
            end),
         {:ok, subst3} <-
           unify_at(get_pre_type(body_pre_term), Definitions.type_o(), subst2, off) do
      quant_name = if type_key == :forall, do: "∀", else: "∃"

      term =
        Enum.reverse(vars)
        |> Enum.reduce(body_pre_term, fn {name, var_type}, acc_term ->
          abs_type = Type.new(:o, [var_type])
          abs_node = {:pre_abs, name, var_type, acc_term, abs_type}
          quant_const = {:pre_const, quant_name, Type.new(:o, [abs_type])}
          {:pre_app, quant_const, abs_node, Definitions.type_o()}
        end)

      {:ok, {term, rest_tokens, ctx, subst3}}
    else
      {:ok, {_, _, remaining}} ->
        {:error, "Syntax Error: Expected closing bracket and colon, found: #{inspect(remaining)}"}

      {:error, _} = err ->
        err
    end
  end

  defp parse_quantifier(type_key, [{:lparen, _, off}, {:lambda, _, _} | rest], ctx, subst) do
    case parse_lambda(rest, ctx, subst) do
      {:ok, {abs_term, [{:rparen, _, _} | final_tokens], _lambda_ctx, subst2}} ->
        abs_type = get_pre_type(abs_term)
        element_type = Type.fresh_type_var()
        expected_pred_type = Type.new(:o, [element_type])
        quant_name = if type_key == :forall, do: "∀", else: "∃"

        with {:ok, subst3} <- unify_at(abs_type, expected_pred_type, subst2, off) do
          quant_const = {:pre_const, quant_name, Type.new(:o, [expected_pred_type])}
          term = {:pre_app, quant_const, abs_term, Definitions.type_o()}
          {:ok, {term, final_tokens, ctx, subst3}}
        end

      {:ok, {_, [{type, val, _} | _], _, _}} ->
        {:error, "Syntax Error: Expected ')', found '#{val}' (#{inspect(type)})."}

      {:ok, {_, [], _, _}} ->
        {:error, "Syntax Error: Unexpected end of input."}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp parse_quantifier(type_key, rest, ctx, subst) do
    off = peek_offset(rest)

    with {:ok, {term, rest2, ctx2, subst2}} <- parse_unitary(rest, ctx, subst),
         term_type = get_pre_type(term),
         alpha = Type.fresh_type_var(),
         expected_pred_type = Type.new(:o, [alpha]),
         {:ok, subst3} <- unify_at(term_type, expected_pred_type, subst2, off) do
      quant_name = if type_key == :forall, do: "∀", else: "∃"
      quant_const_type = Type.new(:o, [expected_pred_type])
      quant_const = {:pre_const, quant_name, quant_const_type}
      {:ok, {{:pre_app, quant_const, term, Definitions.type_o()}, rest2, ctx2, subst3}}
    end
  end

  defp parse_lambda([{:lbracket, _, _} | rest], ctx, subst) do
    with {:ok, {vars, updated_tvar_env, rest_after_vars}} <-
           parse_typed_vars_with_inference(rest, ctx.type_vars),
         inner_ctx =
           vars
           |> Enum.reduce(%{ctx | type_vars: updated_tvar_env}, fn {n, t}, c ->
             Context.put_var(c, n, t)
           end),
         [{:rbracket, _, _}, {:colon, _, _} | body_tokens] <- rest_after_vars,
         {:ok, {body_pre_term, rest_tokens, _body_ctx, subst2}} <-
           (case body_tokens do
              [{:lparen, _, _} | _] -> parse_atomic(body_tokens, inner_ctx, subst)
              _ -> parse_formula(body_tokens, inner_ctx, subst)
            end) do
      term =
        Enum.reverse(vars)
        |> Enum.reduce(body_pre_term, fn {name, type}, acc ->
          body_type = get_pre_type(acc)
          abs_type = Type.new(body_type, [type])
          {:pre_abs, name, type, acc, abs_type}
        end)

      {:ok, {term, rest_tokens, ctx, subst2}}
    else
      unmatched_tokens when is_list(unmatched_tokens) ->
        {:error,
         "Syntax Error: Expected closing bracket and colon in lambda, found: #{inspect(unmatched_tokens)}"}

      {:error, _} = err ->
        err
    end
  end

  # Parses a binder variable list `X, Y: $i, Z: set @ A, ...` returning:
  #   {:ok, {term_vars, updated_tvar_env, remaining_tokens}}
  # where term_vars is [{name, type}] for term-level bound variables.
  # Type-variable binders (`A: $tType`) are added to tvar_env only and excluded
  # from term_vars (type erasure).
  defp parse_typed_vars_with_inference(tokens, tvar_env, term_acc \\ [])

  defp parse_typed_vars_with_inference(
         [{:var, name, _}, {:colon, _, _}, {:system, "$tType", _} | rest],
         tvar_env,
         term_acc
       ) do
    ref = make_ref()
    new_tvar_env = Map.put(tvar_env, name, ref)

    case rest do
      [{:comma, _, _} | rest2] ->
        parse_typed_vars_with_inference(rest2, new_tvar_env, term_acc)

      _ ->
        {:ok, {term_acc, new_tvar_env, rest}}
    end
  end

  defp parse_typed_vars_with_inference(
         [{:var, name, _}, {:colon, _, _} | rest],
         tvar_env,
         term_acc
       ) do
    case parse_poly_type_tokens(rest, tvar_env) do
      {:ok, {type, [{:comma, _, _} | rest2], updated_tvar_env}} ->
        parse_typed_vars_with_inference(
          rest2,
          updated_tvar_env,
          term_acc ++ [{name, type}]
        )

      {:ok, {type, rest2, updated_tvar_env}} ->
        {:ok, {term_acc ++ [{name, type}], updated_tvar_env, rest2}}

      {:error, _} = err ->
        err
    end
  end

  defp parse_typed_vars_with_inference(
         [{:var, name, _}, {:comma, _, _} | rest],
         tvar_env,
         term_acc
       ) do
    parse_typed_vars_with_inference(
      rest,
      tvar_env,
      term_acc ++ [{name, Type.fresh_type_var()}]
    )
  end

  defp parse_typed_vars_with_inference([{:var, name, _} | rest], tvar_env, term_acc) do
    {:ok, {term_acc ++ [{name, Type.fresh_type_var()}], tvar_env, rest}}
  end

  defp parse_typed_vars_with_inference(other, _tvar_env, _term_acc) do
    {:error, "Syntax Error: Invalid variable mapping sequence #{inspect(other)}"}
  end

  defp parse_atomic([{:lparen, _, _} | rest], ctx, subst) do
    with {:ok, {term, rest2, ctx2, subst2}} <- parse_formula(rest, ctx, subst),
         {:ok, {chained, rest3, ctx3, subst3}} <- parse_app_chain(term, rest2, ctx2, subst2) do
      case rest3 do
        [{:rparen, _, _} | final_rest] ->
          {:ok, {chained, final_rest, ctx3, subst3}}

        [{type, val, _} | _] ->
          {:error, "Syntax Error: Expected ')', found '#{val}' (#{inspect(type)})."}

        [] ->
          {:error, "Syntax Error: Missing closing ')'."}
      end
    end
  end

  defp parse_atomic([{:var, name, _} | rest], ctx, subst) do
    case Map.fetch(ctx.type_vars, name) do
      {:ok, ref} ->
        # TH1 type variable used as a term-level type argument
        {:ok, {{:pre_type_arg, %Type{goal: ref, args: []}}, rest, ctx, subst}}

      :error ->
        case Context.get_type(ctx, name) do
          nil ->
            new_type = Type.fresh_type_var()
            ctx2 = Context.put_var(ctx, name, new_type)
            {:ok, {{:pre_var, name, new_type}, rest, ctx2, subst}}

          type ->
            {:ok, {{:pre_var, name, type}, rest, ctx, subst}}
        end
    end
  end

  defp parse_atomic([{atom_or_distinct, name, _} | rest], ctx, subst)
       when atom_or_distinct in [:atom, :distinct] do
    case Context.get_const_scheme(ctx, name) do
      %TypeScheme{vars: [_ | _]} = scheme ->
        {mono_type, fresh_refs} = TypeScheme.instantiate_with_refs(scheme)
        {:ok, {{:pre_const_poly, name, mono_type, fresh_refs}, rest, ctx, subst}}

      _ ->
        case Context.get_type(ctx, name) do
          nil ->
            new_type = Type.fresh_type_var()
            ctx2 = Context.put_const(ctx, name, new_type)
            {:ok, {{:pre_const, name, new_type}, rest, ctx2, subst}}

          type ->
            {:ok, {{:pre_const, name, type}, rest, ctx, subst}}
        end
    end
  end

  defp parse_atomic([{:system, "$true", _} | rest], ctx, subst),
    do: {:ok, {{:pre_const, "$true", Definitions.type_o()}, rest, ctx, subst}}

  defp parse_atomic([{:system, "$false", _} | rest], ctx, subst),
    do: {:ok, {{:pre_const, "$false", Definitions.type_o()}, rest, ctx, subst}}

  defp parse_atomic([{:eq, _, _} | rest], ctx, subst) do
    alpha = Type.fresh_type_var()
    {:ok, {{:pre_const, "=", Type.new(:o, [alpha, alpha])}, rest, ctx, subst}}
  end

  defp parse_atomic([{:neq, _, _} | rest], ctx, subst) do
    alpha = Type.fresh_type_var()
    {:ok, {{:pre_const, "!=", Type.new(:o, [alpha, alpha])}, rest, ctx, subst}}
  end

  defp parse_atomic([{:equiv, _, _} | rest], ctx, subst),
    do: {:ok, {{:pre_const, "<=>", Definitions.type_ooo()}, rest, ctx, subst}}

  defp parse_atomic([{:implies, _, _} | rest], ctx, subst),
    do: {:ok, {{:pre_const, "=>", Definitions.type_ooo()}, rest, ctx, subst}}

  defp parse_atomic([{:implied_by, _, _} | rest], ctx, subst),
    do: {:ok, {{:pre_const, "<=", Definitions.type_ooo()}, rest, ctx, subst}}

  defp parse_atomic([{:xor, _, _} | rest], ctx, subst),
    do: {:ok, {{:pre_const, "<~>", Definitions.type_ooo()}, rest, ctx, subst}}

  defp parse_atomic([{:nor, _, _} | rest], ctx, subst),
    do: {:ok, {{:pre_const, "~|", Definitions.type_ooo()}, rest, ctx, subst}}

  defp parse_atomic([{:nand, _, _} | rest], ctx, subst),
    do: {:ok, {{:pre_const, "~&", Definitions.type_ooo()}, rest, ctx, subst}}

  defp parse_atomic([{:forall, _, _} | [{:lbracket, _, _} | _] = rest], ctx, subst),
    do: parse_quantifier(:forall, rest, ctx, subst)

  defp parse_atomic([{:exists, _, _} | [{:lbracket, _, _} | _] = rest], ctx, subst),
    do: parse_quantifier(:exists, rest, ctx, subst)

  defp parse_atomic(
         [{:forall, _, _} | [{:lparen, _, _}, {:lambda, _, _} | _] = rest],
         ctx,
         subst
       ),
       do: parse_quantifier(:forall, rest, ctx, subst)

  defp parse_atomic(
         [{:exists, _, _} | [{:lparen, _, _}, {:lambda, _, _} | _] = rest],
         ctx,
         subst
       ),
       do: parse_quantifier(:exists, rest, ctx, subst)

  defp parse_atomic([{:forall, _, _} | rest], ctx, subst) do
    type = Type.new(:o, [Type.new(:o, [Type.fresh_type_var()])])
    {:ok, {{:pre_const, "∀", type}, rest, ctx, subst}}
  end

  defp parse_atomic([{:exists, _, _} | rest], ctx, subst) do
    type = Type.new(:o, [Type.new(:o, [Type.fresh_type_var()])])
    {:ok, {{:pre_const, "∃", type}, rest, ctx, subst}}
  end

  defp parse_atomic([{:lambda, _, _} | rest], ctx, subst), do: parse_lambda(rest, ctx, subst)

  defp parse_atomic([{:not, _, _} | rest], ctx, subst),
    do: {:ok, {{:pre_const, "~", Definitions.type_oo()}, rest, ctx, subst}}

  defp parse_atomic([{:or, _, _} | rest], ctx, subst),
    do: {:ok, {{:pre_const, "|", Definitions.type_ooo()}, rest, ctx, subst}}

  defp parse_atomic([{:and, _, _} | rest], ctx, subst),
    do: {:ok, {{:pre_const, "&", Definitions.type_ooo()}, rest, ctx, subst}}

  defp parse_atomic([token | _rest], _ctx, _subst) do
    {type, value, _offset} = token
    {:error, "Syntax Error: Expected atomic term, but found token '#{value}' (#{inspect(type)})."}
  end

  defp parse_atomic([], _ctx, _subst) do
    {:error, "Syntax Error: Unexpected end of input."}
  end
end
