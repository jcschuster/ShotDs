defmodule ShotDs.Parser do
  @moduledoc """
  Contains functionality to parse a formula in TH0 syntax with full type
  inference. The algorithm is similar to Hindley-Milner type systems but for
  simplicity reasons without the optimizations found in algorithms J or W.
  Uses Robinson's first-order unification algorithm for type inference. A
  context can be specified to clear up unknown types. If terms still have
  unknown type after parsing, unifies their type with type o. The main entry
  point is the `parse/2` function.

  The parser follows standard TH0 precedence rules. The binding strength is listed
  below from **strongest (tightest binding)** to **weakest**.

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
  """

  alias ShotDs.Data.{Type, Declaration, Term, Context}
  alias ShotDs.Hol.Definitions
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.Lexer
  alias ShotDs.Util.TypeInference, as: TI

  @dialyzer {:no_opaque, parse: 1, parse!: 1, parse_tokens: 1, parse_tokens!: 1, parse_context: 1}
  @dialyzer {:nowarn_function, parse!: 1}

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

  ## Example:

      iex> match?({:ok, _parsed}, parse("X & a"))
      true

      iex> match?({:ok, _parsed}, parse("X &"))
      false
  """
  @spec parse(String.t(), Context.t()) :: {:ok, Term.term_id()} | {:error, String.t()}
  def parse(formula_str, context \\ Context.new()) do
    case Lexer.tokenize(formula_str) do
      {:ok, tokens, "", _, _, _} ->
        parse_tokens(tokens, context)

      {:ok, _, unparsed, _, _, _} ->
        {:error, "Lexer stopped early. Unparsed content: #{unparsed}"}
    end
  end

  @doc """
  Parses a given string representing a formula in TH0 syntax with full type
  inference, raising a `ShotDs.Parser.ParseError` if invalid. Types which can't
  be inferred are assigned type variables. Variables on the outermost level are
  identified with type o. Returns the assigned ID of the created term.

  ## Example:

      iex> parse!("X & a") |> format_term!()
      "X ∧ a"

      iex> parse!("X @ Y") |> format_term!(_hide_types = false)
      "(X_T[OUFDH]>o Y_T[OUFDH])_o"

      iex> parse!("X @ Y", ~e(X::$i>$i, Y::$i)) |> format_term!(false)
      "(X_i>i Y_i)_i"
  """
  @spec parse!(String.t(), Context.t()) :: Term.term_id()
  def parse!(formula_str, context \\ Context.new()) do
    case parse(formula_str, context) do
      {:ok, term_id} -> term_id
      {:error, msg} -> raise ParseError, message: msg
    end
  end

  @doc """
  Safely parses a given list of tokens with full type inference. Types which
  can't be inferred are assigned type variables. Variables on the outermost
  level are identified with type o. Returns the assigned ID of the created term.

  Returns `{:ok, term_id}` or `{:error, reason}`.
  """
  @spec parse_tokens(Lexer.tokens(), Context.t()) :: {:ok, Term.term_id()} | {:error, String.t()}
  def parse_tokens(tokens, context \\ Context.new()) do
    with {:ok, {pre_term, [], almost_final_ctx}} <- parse_formula(tokens, context),
         root_type = get_pre_type(pre_term),
         {:ok, substitutions} <- TI.solve(almost_final_ctx.constraints),
         resolved_root = TI.apply_subst(root_type, substitutions),
         final_ctx =
           if(Type.type_var?(resolved_root),
             do: Context.add_constraint(almost_final_ctx, resolved_root, Definitions.type_o()),
             else: almost_final_ctx
           ),
         {:ok, final_substitutions} <- TI.solve(final_ctx.constraints) do
      {:ok, build_term(pre_term, final_substitutions)}
    else
      {:ok, {_, remaining, _}} -> {:error, "Unexpected tokens remaining: #{inspect(remaining)}"}
      {:error, reason} -> {:error, reason}
    end
  end

  @doc """
  Parses a given list of tokens with full type inference. Types which can't be
  inferred are assigned type variables. Variables on the outermost level are
  identified with type o. Returns the assigned ID of the created term.

  ## Example:

      iex> {:ok, tokens, _, _, _, _} = Lexer.tokenize("$false")
      iex> parse_tokens!(tokens) |> format_term!()
      "⊥"
  """
  @spec parse_tokens!(Lexer.tokens(), Context.t()) :: Term.term_id()
  def parse_tokens!(tokens, context \\ Context.new()) do
    case parse_tokens(tokens, context) do
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
      {:ok, {lhs, [{:arrow, _} | rest]}} ->
        with {:ok, {rhs, rest2}} <- parse_type_tokens(rest),
             do: {:ok, {Type.new(rhs, lhs), rest2}}

      {:ok, {type, rest}} ->
        {:ok, {type, rest}}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp parse_atomic_type([{:system, "$i"} | rest]), do: {:ok, {Type.new(:i), rest}}
  defp parse_atomic_type([{:system, "$o"} | rest]), do: {:ok, {Type.new(:o), rest}}

  defp parse_atomic_type([{:atom, name} | rest]),
    do: {:ok, {Type.new(String.to_atom(name)), rest}}

  defp parse_atomic_type([{:lparen, _} | rest]) do
    case parse_type_tokens(rest) do
      {:ok, {type, [{:rparen, _} | rest2]}} -> {:ok, {type, rest2}}
      {:ok, {_, other}} -> {:error, "Expected ')', found #{inspect(other)}"}
      {:error, _} = err -> err
    end
  end

  defp parse_atomic_type([other | _rest]),
    do: {:error, "#{inspect(other)} is not a valid type token."}

  defp parse_atomic_type([]), do: {:error, "Cannot parse empty tokens to type."}

  ################################## CONTEXT ###################################

  @doc """
  Parses a string into a `ShotDs.Data.Context` struct. Returns `{:ok, ctx}` or
  `{:error, reason}`.

  ## Example

      iex> parse_context("X::$i, c::$o>$o")
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

      iex> parse_context!("X::$i, c::$o>$o")
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

  defp parse_context_tokens([{:var, name}, {:dcolon, "::"} | rest], ctx) do
    with {:ok, {type, rest2}} <- parse_type_tokens(rest) do
      ctx2 = Context.put_var(ctx, name, type)

      case rest2 do
        [] -> {:ok, ctx2}
        [{:comma, ","} | rest3] -> parse_context_tokens(rest3, ctx2)
        [other | _] -> {:error, "Could not parse context token #{inspect(other)}."}
      end
    end
  end

  defp parse_context_tokens([{:atom, name}, {:dcolon, "::"} | rest], ctx) do
    with {:ok, {type, rest2}} <- parse_type_tokens(rest) do
      ctx2 = Context.put_const(ctx, name, type)

      case rest2 do
        [] -> {:ok, ctx2}
        [{:comma, ","} | rest3] -> parse_context_tokens(rest3, ctx2)
        [other | _] -> {:error, "Could not parse context token #{inspect(other)}."}
      end
    end
  end

  defp parse_context_tokens(other, _ctx),
    do: {:error, "Could not parse #{inspect(other)} into a context struct."}

  ##############################################################################
  # TERM BUILDER
  ##############################################################################

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

  defp build_term({:pre_const, "Π", type}, subst) do
    %Type{args: [%Type{args: [alpha]}]} = TI.apply_subst(type, subst)
    Definitions.pi_term(alpha)
  end

  defp build_term({:pre_const, "Σ", type}, subst) do
    %Type{args: [%Type{args: [alpha]}]} = TI.apply_subst(type, subst)
    Definitions.sigma_term(alpha)
  end

  defp build_term({:pre_const, name, type}, subst) do
    TF.make_const_term(name, TI.apply_subst(type, subst))
  end

  ##############################################################################
  # PARSING LOGIC
  ##############################################################################

  defp constrain(ctx, term_node, expected_type) do
    term_type = get_pre_type(term_node)
    Context.add_constraint(ctx, term_type, expected_type)
  end

  defp get_pre_type({_, _, _, type}), do: type
  defp get_pre_type({_, _, _, _, type}), do: type
  defp get_pre_type({_, _, type}), do: type

  # Level 1: <, >, <=, =>, <=>, <~>

  defp parse_formula(tokens, ctx) do
    with {:ok, {lhs, rest, ctx2}} <- parse_disjunction(tokens, ctx) do
      parse_formula_op(lhs, rest, ctx2)
    end
  end

  defp parse_formula_op(lhs, [{:equiv, _} | rest], ctx) do
    with {:ok, {rhs, rest2, ctx2}} <- parse_formula(rest, ctx) do
      ctx3 = ctx2 |> constrain(lhs, Definitions.type_o()) |> constrain(rhs, Definitions.type_o())

      term =
        {:pre_app,
         {:pre_app, {:pre_const, "<=>", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
         Definitions.type_o()}

      {:ok, {term, rest2, ctx3}}
    end
  end

  defp parse_formula_op(lhs, [{:implies, _} | rest], ctx) do
    with {:ok, {rhs, rest2, ctx2}} <- parse_formula(rest, ctx) do
      ctx3 = ctx2 |> constrain(lhs, Definitions.type_o()) |> constrain(rhs, Definitions.type_o())

      term =
        {:pre_app,
         {:pre_app, {:pre_const, "=>", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
         Definitions.type_o()}

      {:ok, {term, rest2, ctx3}}
    end
  end

  defp parse_formula_op(lhs, [{:implied_by, _} | rest], ctx) do
    with {:ok, {rhs, rest2, ctx2}} <- parse_formula(rest, ctx) do
      ctx3 = ctx2 |> constrain(lhs, Definitions.type_o()) |> constrain(rhs, Definitions.type_o())

      term =
        {:pre_app,
         {:pre_app, {:pre_const, "=>", Definitions.type_ooo()}, rhs, Definitions.type_oo()}, lhs,
         Definitions.type_o()}

      {:ok, {term, rest2, ctx3}}
    end
  end

  defp parse_formula_op(lhs, [{:xor, _} | rest], ctx) do
    with {:ok, {rhs, rest2, ctx2}} <- parse_formula(rest, ctx) do
      ctx3 = ctx2 |> constrain(lhs, Definitions.type_o()) |> constrain(rhs, Definitions.type_o())

      term =
        {:pre_app, {:pre_const, "~", Definitions.type_oo()},
         {:pre_app,
          {:pre_app, {:pre_const, "<=>", Definitions.type_ooo()}, lhs, Definitions.type_oo()},
          rhs, Definitions.type_o()}, Definitions.type_o()}

      {:ok, {term, rest2, ctx3}}
    end
  end

  defp parse_formula_op(lhs, tokens, ctx), do: {:ok, {lhs, tokens, ctx}}

  # Level 2: | (OR), & (AND), ~| (NOR), ~& (NAND)

  defp parse_disjunction(tokens, ctx) do
    with {:ok, {lhs, rest, ctx2}} <- parse_conjunction(tokens, ctx) do
      parse_disjunction_op(lhs, rest, ctx2)
    end
  end

  defp parse_disjunction_op(lhs, [{:or, _} | rest], ctx) do
    with {:ok, {rhs, rest2, ctx2}} <- parse_conjunction(rest, ctx) do
      ctx3 = ctx2 |> constrain(lhs, Definitions.type_o()) |> constrain(rhs, Definitions.type_o())

      term =
        {:pre_app,
         {:pre_app, {:pre_const, "|", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
         Definitions.type_o()}

      parse_disjunction_op(term, rest2, ctx3)
    end
  end

  defp parse_disjunction_op(lhs, [{:nor, _} | rest], ctx) do
    with {:ok, {rhs, rest2, ctx2}} <- parse_conjunction(rest, ctx) do
      ctx3 = ctx2 |> constrain(lhs, Definitions.type_o()) |> constrain(rhs, Definitions.type_o())

      term =
        {:pre_app, {:pre_const, "~", Definitions.type_oo()},
         {:pre_app,
          {:pre_app, {:pre_const, "|", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
          Definitions.type_o()}, Definitions.type_o()}

      parse_disjunction_op(term, rest2, ctx3)
    end
  end

  defp parse_disjunction_op(lhs, tokens, ctx), do: {:ok, {lhs, tokens, ctx}}

  defp parse_conjunction(tokens, ctx) do
    with {:ok, {lhs, rest, ctx2}} <- parse_unitary(tokens, ctx) do
      parse_conjunction_op(lhs, rest, ctx2)
    end
  end

  defp parse_conjunction_op(lhs, [{:and, _} | rest], ctx) do
    with {:ok, {rhs, rest2, ctx2}} <- parse_unitary(rest, ctx) do
      ctx3 = ctx2 |> constrain(lhs, Definitions.type_o()) |> constrain(rhs, Definitions.type_o())

      term =
        {:pre_app,
         {:pre_app, {:pre_const, "&", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
         Definitions.type_o()}

      parse_conjunction_op(term, rest2, ctx3)
    end
  end

  defp parse_conjunction_op(lhs, [{:nand, _} | rest], ctx) do
    with {:ok, {rhs, rest2, ctx2}} <- parse_unitary(rest, ctx) do
      ctx3 = ctx2 |> constrain(lhs, Definitions.type_o()) |> constrain(rhs, Definitions.type_o())

      term =
        {:pre_app, {:pre_const, "~", Definitions.type_oo()},
         {:pre_app,
          {:pre_app, {:pre_const, "&", Definitions.type_ooo()}, lhs, Definitions.type_oo()}, rhs,
          Definitions.type_o()}, Definitions.type_o()}

      parse_conjunction_op(term, rest2, ctx3)
    end
  end

  defp parse_conjunction_op(lhs, tokens, ctx), do: {:ok, {lhs, tokens, ctx}}

  # Level 3: Unitary (~), Quantifiers (!, ?), Equality (=), Application (@)

  defp parse_unitary([{:not, _} | [{:app, _} | _]] = tokens, ctx), do: parse_equality(tokens, ctx)

  defp parse_unitary([{:not, _} | [{:rparen, _} | _]] = tokens, ctx),
    do: parse_equality(tokens, ctx)

  defp parse_unitary([{:not, _} | []] = tokens, ctx), do: parse_equality(tokens, ctx)

  defp parse_unitary([{:not, _} | rest], ctx) do
    with {:ok, {term, rest2, ctx2}} <- parse_unitary(rest, ctx) do
      ctx3 = constrain(ctx2, term, Definitions.type_o())

      {:ok,
       {{:pre_app, {:pre_const, "~", Definitions.type_oo()}, term, Definitions.type_o()}, rest2,
        ctx3}}
    end
  end

  defp parse_unitary([{:forall, _} | rest], ctx), do: parse_quantifier(:pi, rest, ctx)
  defp parse_unitary([{:exists, _} | rest], ctx), do: parse_quantifier(:sigma, rest, ctx)
  defp parse_unitary([{:lambda, _} | rest], ctx), do: parse_lambda(rest, ctx)
  defp parse_unitary([{:pi, _} | [_ | _] = rest], ctx), do: parse_quantifier(:pi, rest, ctx)
  defp parse_unitary([{:sigma, _} | [_ | _] = rest], ctx), do: parse_quantifier(:sigma, rest, ctx)
  defp parse_unitary(tokens, ctx), do: parse_equality(tokens, ctx)

  defp parse_equality(tokens, ctx) do
    case parse_application(tokens, ctx) do
      {:ok, {lhs, [{:eq, _} | rest], ctx2}} ->
        with {:ok, {rhs, rest2, ctx3}} <- parse_application(rest, ctx2) do
          lhs_type = get_pre_type(lhs)
          rhs_type = get_pre_type(rhs)
          ctx4 = Context.add_constraint(ctx3, lhs_type, rhs_type)
          eq_type = Type.new(:o, [lhs_type, lhs_type])

          term =
            {:pre_app, {:pre_app, {:pre_const, "=", eq_type}, lhs, Type.new(:o, [lhs_type])}, rhs,
             Definitions.type_o()}

          {:ok, {term, rest2, ctx4}}
        end

      {:ok, {lhs, [{:neq, _} | rest], ctx2}} ->
        with {:ok, {rhs, rest2, ctx3}} <- parse_application(rest, ctx2) do
          lhs_type = get_pre_type(lhs)
          rhs_type = get_pre_type(rhs)
          ctx4 = Context.add_constraint(ctx3, lhs_type, rhs_type)
          eq_type = Type.new(:o, [lhs_type, lhs_type])

          term =
            {:pre_app, {:pre_const, "~", Definitions.type_oo()},
             {:pre_app, {:pre_app, {:pre_const, "=", eq_type}, lhs, Type.new(:o, [lhs_type])},
              rhs, Definitions.type_o()}, Definitions.type_o()}

          {:ok, {term, rest2, ctx4}}
        end

      {:ok, {lhs, rest, ctx2}} ->
        {:ok, {lhs, rest, ctx2}}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp parse_application(tokens, ctx) do
    with {:ok, {lhs, rest, ctx2}} <- parse_atomic(tokens, ctx) do
      parse_app_chain(lhs, rest, ctx2)
    end
  end

  defp parse_app_chain(lhs, [{:app, _} | rest], ctx) do
    with {:ok, {rhs, rest2, ctx2}} <- parse_atomic(rest, ctx) do
      t_f = get_pre_type(lhs)
      t_x = get_pre_type(rhs)
      t_ret = Type.fresh_type_var()
      arrow_type = Type.new(t_ret, [t_x])
      ctx3 = Context.add_constraint(ctx2, t_f, arrow_type)
      term = {:pre_app, lhs, rhs, t_ret}
      parse_app_chain(term, rest2, ctx3)
    end
  end

  defp parse_app_chain(lhs, tokens, ctx), do: {:ok, {lhs, tokens, ctx}}

  defp parse_quantifier(type_key, [{:lbracket, _} | rest], ctx) do
    with {:ok, {vars, [{:rbracket, _}, {:colon, _} | body_tokens]}} <-
           parse_typed_vars_with_inference(rest),
         inner_ctx =
           Enum.reduce(vars, ctx, fn {name, type}, acc -> Context.put_var(acc, name, type) end),
         {:ok, {body_pre_term, rest_tokens, body_ctx}} <-
           (case body_tokens do
              [{:lparen, _} | _] -> parse_atomic(body_tokens, inner_ctx)
              _ -> parse_formula(body_tokens, inner_ctx)
            end) do
      final_ctx =
        Context.add_constraint(body_ctx, get_pre_type(body_pre_term), Definitions.type_o())

      outer_ctx = %{ctx | constraints: final_ctx.constraints}

      quant_name = if type_key == :pi, do: "Π", else: "Σ"

      term =
        Enum.reverse(vars)
        |> Enum.reduce(body_pre_term, fn {name, var_type}, acc_term ->
          abs_type = Type.new(:o, [var_type])
          abs_node = {:pre_abs, name, var_type, acc_term, abs_type}
          quant_const = {:pre_const, quant_name, Type.new(:o, [abs_type])}
          {:pre_app, quant_const, abs_node, Definitions.type_o()}
        end)

      {:ok, {term, rest_tokens, outer_ctx}}
    else
      {:ok, {_, remaining}} ->
        {:error, "Syntax Error: Expected closing bracket and colon, found: #{inspect(remaining)}"}

      {:error, _} = err ->
        err
    end
  end

  defp parse_quantifier(type_key, [{:lparen, _}, {:lambda, _} | rest], ctx) do
    case parse_lambda(rest, ctx) do
      {:ok, {abs_term, [{:rparen, _} | final_tokens], lambda_ctx}} ->
        abs_type = get_pre_type(abs_term)
        element_type = Type.fresh_type_var()
        expected_pred_type = Type.new(:o, [element_type])
        final_ctx = Context.add_constraint(lambda_ctx, abs_type, expected_pred_type)
        quant_name = if type_key == :pi, do: "Π", else: "Σ"
        quant_const = {:pre_const, quant_name, Type.new(:o, [expected_pred_type])}
        term = {:pre_app, quant_const, abs_term, Definitions.type_o()}
        {:ok, {term, final_tokens, final_ctx}}

      {:ok, {_, [{type, val} | _], _}} ->
        {:error, "Syntax Error: Expected ')', found '#{val}' (#{inspect(type)})."}

      {:ok, {_, [], _}} ->
        {:error, "Syntax Error: Unexpected end of input."}

      {:error, reason} ->
        {:error, reason}
    end
  end

  defp parse_quantifier(type_key, rest, ctx) do
    with {:ok, {term, rest2, ctx2}} <- parse_unitary(rest, ctx) do
      term_type = get_pre_type(term)
      alpha = Type.fresh_type_var()
      expected_pred_type = Type.new(:o, [alpha])
      ctx3 = Context.add_constraint(ctx2, term_type, expected_pred_type)
      quant_name = if type_key == :pi, do: "Π", else: "Σ"
      quant_const_type = Type.new(:o, [expected_pred_type])
      quant_const = {:pre_const, quant_name, quant_const_type}
      {:ok, {{:pre_app, quant_const, term, Definitions.type_o()}, rest2, ctx3}}
    end
  end

  defp parse_lambda([{:lbracket, _} | rest], ctx) do
    with {:ok, {vars, rest_after_vars}} <- parse_typed_vars_with_inference(rest),
         inner_ctx = Enum.reduce(vars, ctx, fn {n, t}, c -> Context.put_var(c, n, t) end),
         [{:rbracket, _}, {:colon, _} | body_tokens] <- rest_after_vars,
         {:ok, {body_pre_term, rest_tokens, body_ctx}} <-
           (case body_tokens do
              [{:lparen, _} | _] -> parse_atomic(body_tokens, inner_ctx)
              _ -> parse_formula(body_tokens, inner_ctx)
            end) do
      final_ctx = %{ctx | constraints: body_ctx.constraints}

      term =
        Enum.reverse(vars)
        |> Enum.reduce(body_pre_term, fn {name, type}, acc ->
          body_type = get_pre_type(acc)
          abs_type = Type.new(body_type, [type])
          {:pre_abs, name, type, acc, abs_type}
        end)

      {:ok, {term, rest_tokens, final_ctx}}
    else
      unmatched_tokens when is_list(unmatched_tokens) ->
        {:error,
         "Syntax Error: Expected closing bracket and colon in lambda, found: #{inspect(unmatched_tokens)}"}

      {:error, _} = err ->
        err
    end
  end

  defp parse_typed_vars_with_inference(tokens, acc \\ []) do
    case tokens do
      [{:var, name}, {:comma, _} | rest] ->
        parse_typed_vars_with_inference(rest, acc ++ [{name, Type.fresh_type_var()}])

      [{:var, name}, {:rbracket, _} = rb | rest] ->
        {:ok, {acc ++ [{name, Type.fresh_type_var()}], [rb | rest]}}

      [{:var, name}, {:colon, _} | rest] ->
        case parse_type_tokens(rest) do
          {:ok, {type, [{:comma, _} | rest2]}} ->
            new_acc = acc ++ [{name, type}]
            parse_typed_vars_with_inference(rest2, new_acc)

          {:ok, {type, rest2}} ->
            new_acc = acc ++ [{name, type}]
            {:ok, {new_acc, rest2}}

          {:error, reason} ->
            {:error, reason}
        end

      other ->
        {:error, "Syntax Error: Invalid variable mapping sequence #{inspect(other)}"}
    end
  end

  defp parse_atomic([{:lparen, _} | rest], ctx) do
    with {:ok, {term, rest2, ctx2}} <- parse_formula(rest, ctx) do
      case rest2 do
        [{:rparen, _} | final_rest] ->
          {:ok, {term, final_rest, ctx2}}

        [{type, val} | _] ->
          {:error, "Syntax Error: Expected ')', found '#{val}' (#{inspect(type)})."}

        [] ->
          {:error, "Syntax Error: Missing closing ')'."}
      end
    end
  end

  defp parse_atomic([{:var, name} | rest], ctx) do
    case Context.get_type(ctx, name) do
      nil ->
        new_type = Type.fresh_type_var()
        ctx2 = Context.put_var(ctx, name, new_type)
        {:ok, {{:pre_var, name, new_type}, rest, ctx2}}

      type ->
        {:ok, {{:pre_var, name, type}, rest, ctx}}
    end
  end

  defp parse_atomic([{:atom, name} | rest], ctx) do
    case Context.get_type(ctx, name) do
      nil ->
        new_type = Type.fresh_type_var()
        ctx2 = Context.put_const(ctx, name, new_type)
        {:ok, {{:pre_const, name, new_type}, rest, ctx2}}

      type ->
        {:ok, {{:pre_const, name, type}, rest, ctx}}
    end
  end

  defp parse_atomic([{:system, "$true"} | rest], ctx),
    do: {:ok, {{:pre_const, "$true", Definitions.type_o()}, rest, ctx}}

  defp parse_atomic([{:system, "$false"} | rest], ctx),
    do: {:ok, {{:pre_const, "$false", Definitions.type_o()}, rest, ctx}}

  defp parse_atomic([{:eq, _} | rest], ctx),
    do:
      {:ok,
       {{:pre_const, "=", Type.new(:o, [Type.fresh_type_var(), Type.fresh_type_var()])}, rest,
        ctx}}

  defp parse_atomic([{:neq, _} | rest], ctx),
    do:
      {:ok,
       {{:pre_const, "!=", Type.new(:o, [Type.fresh_type_var(), Type.fresh_type_var()])}, rest,
        ctx}}

  defp parse_atomic([{:equiv, _} | rest], ctx),
    do: {:ok, {{:pre_const, "<=>", Definitions.type_ooo()}, rest, ctx}}

  defp parse_atomic([{:implies, _} | rest], ctx),
    do: {:ok, {{:pre_const, "=>", Definitions.type_ooo()}, rest, ctx}}

  defp parse_atomic([{:implied_by, _} | rest], ctx),
    do: {:ok, {{:pre_const, "<=", Definitions.type_ooo()}, rest, ctx}}

  defp parse_atomic([{:xor, _} | rest], ctx),
    do: {:ok, {{:pre_const, "<~>", Definitions.type_ooo()}, rest, ctx}}

  defp parse_atomic([{:nor, _} | rest], ctx),
    do: {:ok, {{:pre_const, "~|", Definitions.type_ooo()}, rest, ctx}}

  defp parse_atomic([{:nand, _} | rest], ctx),
    do: {:ok, {{:pre_const, "~&", Definitions.type_ooo()}, rest, ctx}}

  defp parse_atomic([{:forall, _} | [{:lbracket, _} | _] = rest], ctx),
    do: parse_quantifier(:pi, rest, ctx)

  defp parse_atomic([{:exists, _} | [{:lbracket, _} | _] = rest], ctx),
    do: parse_quantifier(:sigma, rest, ctx)

  defp parse_atomic([{:pi, _} | [{:lparen, _}, {:lambda, _} | _] = rest], ctx),
    do: parse_quantifier(:pi, rest, ctx)

  defp parse_atomic([{:sigma, _} | [{:lparen, _}, {:lambda, _} | _] = rest], ctx),
    do: parse_quantifier(:sigma, rest, ctx)

  defp parse_atomic([{:pi, _} | rest], ctx) do
    type = Type.new(:o, [Type.new(:o, [Type.fresh_type_var()])])
    {:ok, {{:pre_const, "Π", type}, rest, ctx}}
  end

  defp parse_atomic([{:forall, _} | rest], ctx) do
    type = Type.new(:o, [Type.new(:o, [Type.fresh_type_var()])])
    {:ok, {{:pre_const, "Π", type}, rest, ctx}}
  end

  defp parse_atomic([{:sigma, _} | rest], ctx) do
    type = Type.new(:o, [Type.new(:o, [Type.fresh_type_var()])])
    {:ok, {{:pre_const, "Σ", type}, rest, ctx}}
  end

  defp parse_atomic([{:exists, _} | rest], ctx) do
    type = Type.new(:o, [Type.new(:o, [Type.fresh_type_var()])])
    {:ok, {{:pre_const, "Σ", type}, rest, ctx}}
  end

  defp parse_atomic([{:lambda, _} | rest], ctx), do: parse_lambda(rest, ctx)

  defp parse_atomic([{:not, _} | rest], ctx),
    do: {:ok, {{:pre_const, "~", Definitions.type_oo()}, rest, ctx}}

  defp parse_atomic([{:or, _} | rest], ctx),
    do: {:ok, {{:pre_const, "|", Definitions.type_ooo()}, rest, ctx}}

  defp parse_atomic([{:and, _} | rest], ctx),
    do: {:ok, {{:pre_const, "&", Definitions.type_ooo()}, rest, ctx}}

  defp parse_atomic([token | _rest], _ctx) do
    {type, value} = token
    {:error, "Syntax Error: Expected atomic term, but found token '#{value}' (#{inspect(type)})."}
  end

  defp parse_atomic([], _ctx) do
    {:error, "Syntax Error: Unexpected end of input."}
  end
end
