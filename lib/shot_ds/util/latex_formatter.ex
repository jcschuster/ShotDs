defmodule ShotDs.Util.LatexFormatter do
  @moduledoc ~S"""
  Renders HOL objects as LaTeX.

  Types are printed as subscripts. Logical constants of the signature
  (`⊤`, `⊥`, `¬`, `∧`, `∨`, `⊃`, `≡`, `=`, `∀`, `∃`) are rendered as their
  standard LaTeX symbols without any type annotation. Bound variables are
  reconstructed with fresh names drawn from a type-specific pool, avoiding
  capture with free variables and outer binders. Duplicates are disambiguated
  with running superscripts (subscripts are reserved for the type annotation).

  ## Examples

      iex> import ShotDs.Hol.Dsl
      iex> import ShotDs.Hol.Definitions
      iex> alias ShotDs.Util.LatexFormatter
      iex> t = forall(type_o(), &(true_term() ||| &1))
      ...> # etc.
  """

  alias ShotDs.Data.{Declaration, Problem, Substitution, Term, Type}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.Formatter

  # LaTeX primitives held as `~S`-sigil constants so the module body never
  # writes a raw backslash-in-a-string. Everywhere below, LaTeX is composed by
  # interpolating these attributes into templates.
  @lambda ~S(\lambda)
  @forall ~S(\forall)
  @exists ~S(\exists)
  @neg ~S(\neg)
  @wedge ~S(\wedge)
  @vee ~S(\vee)
  @supset ~S(\supset)
  @equiv ~S(\equiv)
  @top ~S(\top)
  @bot ~S(\bot)
  @mathrm ~S(\mathrm)
  @mathtt ~S(\mathtt)
  @text ~S(\text)
  @tau ~S(\tau)
  @iota ~S(\iota)
  @to ~S( \to )
  @thin ~S(\,)
  @sp ~S(\ )
  @lbrace ~S(\{)
  @rbrace ~S(\})
  @nl ~S(\\)
  @begin_aligned ~S(\begin{aligned})
  @end_aligned ~S(\end{aligned})

  # LaTeX rendering for the logical signature (per `Hol.Definitions.signature/0`).
  # Membership here decides whether a constant is "logical" (types omitted,
  # special infix/prefix layout).
  @logical %{
    "⊤" => @top,
    "⊥" => @bot,
    "¬" => @neg,
    "∧" => @wedge,
    "∨" => @vee,
    "⊃" => @supset,
    "≡" => @equiv,
    "=" => "=",
    "∀" => @forall,
    "∃" => @exists
  }

  @infix ~w(∧ ∨ ⊃ ≡ =)
  @quantifiers ~w(∀ ∃)

  @typedoc ~S"""
  Options accepted by `format/2` and `format!/2`.

    * `:hide_types` — omit type subscripts on non-logical symbols
      (default `false`).
    * `:merge_binder` — collapse `∀(λx. body)` into `∀ x.\, body`
      (default `true`; ignored when `:reconstruct_names` is `false`).
    * `:reconstruct_names` — pick fresh names for bound variables (default
      `true`). When `false`, binders are rendered as `\lambda_{τ}` and bound
      references as `\mathtt{k}_{τ}`, preserving the raw de Bruijn structure.
    * `:math_mode` — one of `:raw` (default), `:inline` (`$…$`) or `:display`
      (`$$…$$`).
  """
  @type opts :: [
          hide_types: boolean(),
          merge_binder: boolean(),
          reconstruct_names: boolean(),
          math_mode: :raw | :inline | :display
        ]

  @typedoc "HOL objects understood by the formatter."
  @type formattable ::
          Type.t()
          | Declaration.t()
          | Term.t()
          | Term.term_id()
          | Substitution.t()
          | Problem.t()

  ##############################################################################
  # PUBLIC API
  ##############################################################################

  @doc """
  Renders the given HOL object as a LaTeX string. Returns `{:ok, result}` or
  `{:error, reason}`.
  """
  @spec format(formattable(), opts()) ::
          {:ok, String.t()} | TF.lookup_error_t() | {:error, :unknown_argument}
  def format(obj, opts \\ [])

  def format(%Type{} = t, opts), do: {:ok, wrap_math(render_type(t), opts)}

  def format(%Declaration{} = d, opts),
    do: {:ok, wrap_math(render_decl(d, opts), opts)}

  def format(%Term{id: id}, opts), do: format(id, opts)

  def format(term_id, opts) when is_integer(term_id) do
    with {:ok, str} <- render_term(term_id, opts), do: {:ok, wrap_math(str, opts)}
  end

  def format(%Substitution{} = s, opts) do
    with {:ok, str} <- render_substitution(s, opts), do: {:ok, wrap_math(str, opts)}
  end

  def format(%Problem{} = p, opts) do
    try do
      {:ok, render_problem(p, opts)}
    rescue
      e in ArgumentError -> {:error, e.message}
    end
  end

  def format(_, _), do: {:error, :unknown_argument}

  @doc """
  Renders the given HOL object as a LaTeX string. Raises on error.
  """
  @spec format!(formattable(), opts()) :: String.t()
  def format!(obj, opts \\ [])

  def format!(%Type{} = t, opts), do: wrap_math(render_type(t), opts)
  def format!(%Declaration{} = d, opts), do: wrap_math(render_decl(d, opts), opts)
  def format!(%Term{id: id}, opts), do: format!(id, opts)

  def format!(term_id, opts) when is_integer(term_id) do
    case render_term(term_id, opts) do
      {:ok, str} -> wrap_math(str, opts)
      {:error, reason} -> raise ArgumentError, message: inspect(reason)
    end
  end

  def format!(%Substitution{} = s, opts) do
    case render_substitution(s, opts) do
      {:ok, str} -> wrap_math(str, opts)
      {:error, reason} -> raise ArgumentError, message: inspect(reason)
    end
  end

  def format!(%Problem{} = p, opts), do: render_problem(p, opts)

  @doc """
  Runs `fun` with a **LaTeX** alias map active. Unlike
  `ShotDs.Util.Formatter.with_aliases/2` — whose values go through
  `escape_name/1` before being spliced into the output — values here
  are used *verbatim* as LaTeX for the corresponding `reference()`
  variable name or type goal. That lets callers hand out proper LaTeX
  identifiers (e.g. `"H^{1}"`, `"\\hat{F}_{2}"`) for fresh metas.

  Falls back through `:hol_aliases` (plain-text nicknames) and finally
  to the `V^{short_ref}`/`\\mathrm{c}^{short_ref}`/`\\tau_{short_ref}`
  defaults for any ref not listed in this map (free variable, constant,
  and type-goal, respectively). Restores the previous binding on exit.

  Only `LatexFormatter` consults `:hol_latex_aliases` — the plain-text
  `Formatter` and `Declaration.format/2` ignore it entirely, so the two
  alias mechanisms don't interfere.
  """
  @spec with_latex_aliases(%{reference() => String.t()}, (-> a)) :: a when a: var
  def with_latex_aliases(aliases, fun) when is_map(aliases) and is_function(fun, 0) do
    prev = Process.get(:hol_latex_aliases)
    Process.put(:hol_latex_aliases, aliases)

    try do
      fun.()
    after
      case prev do
        nil -> Process.delete(:hol_latex_aliases)
        m -> Process.put(:hol_latex_aliases, m)
      end
    end
  end

  ##############################################################################
  # TYPES
  ##############################################################################

  # Uncurried `%Type{goal, args}` prints right-associatively.
  # `Type.new(:o, [:i, :i])` → "\iota \to \iota \to o".
  defp render_type(%Type{goal: g, args: []}), do: render_goal(g)

  defp render_type(%Type{goal: g, args: args}) do
    (args ++ [Type.new(g)])
    |> Enum.map_join(@to, &render_type_atom/1)
  end

  # An arrow's left-hand side needs parentheses when it is itself an arrow.
  defp render_type_atom(%Type{args: []} = t), do: render_type(t)
  defp render_type_atom(%Type{} = t), do: "(#{render_type(t)})"

  defp render_goal(:o), do: "o"
  defp render_goal(:i), do: @iota
  defp render_goal(atom) when is_atom(atom), do: "#{@mathrm}{#{Atom.to_string(atom)}}"

  defp render_goal(ref) when is_reference(ref) do
    case Process.get(:hol_latex_aliases, %{}) do
      %{^ref => latex} when is_binary(latex) ->
        latex

      _ ->
        case Process.get(:hol_aliases, %{}) do
          %{^ref => nick} -> nick
          _ -> "#{@tau}_{#{Formatter.short_ref(ref)}}"
        end
    end
  end

  ##############################################################################
  # DECLARATIONS
  ##############################################################################

  # Renders a declaration standalone (used for substitutions and free vars in
  # term rendering). Bound-variable declarations aren't rendered by this
  # function during term walking: the term walker resolves them via the binder
  # stack (or via `\mathtt{k}` in raw-index mode).
  defp render_decl(%Declaration{kind: :co, name: name, type: type}, opts) do
    case Map.fetch(@logical, name) do
      {:ok, latex} -> latex
      :error -> attach_type(render_const_name(name), type, opts)
    end
  end

  defp render_decl(%Declaration{kind: :fv, name: name, type: type}, opts) do
    attach_type(render_var_name(name), type, opts)
  end

  defp render_decl(%Declaration{kind: :bv, name: k, type: type}, opts) do
    attach_type("#{@mathtt}{#{k}}", type, opts)
  end

  defp render_var_name(name) when is_binary(name), do: escape_name(name)

  # Anonymous free variable (fresh ref, e.g. γ-instantiation). Disambiguator
  # goes in a *superscript* so the type subscript added by `attach_type` still
  # composes into valid LaTeX (`V^{shortref}_{τ}`).
  defp render_var_name(ref) when is_reference(ref) do
    resolve_ref_name(ref, fn short -> "V^{#{short}}" end)
  end

  defp render_var_name(n) when is_integer(n), do: Integer.to_string(n)

  # Constants named by refs come from Skolemization (δ-rule). Same
  # composition trick as for free-var refs; roman font marks the constant.
  defp render_const_name(name) when is_binary(name),
    do: "#{@mathrm}{#{escape_name(name)}}"

  defp render_const_name(ref) when is_reference(ref) do
    resolve_ref_name(ref, fn short -> "#{@mathrm}{c}^{#{short}}" end)
  end

  # LaTeX alias first, plain nickname second, `default_fun` last.
  defp resolve_ref_name(ref, default_fun) do
    case Process.get(:hol_latex_aliases, %{}) do
      %{^ref => latex} when is_binary(latex) ->
        latex

      _ ->
        case Process.get(:hol_aliases, %{}) do
          %{^ref => nick} -> escape_name(nick)
          _ -> default_fun.(Formatter.short_ref(ref))
        end
    end
  end

  # LaTeX-escape the small set of characters that would otherwise break math
  # mode. Most identifiers used here are alphanumeric or Unicode operators
  # already handled by the logical map.
  defp escape_name(name) do
    name
    |> to_string()
    |> String.replace("_", ~S(\_))
    |> String.replace("#", ~S(\#))
    |> String.replace("$", ~S(\$))
    |> String.replace("%", ~S(\%))
    |> String.replace("&", ~S(\&))
    |> String.replace("{", @lbrace)
    |> String.replace("}", @rbrace)
  end

  defp attach_type(head, type, opts) do
    if Keyword.get(opts, :hide_types, false) do
      head
    else
      "#{head}_{#{render_type(type)}}"
    end
  end

  ##############################################################################
  # TERM RENDERING
  ##############################################################################

  # Top-down descent maintaining a binder-name stack (innermost at head) and a
  # taboo set (names already reserved). Shared subterms aren't memoized: their
  # rendering depends on the surrounding binder context.
  defp render_term(term_id, opts) do
    with {:ok, term} <- TF.get_term(term_id) do
      taboo =
        MapSet.new()
        |> MapSet.union(free_var_names(term))
        |> MapSet.union(logical_names())

      env = %{stack: [], taboo: taboo, opts: opts}

      try do
        {:ok, do_render(term_id, env)}
      rescue
        ArgumentError -> {:error, :non_existing_id}
      end
    end
  end

  defp do_render(term_id, env) do
    term = TF.get_term!(term_id)
    {binder_names, env_inside} = reserve_binders(term.bvars, env)
    render_after_binders(term, binder_names, env_inside)
  end

  # Rendering the "already-stripped" body of a term: takes the head, args and
  # the environment (with any bvars already reserved by the caller). Runs the
  # quantifier-merge check and falls back to the default λ-wrapper.
  defp render_after_binders(
         %Term{bvars: bvars, head: head, args: args},
         binder_names,
         env
       ) do
    # Merging is only meaningful when we can name the bound variable — with
    # raw indices it would produce `\forall_{τ}. \mathtt{1}` which just
    # obscures the constructor structure without helping readability.
    merge? = Keyword.get(env.opts, :merge_binder, true) and reconstruct?(env.opts)

    core =
      case try_merge_quantifier(merge?, head, args, env) do
        {:ok, merged} -> merged
        :none -> render_spine(head, args, env)
      end

    wrap_binders(binder_names, bvars, core, env.opts)
  end

  defp wrap_binders([], _bvars, core, _opts), do: core

  defp wrap_binders(names, bvars, core, opts) do
    if reconstruct?(opts) do
      "#{@lambda} #{render_binder_list(names, bvars, opts)}.#{@thin}#{core}"
    else
      "#{render_raw_binders(bvars, opts)}.#{@thin}#{core}"
    end
  end

  defp render_binder_list(names, bvars, opts) do
    names
    |> Enum.zip(bvars)
    |> Enum.map_join(@sp, fn {name, %Declaration{type: t}} ->
      attach_type(name, t, opts)
    end)
  end

  # Raw mode: emit one `\lambda_{τ}` per binder, no names.
  defp render_raw_binders(bvars, opts) do
    hide? = Keyword.get(opts, :hide_types, false)

    Enum.map_join(bvars, @sp, fn %Declaration{type: t} ->
      if hide?, do: @lambda, else: "#{@lambda}_{#{render_type(t)}}"
    end)
  end

  defp reconstruct?(opts), do: Keyword.get(opts, :reconstruct_names, true)

  ##############################################################################
  # Quantifier + λ merging (recursive: chains like ∀x. ∀y. … collapse fully).
  ##############################################################################

  defp try_merge_quantifier(
         true,
         %Declaration{kind: :co, name: q},
         [arg_id],
         env
       )
       when q in @quantifiers do
    %Term{bvars: inner_bvars} = arg = TF.get_term!(arg_id)

    case inner_bvars do
      [] ->
        :none

      _ ->
        {names, env_inside} = reserve_binders(inner_bvars, env)
        binder_str = render_binder_list(names, inner_bvars, env_inside.opts)
        body = render_after_binders(%{arg | bvars: []}, [], env_inside)
        quant = Map.fetch!(@logical, q)
        {:ok, "#{quant} #{binder_str}.#{@thin}#{body}"}
    end
  end

  defp try_merge_quantifier(_, _, _, _), do: :none

  # `render_spine` decides how the head combines with its arguments.
  defp render_spine(%Declaration{kind: :co, name: name} = head, args, env)
       when name in @infix do
    case args do
      [a, b] ->
        left = do_render_arg(a, env)
        right = do_render_arg(b, env)
        op = Map.fetch!(@logical, name)
        "#{parens_if_complex(left)} #{op} #{parens_if_complex(right)}"

      _ ->
        render_generic_head(head, args, env)
    end
  end

  defp render_spine(%Declaration{kind: :co, name: "¬"} = head, args, env) do
    case args do
      [a] ->
        "#{@neg} #{parens_if_complex(do_render_arg(a, env))}"

      _ ->
        render_generic_head(head, args, env)
    end
  end

  defp render_spine(head, args, env), do: render_generic_head(head, args, env)

  defp render_generic_head(%Declaration{kind: :bv, name: k, type: t}, args, env) do
    head_str =
      if reconstruct?(env.opts) do
        Enum.at(env.stack, k - 1) || "#{@text}{?bv}#{k}"
      else
        attach_type("#{@mathtt}{#{k}}", t, env.opts)
      end

    case args do
      [] -> head_str
      _ -> "#{head_str}~#{render_args(args, env)}"
    end
  end

  defp render_generic_head(head, args, env) do
    head_str = render_decl(head, env.opts)

    case args do
      [] -> head_str
      _ -> "#{head_str}~#{render_args(args, env)}"
    end
  end

  defp render_args(args, env) do
    args
    |> Enum.map_join("~", fn id ->
      id |> do_render_arg(env) |> parens_if_complex()
    end)
  end

  # Wraps `render` producing a `{str, complex?}` pair so the caller can decide
  # whether to parenthesise.
  defp do_render_arg(term_id, env) do
    %Term{bvars: bvars, args: args} = TF.get_term!(term_id)
    complex? = bvars != [] or args != []
    {do_render(term_id, env), complex?}
  end

  defp parens_if_complex({str, false}), do: str
  defp parens_if_complex({str, true}), do: "(#{str})"

  ##############################################################################
  # BINDER NAME RESERVATION
  ##############################################################################

  # `bvars` is stored outermost-first. We assign fresh names in that order (so
  # the printed sequence `λx y z. …` matches), then push them onto `stack`
  # innermost-first so that a bound reference `%Declaration{name: k}` looks up
  # via `Enum.at(stack, k - 1)`.
  defp reserve_binders(bvars, env) do
    {names_rev, taboo_out} =
      Enum.reduce(bvars, {[], env.taboo}, fn %Declaration{type: t}, {acc, tab} ->
        {name, tab_next} = fresh_name(t, tab)
        {[name | acc], tab_next}
      end)

    names = Enum.reverse(names_rev)
    new_stack = Enum.reverse(names) ++ env.stack
    {names, %{env | stack: new_stack, taboo: taboo_out}}
  end

  # First try the pool for this type. If everything in the pool is taboo, use
  # its first element and append running superscripts until we find a free
  # slot. Subscripts are reserved for the type annotation, so we superscript.
  defp fresh_name(type, taboo) do
    pool = pool_for(type)
    do_fresh(pool, pool, taboo)
  end

  defp do_fresh([name | rest], full_pool, taboo) do
    if MapSet.member?(taboo, name) do
      do_fresh(rest, full_pool, taboo)
    else
      {name, MapSet.put(taboo, name)}
    end
  end

  defp do_fresh([], full_pool, taboo), do: do_superscript(full_pool, 1, taboo)

  defp do_superscript([base | _] = pool, n, taboo) do
    candidate = "#{base}^{#{n}}"

    if MapSet.member?(taboo, candidate) do
      do_superscript(pool, n + 1, taboo)
    else
      {candidate, MapSet.put(taboo, candidate)}
    end
  end

  # Pool selection based on the shape of the binder's type. All variable names
  # are uppercase by convention (TPTP-style: variables uppercase, constants
  # lowercase). No special fonts; the taboo mechanism disambiguates via
  # superscripts.
  defp pool_for(%Type{goal: :i, args: []}), do: ~w(X Y Z U V W)
  defp pool_for(%Type{goal: :o, args: []}), do: ~w(P Q R S)
  defp pool_for(%Type{goal: :o, args: [_]}), do: ~w(P Q R S)
  defp pool_for(%Type{goal: :o, args: [_, _ | _]}), do: ~w(R S T U)
  defp pool_for(%Type{goal: g, args: [_ | _]}) when g != :o, do: ~w(F G H K)
  defp pool_for(%Type{}), do: ~w(X Y Z W)

  ##############################################################################
  # TABOO SET
  ##############################################################################

  defp free_var_names(%Term{fvars: fvars}) do
    fvars
    |> Enum.map(& &1.name)
    |> Enum.filter(&is_binary/1)
    |> MapSet.new()
  end

  defp logical_names, do: @logical |> Map.keys() |> MapSet.new()

  ##############################################################################
  # SUBSTITUTIONS
  ##############################################################################

  defp render_substitution(%Substitution{fvar: fvar, term_id: term_id}, opts) do
    with {:ok, term_str} <- render_term(term_id, opts) do
      var_str = render_decl(fvar, opts)
      {:ok, "[#{var_str} \mapsto #{term_str}]"}
    end
  end

  ##############################################################################
  # PROBLEMS
  ##############################################################################

  defp render_problem(
         %Problem{
           path: path,
           includes: includes,
           types: types,
           definitions: defs,
           axioms: axioms,
           conjecture: conjecture
         },
         opts
       ) do
    header = "% Problem #{if path in ["", "memory"], do: "<unnamed>", else: path}"

    sections =
      [
        includes_section(includes),
        types_section(types, opts),
        defs_section(defs, opts),
        axioms_section(axioms, opts),
        conjecture_section(conjecture, opts)
      ]
      |> Enum.reject(&(&1 == ""))

    Enum.join([header | sections], "\n")
  end

  defp includes_section([]), do: ""

  defp includes_section(includes),
    do: "% includes: " <> Enum.join(includes, ", ")

  defp types_section([], _opts), do: ""

  defp types_section(types, opts) do
    body =
      Enum.map_join(types, ", ", fn
        {name, :base_type} ->
          "#{@mathrm}{#{escape_name(name)}}#{@text}{ (base)}"

        {name, type} ->
          "#{@mathrm}{#{escape_name(name)}} : #{render_type(type)}"
      end)

    wrap_math("#{@text}{Types: } #{body}", opts)
  end

  defp defs_section([], _opts), do: ""

  defp defs_section(defs, opts) do
    body =
      Enum.map_join(defs, "#{@nl}\n", fn {decl, term_id} ->
        {:ok, term_str} = render_term(term_id, opts)
        "#{render_decl(decl, opts)} := #{term_str}"
      end)

    wrap_math("#{@begin_aligned}\n#{body}\n#{@end_aligned}", opts)
  end

  defp axioms_section([], _opts), do: ""

  defp axioms_section(axioms, opts) do
    body =
      Enum.map_join(axioms, "#{@nl}\n", fn {name, term_id} ->
        {:ok, term_str} = render_term(term_id, opts)
        "#{@text}{#{escape_name(name)}}:#{@sp}#{term_str}"
      end)

    wrap_math("#{@begin_aligned}\n#{body}\n#{@end_aligned}", opts)
  end

  defp conjecture_section(nil, _opts), do: ""

  defp conjecture_section({name, term_id}, opts) do
    {:ok, term_str} = render_term(term_id, opts)
    wrap_math("#{@text}{Conjecture #{escape_name(name)}}:#{@sp}#{term_str}", opts)
  end

  ##############################################################################
  # MATH-MODE WRAPPING
  ##############################################################################

  defp wrap_math(str, opts) do
    case Keyword.get(opts, :math_mode, :raw) do
      :raw -> str
      :inline -> "$#{str}$"
      :display -> "$$#{str}$$"
    end
  end
end
