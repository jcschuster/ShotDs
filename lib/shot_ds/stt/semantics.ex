defmodule ShotDs.Stt.Semantics do
  @moduledoc """
  Implements the semantics of Church's simple type theory. The most important
  functions are `subst/2` and `subst!/2`, which apply substitutions to a given
  term, and `unfold_defs/2` and `unfold_defs!/2`, which unfold (possibly
  polymorphic) constant definitions while instantiating their type variables
  according to each occurrence's monotype.
  """

  alias ShotDs.Data.{Type, Declaration, Term, Substitution}
  alias ShotDs.Stt.TermFactory, as: TF
  alias ShotDs.Util.TypeInference
  import ShotDs.Util.TermTraversal

  ##############################################################################
  # SUBSTITUTION LOGIC
  ##############################################################################

  @doc """
  Applies a singular substitution or a list of substitutions left to right to
  the term with the given id, propagating any lookup or type errors.
  """
  @spec subst([Substitution.t()] | Substitution.t(), Term.term_id()) ::
          {:ok, Term.term_id()} | TF.lookup_error_t() | {:error, :incompatible_types}
  def subst(substitutions, term_id)

  def subst([s | ss], term_id) do
    with {:ok, next_id} <- subst(s, term_id), do: subst(ss, next_id)
  end

  def subst([], term_id), do: {:ok, term_id}

  def subst(%Substitution{fvar: fvar, term_id: replacement_id}, term_id) do
    update_env = fn term, depth -> depth + length(term.bvars) end
    short_circuit = fn term, _depth -> fvar not in term.fvars end

    transform = fn term, new_args, depth, acc_cache ->
      if term.head == fvar do
        subst_matched(term, new_args, depth, replacement_id, fvar, acc_cache)
      else
        subst_unmatched(term, new_args, acc_cache)
      end
    end

    case map_term(term_id, 0, update_env, transform, short_circuit) do
      {:ok, {new_id, _cache}} -> {:ok, new_id}
      error -> error
    end
  end

  defp subst_matched(
         %Term{fvars: fvars, bvars: bvars},
         new_args,
         depth,
         replacement_id,
         fvar,
         acc_cache
       ) do
    shift_cache = Map.get(acc_cache, {:shift_cache, depth}, %{})

    with {:ok, {shifted_replacement_id, next_shift_cache}} <-
           shift(replacement_id, depth, 0, shift_cache),
         {:ok, reduced_id} <- TF.fold_apply(shifted_replacement_id, new_args),
         {:ok, %Term{bvars: red_bvars, fvars: red_fvars} = reduced_body} <-
           TF.get_term(reduced_id),
         shifted_bvars = Enum.map(bvars, fn bv -> %{bv | name: bv.name + length(red_bvars)} end),
         combined_bvars = shifted_bvars ++ red_bvars,
         {:ok, new_max_num} <-
           calc_new_max_num(reduced_body.head, reduced_body.args, combined_bvars),
         {:ok, new_tvars} <-
           calc_new_tvars(reduced_body.head, reduced_body.args, combined_bvars) do
      final_fvars = Enum.uniq(List.delete(fvars, fvar) ++ red_fvars)
      new_type = Type.new(reduced_body.type, Enum.map(bvars, & &1.type))

      wrapped_term = %Term{
        reduced_body
        | bvars: combined_bvars,
          fvars: final_fvars,
          tvars: new_tvars,
          type: new_type,
          max_num: new_max_num
      }

      final_acc_cache = Map.put(acc_cache, {:shift_cache, depth}, next_shift_cache)

      {{:ok, TF.memoize(wrapped_term)}, final_acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  defp subst_unmatched(term, new_args, acc_cache) do
    with {:ok, new_fvars} <- calc_new_fvars(term.head, new_args),
         {:ok, new_tvars} <- calc_new_tvars(term.head, new_args, term.bvars),
         {:ok, new_max_num} <- calc_new_max_num(term.head, new_args, term.bvars) do
      new_term = %{
        term
        | args: new_args,
          fvars: new_fvars,
          tvars: new_tvars,
          max_num: new_max_num
      }

      {{:ok, TF.memoize(new_term)}, acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  @doc """
  Applies a singular substitution or a list of substitutions left to right to
  the term with the given id, erroring out if it encounters an invalid ID.
  """
  @spec subst!([Substitution.t()] | Substitution.t(), Term.term_id()) :: Term.term_id()
  def subst!(substitutions, term_id) do
    case subst(substitutions, term_id) do
      {:ok, new_id} -> new_id
      {:error, reason} -> raise ArgumentError, message: inspect(reason)
    end
  end

  @doc """
  Adds a new substitution to a list of substitutions by applying it to every
  member and prepending it, propagating errors.
  """
  @spec add_subst([Substitution.t()], Substitution.t()) ::
          {:ok, [Substitution.t()]} | TF.lookup_error_t()
  def add_subst(substs, %Substitution{} = new_subst) do
    Enum.reduce_while(substs, {:ok, [new_subst]}, fn s, {:ok, acc} ->
      case subst(new_subst, s.term_id) do
        {:ok, new_id} -> {:cont, {:ok, [%{s | term_id: new_id} | acc]}}
        error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, rev_acc} -> {:ok, Enum.reverse(rev_acc)}
      error -> error
    end
  end

  @doc """
  Adds a new substitution to a list of substitutions by applying it to every
  member and prepending it, raising on errors.
  """
  @spec add_subst!([Substitution.t()], Substitution.t()) :: [Substitution.t()]
  def add_subst!(substs, %Substitution{} = new_subst) do
    applied =
      Enum.map(substs, fn %Substitution{term_id: t_id} = s ->
        %{s | term_id: subst!(new_subst, t_id)}
      end)

    [new_subst | applied]
  end

  ##############################################################################
  # SHIFT AND INSTANTIATION
  ##############################################################################

  @doc """
  Applies a *d*-shift above cutoff *c* to the term with the given id.
  """
  @spec shift(Term.term_id(), integer(), non_neg_integer(), map()) ::
          {:ok, {Term.term_id(), map()}} | TF.lookup_error_t()
  def shift(term_id, d, c \\ 0, cache \\ %{}) do
    update_env = fn term, current_c -> current_c + length(term.bvars) end

    transform = fn %Term{head: head, bvars: bvars} = term, new_args, current_c, acc_cache ->
      new_head =
        case head do
          %Declaration{kind: :bv, name: index, type: type} when index > current_c ->
            Declaration.new_bound_var(index + d, type)

          decl ->
            decl
        end

      case calc_new_max_num(new_head, new_args, bvars) do
        {:ok, new_max_num} ->
          new_term = %Term{term | head: new_head, args: new_args, max_num: new_max_num}
          {{:ok, TF.memoize(new_term)}, acc_cache}

        error ->
          {error, acc_cache}
      end
    end

    short_circuit = fn term, current_c -> term.max_num <= current_c end

    map_term(term_id, c, update_env, transform, short_circuit, cache)
  end

  @doc """
  Applies a *d*-shift above cutoff *c* to the term with the given id, raising on
  invalid IDs.
  """
  @spec shift!(Term.term_id(), integer(), non_neg_integer(), map()) :: {Term.term_id(), map()}
  def shift!(term_id, d, c \\ 0, cache \\ %{}) do
    case shift(term_id, d, c, cache) do
      {:ok, {new_id, final_cache}} -> {new_id, final_cache}
      {:error, reason} -> raise ArgumentError, message: inspect(reason)
    end
  end

  @doc """
  Instantiates the bound variable with index *k* with the replacement term
  corresponding to the given id, safely propagating errors.
  """
  @spec instantiate(Term.term_id(), pos_integer(), Term.term_id(), map()) ::
          {:ok, {Term.term_id(), map()}} | TF.lookup_error_t() | {:error, :incompatible_types}
  def instantiate(term_id, k, replacement_id, cache \\ %{}) do
    update_env = fn term, current_k -> current_k + length(term.bvars) end

    transform = fn term, new_args, current_k, acc_cache ->
      instantiate_transform(term, new_args, current_k, acc_cache, k, replacement_id)
    end

    map_term(term_id, k, update_env, transform, fn _, _ -> false end, cache)
  end

  defp instantiate_transform(
         %Term{head: %Declaration{kind: :bv, name: index}, bvars: bvars},
         new_args,
         current_k,
         acc_cache,
         k,
         replacement_id
       )
       when index == current_k do
    shift_amount = current_k - k
    shift_cache = Map.get(acc_cache, {:shift_cache, shift_amount}, %{})

    with {:ok, {shifted_replacement_id, next_shift_cache}} <-
           shift(replacement_id, shift_amount, 0, shift_cache),
         {:ok, reduced_body_id} <- TF.fold_apply(shifted_replacement_id, new_args),
         {:ok, %Term{bvars: red_bvars, max_num: red_max} = reduced_body} <-
           TF.get_term(reduced_body_id),
         {:ok, new_tvars} <-
           calc_new_tvars(reduced_body.head, reduced_body.args, red_bvars ++ bvars) do
      shifted_bvars = Enum.map(bvars, fn bv -> %{bv | name: bv.name + length(red_bvars)} end)
      combined_bvars = shifted_bvars ++ red_bvars

      new_type = Type.new(reduced_body.type, Enum.map(bvars, & &1.type))

      bvar_maxes = Enum.map(combined_bvars, & &1.name)
      new_max_num = Enum.max([red_max | bvar_maxes], fn -> 0 end)

      wrapped_term = %Term{
        reduced_body
        | bvars: combined_bvars,
          type: new_type,
          tvars: new_tvars,
          max_num: new_max_num
      }

      final_acc_cache = Map.put(acc_cache, {:shift_cache, shift_amount}, next_shift_cache)

      {{:ok, TF.memoize(wrapped_term)}, final_acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  defp instantiate_transform(
         %Term{head: %Declaration{kind: :bv, name: index, type: type}, bvars: bvars} = term,
         new_args,
         current_k,
         acc_cache,
         _k,
         _replacement_id
       )
       when index > current_k do
    new_head = Declaration.new_bound_var(index - 1, type)

    with {:ok, new_max_num} <- calc_new_max_num(new_head, new_args, bvars),
         {:ok, new_fvars} <- calc_new_fvars(new_head, new_args),
         {:ok, new_tvars} <- calc_new_tvars(new_head, new_args, bvars) do
      new_term = %Term{
        term
        | head: new_head,
          args: new_args,
          fvars: new_fvars,
          tvars: new_tvars,
          max_num: new_max_num
      }

      {{:ok, TF.memoize(new_term)}, acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  defp instantiate_transform(
         %Term{head: head_decl, bvars: bvars} = term,
         new_args,
         _current_k,
         acc_cache,
         _k,
         _replacement_id
       ) do
    with {:ok, new_max_num} <- calc_new_max_num(head_decl, new_args, bvars),
         {:ok, new_fvars} <- calc_new_fvars(head_decl, new_args),
         {:ok, new_tvars} <- calc_new_tvars(head_decl, new_args, bvars) do
      new_term = %Term{
        term
        | args: new_args,
          fvars: new_fvars,
          tvars: new_tvars,
          max_num: new_max_num
      }

      {{:ok, TF.memoize(new_term)}, acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  @doc """
  Instantiates the bound variable with index *k* with the replacement term
  corresponding to the given id, raising on errors. Uses caching for efficient
  computation.
  """
  @spec instantiate!(Term.term_id(), pos_integer(), Term.term_id(), map()) ::
          {Term.term_id(), map()}
  def instantiate!(term_id, k, replacement_id, cache \\ %{}) do
    case instantiate(term_id, k, replacement_id, cache) do
      {:ok, {new_id, final_cache}} -> {new_id, final_cache}
      {:error, reason} -> raise ArgumentError, message: inspect(reason)
    end
  end

  ##############################################################################
  # TYPE SUBSTITUTION & POLYMORPHIC UNFOLDING
  ##############################################################################

  @doc """
  Applies a type substitution (a map from type-variable references to types) to
  every type appearing in the term with the given id, propagating any lookup
  errors.

  This rewrites the head, the bound and free variables, and the term-level
  type, while leaving the term's tree-structure - i.e. its de Bruijn indices
  and abstraction nesting - untouched. Subterms whose `:tvars` field shares no
  element with the substitution's domain are skipped via short-circuit, so the
  cost of `subst_types/2` is proportional to the part of the term that
  actually mentions the substituted variables.
  """
  @spec subst_types(Term.term_id(), TypeInference.type_substitution()) ::
          {:ok, Term.term_id()} | TF.lookup_error_t()
  def subst_types(term_id, type_subst) when is_map(type_subst) and map_size(type_subst) == 0 do
    {:ok, term_id}
  end

  def subst_types(term_id, type_subst) when is_map(type_subst) do
    domain = MapSet.new(Map.keys(type_subst))

    update_env = fn _term, env -> env end

    short_circuit = fn term, _env ->
      Enum.all?(term.tvars, fn tv -> not MapSet.member?(domain, tv) end)
    end

    transform = &subst_types_transform(&1, &2, &3, &4, type_subst)

    case map_term(term_id, nil, update_env, transform, short_circuit) do
      {:ok, {new_id, _cache}} -> {:ok, new_id}
      error -> error
    end
  end

  defp subst_types_transform(term, new_args, _env, acc_cache, type_subst) do
    new_head = subst_decl_type(term.head, type_subst)
    new_bvars = Enum.map(term.bvars, &subst_decl_type(&1, type_subst))
    new_type = TypeInference.apply_subst(term.type, type_subst)

    with {:ok, new_fvars} <- calc_new_fvars(new_head, new_args),
         {:ok, new_max_num} <- calc_new_max_num(new_head, new_args, new_bvars),
         {:ok, new_tvars} <- calc_new_tvars(new_head, new_args, new_bvars) do
      new_term = %{
        term
        | head: new_head,
          args: new_args,
          type: new_type,
          bvars: new_bvars,
          fvars: new_fvars,
          tvars: new_tvars,
          max_num: new_max_num
      }

      {{:ok, TF.memoize(new_term)}, acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  @doc """
  Like `subst_types/2`, but raises on invalid IDs.
  """
  @spec subst_types!(Term.term_id(), TypeInference.type_substitution()) :: Term.term_id()
  def subst_types!(term_id, type_subst) do
    case subst_types(term_id, type_subst) do
      {:ok, new_id} -> new_id
      {:error, reason} -> raise ArgumentError, message: inspect(reason)
    end
  end

  @doc ~S"""
  Unfolds occurrences of all defined constants in `target_id` by replacing
  each occurrence with a type-instantiated, β-reduced copy of the
  corresponding definition body.

  The `defs` map associates polymorphic (or monomorphic) constant declarations
  with their definition bodies. Polymorphism is implicit: any free type
  variables appearing in a declaration's stored type are treated as
  universally quantified scheme variables, and the same variables are expected
  to occur in the corresponding definition body. At each occurrence of a
  defined constant, the declaration's polymorphic type is matched against the
  occurrence's instance type to derive a type substitution, which is applied
  to the definition body via `subst_types/2` before β-reducing it with the
  occurrence's arguments.

  Lookup is by constant name: each declaration is keyed in `defs` by its full
  struct, but only its `:name` is consulted at occurrences (since the type at
  each occurrence is the instance, not the polymorphic, type).

  For a monomorphic declaration (no free type variables in its stored type)
  this degenerates to constant rewriting analogous to free variable
  substitution via `subst/2`.

  Returns `{:ok, target_id}` immediately when `defs` is empty.
  """
  @spec unfold_defs(Term.term_id(), %{Declaration.const_t() => Term.term_id()}) ::
          {:ok, Term.term_id()}
          | TF.lookup_error_t()
          | {:error, :incompatible_types}
          | {:error, String.t()}
  def unfold_defs(target_id, defs) when is_map(defs) do
    if map_size(defs) == 0 do
      {:ok, target_id}
    else
      by_name =
        Map.new(defs, fn {%Declaration{kind: :co, name: name} = decl, def_id} ->
          {name, {decl, def_id}}
        end)

      update_env = fn term, depth -> depth + length(term.bvars) end
      short_circuit = fn _term, _depth -> false end

      transform = &unfold_transform(&1, &2, &3, &4, by_name)

      case map_term(target_id, 0, update_env, transform, short_circuit) do
        {:ok, {new_id, _cache}} -> {:ok, new_id}
        error -> error
      end
    end
  end

  defp unfold_transform(term, new_args, depth, acc_cache, by_name) do
    case term.head do
      %Declaration{kind: :co, name: name} ->
        case Map.get(by_name, name) do
          nil ->
            subst_unmatched(term, new_args, acc_cache)

          {polymorphic_decl, definition_id} ->
            unfold_at(term, new_args, depth, polymorphic_decl, definition_id, acc_cache)
        end

      _ ->
        subst_unmatched(term, new_args, acc_cache)
    end
  end

  @doc """
  Like `unfold_defs/2`, but raises on invalid IDs or matching failures.
  """
  @spec unfold_defs!(Term.term_id(), %{Declaration.const_t() => Term.term_id()}) ::
          Term.term_id()
  def unfold_defs!(target_id, defs) do
    case unfold_defs(target_id, defs) do
      {:ok, new_id} -> new_id
      {:error, reason} -> raise ArgumentError, message: inspect(reason)
    end
  end

  defp unfold_at(
         %Term{head: const_decl, bvars: bvars, fvars: fvars},
         new_args,
         depth,
         polymorphic_decl,
         definition_id,
         acc_cache
       ) do
    shift_cache = Map.get(acc_cache, {:shift_cache, depth}, %{})

    with {:ok, type_subst} <- match_decl(polymorphic_decl, const_decl.type),
         {:ok, instantiated_def_id} <- subst_types(definition_id, type_subst),
         {:ok, {shifted_def_id, next_shift_cache}} <-
           shift(instantiated_def_id, depth, 0, shift_cache),
         {:ok, reduced_id} <- TF.fold_apply(shifted_def_id, new_args),
         {:ok, %Term{bvars: red_bvars, fvars: red_fvars} = reduced_body} <-
           TF.get_term(reduced_id),
         shifted_bvars =
           Enum.map(bvars, fn bv -> %{bv | name: bv.name + length(red_bvars)} end),
         combined_bvars = shifted_bvars ++ red_bvars,
         {:ok, new_max_num} <-
           calc_new_max_num(reduced_body.head, reduced_body.args, combined_bvars),
         {:ok, new_tvars} <-
           calc_new_tvars(reduced_body.head, reduced_body.args, combined_bvars) do
      final_fvars = Enum.uniq(fvars ++ red_fvars)
      new_type = Type.new(reduced_body.type, Enum.map(bvars, & &1.type))

      wrapped_term = %Term{
        reduced_body
        | bvars: combined_bvars,
          fvars: final_fvars,
          tvars: new_tvars,
          type: new_type,
          max_num: new_max_num
      }

      final_acc_cache = Map.put(acc_cache, {:shift_cache, depth}, next_shift_cache)

      {{:ok, TF.memoize(wrapped_term)}, final_acc_cache}
    else
      error -> {error, acc_cache}
    end
  end

  # Computes a type substitution σ such that
  # `apply_subst(polymorphic_decl.type, σ) == instance_type`, restricted to the
  # free type variables of the polymorphic declaration's stored type.
  #
  # The free type variables of `polymorphic_decl.type` are unique references
  # that don't appear in `instance_type` (which is fully concrete at the
  # occurrence), so plain unification followed by domain restriction produces
  # the desired matching substitution.
  @spec match_decl(Declaration.const_t(), Type.t()) ::
          {:ok, TypeInference.type_substitution()} | {:error, String.t()}
  defp match_decl(%Declaration{type: poly_type}, instance_type) do
    scheme_vars = Type.free_type_vars(poly_type)

    if MapSet.size(scheme_vars) == 0 do
      {:ok, %{}}
    else
      case TypeInference.unify(poly_type, instance_type, %{}) do
        {:ok, subst} -> {:ok, Map.take(subst, MapSet.to_list(scheme_vars))}
        {:error, _} = err -> err
      end
    end
  end

  defp subst_decl_type(%Declaration{type: type} = decl, type_subst) do
    %{decl | type: TypeInference.apply_subst(type, type_subst)}
  end

  ##############################################################################
  # HELPERS
  ##############################################################################

  defp calc_new_max_num(head_decl, arg_ids, bvars) do
    head_max =
      case head_decl do
        %Declaration{kind: :bv, name: n} -> n
        _ -> 0
      end

    bvar_maxes = Enum.map(bvars, & &1.name)

    Enum.reduce_while(arg_ids, {:ok, []}, fn id, {:ok, acc} ->
      case TF.get_term(id) do
        {:ok, term} -> {:cont, {:ok, [term.max_num | acc]}}
        error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, arg_maxes} -> {:ok, Enum.max([head_max | arg_maxes ++ bvar_maxes], fn -> 0 end)}
      error -> error
    end
  end

  defp calc_new_fvars(head_decl, arg_ids) do
    head_fvars =
      case head_decl do
        %Declaration{kind: :fv} -> [head_decl]
        _ -> []
      end

    Enum.reduce_while(arg_ids, {:ok, []}, fn id, {:ok, acc} ->
      case TF.get_term(id) do
        {:ok, term} -> {:cont, {:ok, [term.fvars | acc]}}
        error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, nested_fvars} -> {:ok, Enum.uniq(head_fvars ++ List.flatten(nested_fvars))}
      error -> error
    end
  end

  defp calc_new_tvars(head_decl, arg_ids, bvars) do
    head_tvars = Type.free_type_vars(head_decl.type) |> MapSet.to_list()

    bvar_tvars =
      Enum.flat_map(bvars, fn bv ->
        Type.free_type_vars(bv.type) |> MapSet.to_list()
      end)

    Enum.reduce_while(arg_ids, {:ok, []}, fn id, {:ok, acc} ->
      case TF.get_term(id) do
        {:ok, term} -> {:cont, {:ok, [term.tvars | acc]}}
        error -> {:halt, error}
      end
    end)
    |> case do
      {:ok, nested_tvars} ->
        {:ok, Enum.uniq(head_tvars ++ bvar_tvars ++ List.flatten(nested_tvars))}

      error ->
        error
    end
  end
end
