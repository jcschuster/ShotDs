defmodule ShotDs.Util.TermTraversal do
  @moduledoc """
  Utilities for efficiently traversing and transforming Hol term DAGs.
  """
  alias ShotDs.Data.Term
  alias ShotDs.Stt.TermFactory, as: TF

  @doc """
  A bottom-up map combinator on term DAGs for transforming term DAGs with
  environment passing and efficient caching.

  This function traverses a term and its arguments recursively. It evaluates in
  a post-order fashion (bottom-up), meaning the arguments of a term are mapped
  before the term itself is transformed. It uses a cache to memoize visits,
  ensuring that shared subterms are only processed once per unique environment.

  Returns a tuple `{:ok, {result_id, final_cache}}` or `{:error, reason}`.
  """
  @spec map_term(
          term_id :: Term.term_id(),
          env :: a,
          update_env :: (Term.t(), a -> a),
          transform :: (Term.t(), [Term.term_id()], a, map() ->
                          {{:ok, Term.term_id()} | TF.lookup_error_t(), map()}),
          short_circuit :: (Term.t(), a -> boolean()),
          cache :: map()
        ) :: {:ok, {Term.term_id(), map()}} | TF.lookup_error_t()
        when a: var
  def map_term(
        term_id,
        env,
        update_env,
        transform,
        short_circuit \\ fn _, _ -> false end,
        cache \\ %{}
      ) do
    case Map.fetch(cache, {term_id, env}) do
      {:ok, cached_id} ->
        {:ok, {cached_id, cache}}

      :error ->
        do_map_term(term_id, env, update_env, transform, short_circuit, cache)
    end
  end

  defp do_map_term(term_id, env, update_env, transform, short_circuit, cache) do
    with {:ok, term} <- TF.get_term(term_id) do
      if short_circuit.(term, env) do
        {:ok, {term_id, Map.put(cache, {term_id, env}, term_id)}}
      else
        process_map_term_args(term, term_id, env, update_env, transform, short_circuit, cache)
      end
    end
  end

  defp process_map_term_args(term, term_id, env, update_env, transform, short_circuit, cache) do
    new_env = update_env.(term, env)

    args_result =
      Enum.reduce_while(term.args, {:ok, {[], cache}}, fn arg_id, {:ok, {acc_args, acc_cache}} ->
        case map_term(arg_id, new_env, update_env, transform, short_circuit, acc_cache) do
          {:ok, {new_arg_id, next_cache}} -> {:cont, {:ok, {[new_arg_id | acc_args], next_cache}}}
          error -> {:halt, error}
        end
      end)

    with {:ok, {rev_new_args, cache_after_args}} <- args_result,
         new_args = Enum.reverse(rev_new_args),
         {transform_result, final_cache} = transform.(term, new_args, new_env, cache_after_args),
         {:ok, new_id} <- transform_result do
      {:ok, {new_id, Map.put(final_cache, {term_id, env}, new_id)}}
    end
  end

  @doc """
  A bottom-up map combinator on term DAGs for transforming term DAGs with
  environment passing and efficient caching, erroring out if it encounters an
  invalid ID.

  This function traverses a term and its arguments recursively. It evaluates in
  a post-order fashion (bottom-up), meaning the arguments of a term are mapped
  before the term itself is transformed. It uses a cache to memoize visits,
  ensuring that shared subterms are only processed once per unique environment.

  Returns a tuple `{result_id, final_cache}`.
  """
  @spec map_term!(
          term_id :: Term.term_id(),
          env :: a,
          update_env :: (Term.t(), a -> a),
          transform :: (Term.t(), [Term.term_id()], a, map() -> {Term.term_id(), map()}),
          short_circuit :: (Term.t(), a -> boolean()),
          cache :: map()
        ) :: {Term.term_id(), map()}
        when a: var
  def map_term!(
        term_id,
        env,
        update_env,
        transform,
        short_circuit \\ fn _, _ -> false end,
        cache \\ %{}
      ) do
    case Map.fetch(cache, {term_id, env}) do
      {:ok, cached_id} ->
        {cached_id, cache}

      :error ->
        term = TF.get_term!(term_id)

        if short_circuit.(term, env) do
          {term_id, Map.put(cache, {term_id, env}, term_id)}
        else
          new_env = update_env.(term, env)

          arg_map_fn = &map_term!(&1, new_env, update_env, transform, short_circuit, &2)

          {new_args, cache} = Enum.map_reduce(term.args, cache, arg_map_fn)

          {new_id, cache} = transform.(term, new_args, new_env, cache)

          {new_id, Map.put(cache, {term_id, env}, new_id)}
        end
    end
  end

  @doc """
  A bottom-up fold combinator for reducing a term DAG into a single value.

  This combinator visits the leaves of the term graph first, applies the
  `fold_fn`, and propagates the computed result up to the parent terms.

  Returns a tuple `{:ok, {result, final_cache}}` or `{:error, reason}`.
  """
  @spec fold_term(Term.term_id(), (Term.t(), [a] -> a), map()) ::
          {:ok, {a, map()}} | TF.lookup_error_t()
        when a: var
  def fold_term(term_id, fold_fn, cache \\ %{}) do
    case Map.fetch(cache, term_id) do
      {:ok, result} ->
        {:ok, {result, cache}}

      :error ->
        with {:ok, term} <- TF.get_term(term_id),
             {:ok, {rev_args, next_cache}} <- fold_args(term.args, fold_fn, cache, []) do
          args = Enum.reverse(rev_args)
          result = fold_fn.(term, args)
          {:ok, {result, Map.put(next_cache, term_id, result)}}
        end
    end
  end

  defp fold_args([], _fold_fn, cache, acc), do: {:ok, {acc, cache}}

  defp fold_args([arg_id | rest], fold_fn, cache, acc) do
    case fold_term(arg_id, fold_fn, cache) do
      {:ok, {res, next_cache}} -> fold_args(rest, fold_fn, next_cache, [res | acc])
      error -> error
    end
  end

  @doc """
  A bottom-up fold combinator for reducing a term DAG into a single value,
  erroring out if it encounters an invalid ID.

  This combinator visits the leaves of the term graph first, applies the
  `fold_fn`, and propagates the computed result up to the parent terms.

  Returns a tuple `{result, final_cache}`.
  """
  @spec fold_term!(Term.term_id(), (Term.t(), [a] -> a), map()) :: {a, map()}
        when a: var
  def fold_term!(term_id, fold_fn, cache \\ %{}) do
    case fold_term(term_id, fold_fn, cache) do
      {:ok, {result, final_cache}} -> {result, final_cache}
      {:error, reason} -> raise ArgumentError, message: inspect(reason)
    end
  end
end
