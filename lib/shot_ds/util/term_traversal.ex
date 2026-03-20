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

  ## Parameters

  * `term_id`: The unique identifier of the term to begin traversing.
  * `env`: An environment or context passed down the traversal (e.g., bound
    variables)
  * `update_env`: A function `(Term.t(), env -> env)` invoked on the way down
    to calculate the environment for the term's arguments.
  * `transform`: A function `(Term.t(), [Term.term_id()], env, cache ->
    {Term.term_id(), cache})`
  * `short_circuit`: (Optional) A predicate function `(Term.t(), env ->
    boolean())`. If it returns `true`, the traversal halts for this branch and
    returns the unmodified `term_id`.
  * `cache`: (Optional) A map tracking previously processed `{term_id, env}`
    pairs to their resulting `new_term_id`.

  ## Returns

  A tuple `{new_term_id, final_cache}`
  """
  @spec map_term(
          term_id :: Term.term_id(),
          env :: a,
          update_env :: (Term.t(), a -> a),
          transform :: (Term.t(), [Term.term_id()], a, map() -> {Term.term_id(), map()}),
          short_circuit :: (Term.t(), a -> boolean()),
          cache :: map()
        ) :: {Term.term_id(), map()}
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
        {cached_id, cache}

      :error ->
        term = TF.get_term(term_id)

        if short_circuit.(term, env) do
          {term_id, Map.put(cache, {term_id, env}, term_id)}
        else
          new_env = update_env.(term, env)

          arg_map_fn = &map_term(&1, new_env, update_env, transform, short_circuit, &2)

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

  > #### Note {: .info}
  >
  > Unlike `map_term`, this basic fold does not implement DAG caching out of
  > the box, so it will traverse shared subterms multiple times. It is best
  > suited for lightweight reduction or formatting tasks.

  ## Parameters

  * `term_id`: The unique identifier of the term to fold.
  * `fold_fn`: A function `(Term.t(), [a] -> a)` that receives the current
    term and a list of the already folded results of its arguments, returning
    the folded result for the current term.
  """
  @spec fold_term(Term.term_id(), (Term.t(), [a] -> a)) :: a when a: var
  def fold_term(term_id, fold_fn) do
    term = TF.get_term(term_id)
    folded_args = Enum.map(term.args, &fold_term(&1, fold_fn))
    fold_fn.(term, folded_args)
  end
end
