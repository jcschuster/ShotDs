defmodule ShotDs.Data.Substitution do
  @moduledoc """
  Represents a substitution.
  """

  alias ShotDs.Data.{Declaration, Term}

  @enforce_keys [:fvar, :term_id]
  defstruct [:fvar, :term_id]

  @typedoc """
  The type of a substitution.

  A substitution is made up by the free variable to substitute and the id for
  its replacement term.
  """
  @type t :: %__MODULE__{
          fvar: Declaration.free_var_t(),
          term_id: Term.term_id()
        }

  @doc """
  Creates a new substitution for the given free variable and the id for its
  replacement term.
  """
  @spec new(Declaration.free_var_t(), Term.term_id()) :: t()
  def new(%Declaration{kind: :fv} = fvar, term_id) when is_binary(term_id) do
    %__MODULE__{fvar: fvar, term_id: term_id}
  end
end
