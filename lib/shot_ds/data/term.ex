defmodule ShotDs.Data.Term do
  @moduledoc """
  Represents a Hol term as directed acyclic graph (DAG).

  All terms contain a deterministic ID assigned by `ShotDs.TermFactory`. Note
  that terms are in βη-normal form, i.e., fully β-reduced and η-expanded.

  Besides the obvious fields `:head`, `:args` and `:type`, two accessor fields
  are implemented for efficiency: `:fvars` contains all free variables
  occurring in the term, `:max_num` represents the index of the highest bound
  variable. Abstractions are identified by the `:bvars` field.
  """

  alias ShotDs.Data.Declaration
  alias ShotDs.Data.Type

  @enforce_keys [:id, :head, :type]
  defstruct [:id, :head, :type, bvars: [], args: [], fvars: [], max_num: 0]

  @doc """
  Returns a dummy ID for term construction before memoization.

  #### Warning {: .warning}

  Note that this is not a valid ID and should be used with caution!
  """
  @spec dummy_id() :: <<_::256>>
  def dummy_id, do: <<0::256>>

  @type term_id :: <<_::256>>
  @type t :: %__MODULE__{
          id: term_id(),
          bvars: [Declaration.t()],
          head: Declaration.t(),
          args: [term_id()],
          type: Type.t(),
          fvars: [Declaration.t()],
          max_num: non_neg_integer()
        }
end

defimpl String.Chars, for: ShotDs.Data.Term do
  def to_string(%{bvars: bvars, head: head, args: args, type: type}) do
    args_str = if args == [], do: "", else: "[#{length(args)} args]"
    bvars_str = String.duplicate("λ", length(bvars))

    case {bvars_str, args_str} do
      {"", ""} -> "#{head}"
      {"", a} -> "(#{head} #{a})_#{type}"
      {b, ""} -> "(#{b}. #{head})_#{type}"
      {b, a} -> "(#{b}. #{head} #{a})_#{type}"
    end
  end
end

