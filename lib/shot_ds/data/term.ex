defmodule ShotDs.Data.Term do
  @moduledoc """
  Represents a Hol term as directed acyclic graph (DAG).

  All terms contain a deterministic ID assigned by `ShotDs.Stt.TermFactory`.
  Note that terms are in βη-normal form, i.e., fully β-reduced and η-expanded.

  Besides the obvious fields `:head`, `:args` and `:type`, two accessor fields
  are implemented for efficiency: `:fvars` contains all free variables
  occurring in the term, `:max_num` represents the index of the highest bound
  variable. Abstractions are identified by the `:bvars` field.
  """

  alias ShotDs.Data.Declaration
  alias ShotDs.Data.Type

  @enforce_keys [:id, :head, :type]
  defstruct [:id, :head, :type, bvars: [], args: [], fvars: [], max_num: 0]

  @typedoc """
  A term's id is given by an atomic positive integer where 0 denotes a dummy.
  """
  @type term_id :: non_neg_integer()

  @typedoc """
  The type of a term. The fields `:id`, `:head` and `:type` are required.
  """
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
