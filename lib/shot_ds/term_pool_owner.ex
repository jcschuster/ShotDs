defmodule ShotDs.TermPoolOwner do
  @moduledoc false
  use GenServer

  def start_link(_),
    do: GenServer.start_link(__MODULE__, %{}, name: __MODULE__)

  def init(_) do
    :ets.new(:term_pool, [
      :set,
      :public,
      :named_table,
      read_concurrency: true,
      write_concurrency: true
    ])

    # The first value returned by :ets.update_counter/3 will be 1
    :ets.insert(:term_pool, {:id_counter, 0})

    {:ok, %{}}
  end
end
