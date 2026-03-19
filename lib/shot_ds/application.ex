defmodule ShotDs.Application do
  @moduledoc false
  use Application

  @impl true
  def start(_type, _args) do
    :ets.new(:term_pool, [
      :set,
      :public,
      :named_table,
      read_concurrency: true,
      write_concurrency: true
    ])

    :ets.insert(:term_pool, {:id_counter, 0})

    children = []
    opts = [strategy: :one_for_one, name: ShotDs.Supervisor]
    Supervisor.start_link(children, opts)
  end
end
