/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Topology.Order.WithTop

/-!
# Order-topological limits in `WithTop`

Natural-number casts `(n : WithTop ι)` tend to `⊤` in any unbounded Archimedean ordered semiring
with the order topology.
-/

public section

open Filter
open scoped Topology

/-- Natural-number casts in `WithTop ι` converge to `⊤` in any unbounded Archimedean ordered
semiring with the order topology. -/
theorem WithTop.tendsto_coe_natCast_atTop {ι : Type*} [Semiring ι] [LinearOrder ι]
    [IsOrderedRing ι] [NoMaxOrder ι] [Archimedean ι] [TopologicalSpace ι] [OrderTopology ι] :
    Tendsto (fun n : ℕ ↦ ((n : ι) : WithTop ι)) atTop (𝓝 ⊤) :=
  WithTop.tendsto_coe_atTop.comp tendsto_natCast_atTop_atTop

end
