/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.FrattiniSeries
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini.Basic
import Mathlib.Topology.Separation.Connected

/-!
# One step of the Frattini series is a pro-`p` Frattini subgroup

One step `TauCeti.proPFrattiniStep p H = closure (Hᵖ [H, H])` of the Frattini series, defined for
arbitrary topological groups in `TauCeti.Topology.Algebra.Group.FrattiniSeries`, is for a prime
`p` and a closed subgroup `H` of a profinite group the pro-`p` Frattini subgroup
`TauCeti.proPFrattini p H` of `H`, transported to the ambient group along the inclusion. This is
the verbal description `TauCeti.proPFrattini_eq_topologicalClosure` applied inside `H`.

This bridge is kept apart from the rest of the Frattini series so that the relative Frattini
argument in `TauCeti.Topology.Algebra.Group.Profinite.ProP.Burnside` can use it: the Frattini
series module itself lies above `Burnside` in the import graph.

## Main results

* `TauCeti.proPFrattiniStep_eq_map_proPFrattini`: for a prime `p` and a closed subgroup `H` of a
  profinite group, `proPFrattiniStep p H` is the pro-`p` Frattini subgroup of `H`, viewed inside
  the ambient group.
-/

public section

namespace TauCeti

open Subgroup

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **One step of the Frattini series is the pro-`p` Frattini subgroup.** For a prime `p` and a
closed subgroup `H` of a profinite group, `proPFrattiniStep p H` is the pro-`p` Frattini subgroup
of `H`, viewed inside the ambient group along the inclusion. -/
theorem proPFrattiniStep_eq_map_proPFrattini (hp : p.Prime) {H : Subgroup G}
    (hH : IsClosed (H : Set G)) :
    proPFrattiniStep p H = (proPFrattini p H).map H.subtype := by
  have : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  -- The `p`-th powers of `H`, computed in `H` and transported, are the `p`-th powers of `H`.
  have himage : ⇑H.subtype '' (Set.range fun x : H ↦ x ^ p) = (· ^ p) '' (H : Set G) := by
    rw [← Set.range_comp]
    refine Set.ext fun x ↦ ⟨?_, ?_⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, by simp⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, by simp⟩
  rw [proPFrattini_eq_topologicalClosure hp,
    H.subtype.map_topologicalClosure continuous_subtype_val _
      (isClosed_topologicalClosure _).isCompact,
    Subgroup.map_sup, MonoidHom.map_closure, himage, H.map_subtype_commutator,
    proPFrattiniStep_def]

end TauCeti
