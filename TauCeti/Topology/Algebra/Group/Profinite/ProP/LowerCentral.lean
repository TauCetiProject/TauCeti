/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.LowerCentralSeries
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini

/-!
# The first step of the lower `p`-central series and the pro-`p` Frattini subgroup

The lower `p`-central series `TauCeti.pLowerCentralSeries` and its degree lemmas live in
`TauCeti.Topology.Algebra.Group.LowerCentralSeries`. This file adds the comparison with the
pro-`p` Frattini subgroup `TauCeti.proPFrattini`, which is not available there: that file does
not import the pro-`p` Frattini development.

## Main results

* `TauCeti.pLowerCentralStep_le_proPFrattini`: the first term `P₁` of the lower `p`-central
  series is contained in `TauCeti.proPFrattini p G`. Both of its generating families — the
  `p`-th powers and the commutators `⁅G, G⁆` — already lie in the Frattini subgroup, and the
  latter is closed, so the topological closure defining `P₁` is contained in it too.
-/

public section

namespace TauCeti

open scoped commutatorElement

variable {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The first step of the lower `p`-central series is contained in the pro-`p` Frattini subgroup:
its two generating families are exactly the `p`-th powers and the commutators, both of which lie
in `proPFrattini p G`. -/
theorem pLowerCentralStep_le_proPFrattini (hp : p.Prime)
    (hF : IsClosed ((proPFrattini p G : Subgroup G) : Set G)) :
    pLowerCentralSeries p G 1 ≤ proPFrattini p G := by
  rw [pLowerCentralSeries_succ, pLowerCentralSeries_zero]
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) hF
  · refine Subgroup.closure_le _ |>.mpr ?_
    rintro x ⟨h, -, rfl⟩
    exact pow_mem_proPFrattini h
  · refine Subgroup.commutator_le.mpr fun h _ g _ => ?_
    exact commutator_le_proPFrattini hp (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top h) (Subgroup.mem_top g))

end TauCeti
