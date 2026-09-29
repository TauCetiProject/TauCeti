/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Group
public import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# Valuation bounds on sums of series in a valuative topology

Let `R` be a ring whose topology is induced by its valuative relation. For `γ ≠ 0` the open ball
`{z | v z < γ}` is an open, hence closed, additive subgroup of `R`. So it contains the sum of any
convergent series all of whose terms lie in it: this is `TauCeti.valuation_lt_of_hasSum`.
-/

public section

open Filter ValuativeRel

namespace TauCeti

variable {R : Type*} [Ring R] [ValuativeRel R] [TopologicalSpace R] [IsValuativeTopology R]

/-- A convergent series whose terms all have valuation less than `γ` has sum of valuation less
than `γ`, because the open ball `{z | v z < γ}` is a closed additive subgroup. -/
theorem valuation_lt_of_hasSum {ι : Type*} {f : ι → R} {s : R} (hf : HasSum f s)
    (γ : (ValueGroupWithZero R)ˣ) (h : ∀ i, valuation R (f i) < γ) : valuation R s < γ := by
  let S := (valuation R).ltAddSubgroup γ
  have hS : IsClosed (S : Set R) := by
    refine AddSubgroup.isClosed_of_isOpen S (AddSubgroup.isOpen_of_mem_nhds S (g := 0) ?_)
    exact (IsValuativeTopology.mem_nhds_zero_iff _).mpr ⟨γ, fun z hz => hz⟩
  exact hS.mem_of_tendsto hf (Eventually.of_forall fun t => AddSubgroup.sum_mem _ fun i _ => h i)

end TauCeti
