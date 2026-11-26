/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Convex.ConvexSpace.Defs
public import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Hausdorff dimension of the standard simplex

The weight vectors of `Convexity.StdSimplex ℝ ι`, for a nonempty finite type `ι`, lie in the
affine hyperplane `∑ v = 1` of `ι → ℝ`, whose Hausdorff dimension is `card ι - 1`. So the standard
simplex has Hausdorff dimension below `card ι`
(`Convexity.StdSimplex.dimH_range_weights_lt_card`).
-/

public section

open Set Module

namespace Convexity.StdSimplex

/-- The weight vectors of the standard simplex on a nonempty finite type `ι`, as a subset of
`ι → ℝ`, have Hausdorff dimension below `card ι`. -/
theorem dimH_range_weights_lt_card {ι : Type*} [Fintype ι] [Nonempty ι] :
    dimH (range fun t : StdSimplex ℝ ι ↦ ⇑t.weights) < Fintype.card ι := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty ι›
  set s : (ι → ℝ) →ₗ[ℝ] ℝ := ∑ a, LinearMap.proj a
  have hs (v : ι → ℝ) : s v = ∑ a, v a := by simp [s, LinearMap.sum_apply]
  have hsub : (range fun t : StdSimplex ℝ ι ↦ ⇑t.weights) ⊆ s ⁻¹' {1} := by
    rintro _ ⟨t, rfl⟩
    rw [mem_preimage, mem_singleton_iff, hs, ← t.total, Finsupp.sum_fintype _ _ (by simp)]
  have hne : (s ⁻¹' {1}).Nonempty := ⟨Pi.single a₀ 1, by simp [hs]⟩
  have hspan : vectorSpan ℝ (s ⁻¹' {1}) ≤ LinearMap.ker s := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨v, hv, w, hw, rfl⟩
    simp only [mem_preimage, mem_singleton_iff] at hv hw
    simp [hv, hw]
  have hker : LinearMap.ker s ≠ ⊤ := fun h ↦ one_ne_zero (α := ℝ) <| by
    simpa [hs] using LinearMap.congr_fun (LinearMap.ker_eq_top.mp h) (Pi.single a₀ 1)
  have hlt : finrank ℝ (vectorSpan ℝ (s ⁻¹' {1})) < Fintype.card ι := by
    refine (Submodule.finrank_mono hspan).trans_lt ?_
    simpa using Submodule.finrank_lt hker
  calc dimH (range fun t : StdSimplex ℝ ι ↦ ⇑t.weights) ≤ dimH (s ⁻¹' {1}) := dimH_mono hsub
    _ = finrank ℝ (vectorSpan ℝ (s ⁻¹' {1})) :=
        Real.Convex.dimH_eq_finrank_vectorSpan ((convex_singleton (1 : ℝ)).linear_preimage s) hne
    _ < Fintype.card ι := by exact_mod_cast hlt

end Convexity.StdSimplex
