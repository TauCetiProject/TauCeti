/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Geometric bounds from cofinite decay

A real family tending to zero along the cofinite filter is uniformly bounded and small outside
a finite set. After rescaling, these bounds give a common geometric tail for products of distinct
entries, as used in principal-minor coefficient estimates.
-/

public section

namespace TauCeti

open Filter Topology

/-- A null family admits a uniform bound and a finite exceptional set outside which its rescaling
is at most any prescribed `q ∈ (0, 1)`. The associated geometric tail tends to zero. -/
theorem exists_geometric_bound_of_tendsto_cofinite {ι : Type*}
    {r : ι → ℝ} (hr : Tendsto r cofinite (𝓝 0)) {ρ q : ℝ} (hρ : 0 ≤ ρ)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    ∃ (T : Finset ι) (B : ℝ), 1 ≤ B ∧ (∀ i ∉ T, ρ * r i ≤ q) ∧
      (∀ i, ρ * r i ≤ B) ∧
      Tendsto (fun n : ℕ ↦ B ^ T.card * q ^ (n - T.card)) atTop (𝓝 0) := by
  classical
  obtain ⟨M, hM⟩ := hr.bddAbove_range_of_cofinite
  have hfinite : {i | ¬ρ * r i ≤ q}.Finite := by
    refine eventually_cofinite.mp ?_
    exact ((hr.const_mul ρ).eventually
      (gt_mem_nhds (by simpa using hq₀ : ρ * 0 < q))).mono fun _ hi ↦ hi.le
  let T := hfinite.toFinset
  let B := max 1 (ρ * M)
  refine ⟨T, B, le_max_left _ _, (fun i hi ↦ ?_), (fun i ↦ ?_), ?_⟩
  · simpa [T] using hi
  · exact (mul_le_mul_of_nonneg_left (hM ⟨i, rfl⟩) hρ).trans (le_max_right _ _)
  · simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hq₀.le hq₁).comp
      (tendsto_sub_atTop_nat T.card)).const_mul (B ^ T.card)

end TauCeti
