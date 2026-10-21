/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Mazur's lemma

A weak limit in a locally convex space belongs to the closure of the convex hull of the
range. In a seminormed space, finite convex combinations from successive tails of a weakly
convergent sequence converge in norm to the weak limit. The coefficients are real and
nonnegative even for complex spaces.

`exists_sum_smul_norm_sub_lt_of_tendsto_weak` gives a finite combination from any specified
tail with any positive error tolerance. `exists_tendsto_sum_smul_of_tendsto_weak` chooses
such combinations as a norm-convergent sequence. In both statements, the indices in the
`n`th tail are written as `n + i`, so no coefficient can involve an earlier term.

These results require neither completeness nor separability. They use Mathlib's
`Convex.toWeakSpace_closure` to pass from weak convergence to norm approximation, and
`convexHull_range_eq_exists_affineCombination` to extract the finite coefficients.

## References

* R. E. Megginson, *An Introduction to Banach Space Theory*, §2.5 (Mazur's theorem).
-/

public section

open Filter Set Topology
open scoped BigOperators

namespace TauCeti

variable {𝕜 E : Type*} [RCLike 𝕜]

section

variable [AddCommGroup E] [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
  [LocallyConvexSpace ℝ E]

/-- A weak limit along a nontrivial filter in a locally convex space lies in the closure
of the real convex hull of the range, taken in the original topology. -/
theorem mem_closure_convexHull_range_of_tendsto_weak {ι : Type*} {l : Filter ι} [NeBot l]
    {u : ι → E} {x : E}
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) l (𝓝 (toWeakSpace 𝕜 E x))) :
    x ∈ closure (convexHull ℝ (range u)) := by
  have hx : toWeakSpace 𝕜 E x ∈
      closure (toWeakSpace 𝕜 E '' convexHull ℝ (range u)) :=
    mem_closure_of_tendsto hu (.of_forall fun n ↦
      mem_image_of_mem _ (subset_convexHull ℝ _ (mem_range_self n)))
  rw [← (convex_convexHull ℝ (range u)).toWeakSpace_closure 𝕜] at hx
  exact (toWeakSpace 𝕜 E).injective.mem_set_image.mp hx

end

variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]

/-- **Mazur's lemma**, with explicit finite coefficients: every tail of a weakly convergent
sequence admits a convex combination within any positive norm distance of its weak limit. -/
theorem exists_sum_smul_norm_sub_lt_of_tendsto_weak {u : ℕ → E} {x : E}
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x)))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (w : ℕ → ℝ),
      (∀ i ∈ s, 0 ≤ w i) ∧ (∑ i ∈ s, w i) = 1 ∧
        ‖(∑ i ∈ s, w i • u (n + i)) - x‖ < ε := by
  have htail : Tendsto (fun i ↦ toWeakSpace 𝕜 E (u (n + i))) atTop
      (𝓝 (toWeakSpace 𝕜 E x)) := by
    apply hu.comp
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat n
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp
    (mem_closure_convexHull_range_of_tendsto_weak htail) ε hε
  rw [convexHull_range_eq_exists_affineCombination] at hy
  obtain ⟨s, w, hw, hsum, rfl⟩ := hy
  refine ⟨s, w, hw, hsum, ?_⟩
  rw [Finset.affineCombination_eq_linear_combination _ _ _ hsum] at hxy
  simpa only [dist_eq_norm, norm_sub_rev] using hxy

/-- **Mazur's lemma**, in sequential form: choose a finite real convex combination from the
`n`th tail for every `n`, so that the combinations converge in norm to the weak limit. -/
theorem exists_tendsto_sum_smul_of_tendsto_weak {u : ℕ → E} {x : E}
    (hu : Tendsto (fun n ↦ toWeakSpace 𝕜 E (u n)) atTop (𝓝 (toWeakSpace 𝕜 E x))) :
    ∃ (s : ℕ → Finset ℕ) (w : ℕ → ℕ → ℝ),
      (∀ n i, i ∈ s n → 0 ≤ w n i) ∧ (∀ n, (∑ i ∈ s n, w n i) = 1) ∧
        Tendsto (fun n ↦ ∑ i ∈ s n, w n i • u (n + i)) atTop (𝓝 x) := by
  have happrox (n : ℕ) := exists_sum_smul_norm_sub_lt_of_tendsto_weak hu n
    (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  choose s w hw hsum hdist using happrox
  refine ⟨s, w, hw, hsum, ?_⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  exact squeeze_zero (fun _ ↦ norm_nonneg _) (fun n ↦ (hdist n).le)
    tendsto_one_div_add_atTop_nhds_zero_nat

end TauCeti
