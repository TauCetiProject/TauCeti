/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Pointwise summability of families of operators

If the finite partial sums `∑ i ∈ s, T i` of a family of bounded operators into a complete space
are uniformly bounded in operator norm, then the vectors `x` for which the series `∑ i, T i x`
converges form a closed set (`TauCeti.isClosed_setOf_summable_apply`). Combined with convergence
on a dense set, this gives convergence of the series in the strong operator topology.
-/

public section

open ContinuousLinearMap Finset

namespace TauCeti

variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- If the finite partial sums of a family of operators are uniformly bounded, then the vectors
`x` for which the series `∑ i, T i x` converges form a closed set. -/
theorem isClosed_setOf_summable_apply {T : ι → E →L[𝕜] F} {A : ℝ}
    (hT : ∀ s : Finset ι, ‖∑ i ∈ s, T i‖ ≤ A) : IsClosed {x | Summable fun i ↦ T i x} := by
  refine isClosed_of_closure_subset fun x hx ↦ summable_iff_vanishing_norm.mpr fun ε hε ↦ ?_
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.mp hx (ε / (2 * (|A| + 1))) (by positivity)
  obtain ⟨s, hs⟩ := summable_iff_vanishing_norm.mp hy (ε / 2) (half_pos hε)
  refine ⟨s, fun t ht ↦ ?_⟩
  have hdist : (|A| + 1) * ‖x - y‖ < ε / 2 := by
    rw [← dist_eq_norm]
    calc (|A| + 1) * dist x y < (|A| + 1) * (ε / (2 * (|A| + 1))) := by gcongr
      _ = ε / 2 := by field_simp
  calc ‖∑ i ∈ t, T i x‖ = ‖(∑ i ∈ t, T i) (x - y) + ∑ i ∈ t, T i y‖ := by
        simp [sum_apply, map_sub]
    _ ≤ ‖∑ i ∈ t, T i‖ * ‖x - y‖ + ‖∑ i ∈ t, T i y‖ :=
        norm_add_le_of_le (le_opNorm _ _) le_rfl
    _ < ε / 2 + ε / 2 := by
        gcongr ?_ + ?_
        · calc ‖∑ i ∈ t, T i‖ * ‖x - y‖ ≤ (|A| + 1) * ‖x - y‖ := by
                gcongr; linarith [hT t, le_abs_self A]
            _ < ε / 2 := hdist
        · exact hs t ht
    _ = ε := add_halves ε

end TauCeti

end
