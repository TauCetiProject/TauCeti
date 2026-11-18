/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giada Franz, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.MeanValue

/-!
# A first-order Taylor bound on the unit interval

For a twice differentiable curve `c : ℝ → F` on `[0, 1]` with `‖c''‖ ≤ K` there,
`‖c(1) - c(0) - c'(0)‖ ≤ K`. This controls the deviation of the endpoint from its first-order
affine approximation, for example when estimating the error in a tangent-plane projection.
Continuity of the second derivative is not required.

Adapted from Giada Franz's `ForTauCeti/Analysis/Calculus/TaylorSecondOrder.lean` in
[ColdingMinicozziTheory](https://github.com/riccardobrasca/ColdingMinicozziTheory).
-/

public section

open Set

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **First-order Taylor bound on `[0, 1]`.** If `c` and `deriv c` are differentiable at every
point of `[0, 1]` and `‖c''‖ ≤ K` there, then `‖c(1) - c(0) - c'(0)‖ ≤ K`. -/
theorem norm_sub_sub_deriv_le_of_norm_deriv_deriv_le {c : ℝ → F} {K : ℝ}
    (hc : ∀ t ∈ Icc (0 : ℝ) 1,
      DifferentiableAt ℝ c t ∧ DifferentiableAt ℝ (deriv c) t)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (deriv c) t‖ ≤ K) :
    ‖c 1 - c 0 - deriv c 0‖ ≤ K := by
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt c (deriv c t) t := fun t ht ↦
    (hc t ht).1.hasDerivAt
  have hdd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (deriv c) (deriv (deriv c) t) t := fun t ht ↦
    (hc t ht).2.hasDerivAt
  have hvel : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv c t - deriv c 0‖ ≤ K * (t - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun t ht ↦ (hdd t ht).hasDerivWithinAt)
      fun t ht ↦ hK t (Ico_subset_Icc_self ht)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0 ⟨le_rfl, zero_le_one⟩)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' (f := fun t ↦ c t - t • deriv c 0)
    (f' := fun t ↦ deriv c t - deriv c 0) (C := K)
    (fun t ht ↦ ((hd t ht).sub ((hasDerivAt_id t).smul_const (deriv c 0))).hasDerivWithinAt
      |>.congr_deriv (by simp))
    (fun t ht ↦ (hvel t (Ico_subset_Icc_self ht)).trans (by nlinarith [ht.1, ht.2.le]))
    1 ⟨zero_le_one, le_rfl⟩
  simpa [sub_right_comm] using h

end TauCeti
