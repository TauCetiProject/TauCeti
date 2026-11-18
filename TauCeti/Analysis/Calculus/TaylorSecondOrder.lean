/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue

/-!
# A first-order Taylor bound on the unit interval

For a curve `c : ℝ → F` that is `C²` at every point of `[0, 1]` with `‖c''‖ ≤ K` there,
`‖c(1) - c(0) - c'(0)‖ ≤ K`. It follows from the segment mean value inequality applied first to
`c'` and then to `t ↦ c(t) - t c'(0)`.
-/

public section

open Set

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **First-order Taylor bound on `[0, 1]`.** If `c` is `C²` at every point of `[0, 1]` and
`‖c''‖ ≤ K` there, then `‖c(1) - c(0) - c'(0)‖ ≤ K`. -/
theorem norm_sub_sub_deriv_le_of_norm_deriv_deriv_le {c : ℝ → F} {K : ℝ}
    (hc : ∀ t ∈ Icc (0 : ℝ) 1, ContDiffAt ℝ 2 c t)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, ‖deriv (deriv c) t‖ ≤ K) :
    ‖c 1 - c 0 - deriv c 0‖ ≤ K := by
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt c (deriv c t) t := fun t ht ↦
    ((hc t ht).differentiableAt (by simp)).hasDerivAt
  have hdd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt (deriv c) (deriv (deriv c) t) t := fun t ht ↦ by
    have h1 : ContDiffAt ℝ 1 (deriv c) t := by
      have := (hc t ht).fderiv_right (m := 1) (by norm_num)
      have hfun : deriv c = (ContinuousLinearMap.apply ℝ F (1 : ℝ)) ∘ fderiv ℝ c :=
        funext fun s ↦ (fderiv_apply_one_eq_deriv).symm
      rw [hfun]
      exact (ContinuousLinearMap.apply ℝ F (1 : ℝ)).contDiff.contDiffAt.comp t this
    exact (h1.differentiableAt one_ne_zero).hasDerivAt
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
