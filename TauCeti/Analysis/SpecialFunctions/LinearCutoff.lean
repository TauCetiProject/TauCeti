/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# Smooth cutoffs along a linear functional

For a real continuous linear functional `L` on a normed space, a slope `c` and a level `s`, the
cutoff `TauCeti.linearCutoff L c s` is `x ↦ ψ (c (L x - s))`, where `ψ` is
`Real.smoothTransition`. For `0 < c` it vanishes on the half-space `{L x ≤ s}` and is one on
`{L x ≥ s + c⁻¹}`. It is smooth, takes values in `[0, 1]`, and its derivative is bounded, so it
can multiply Sobolev functions. Cutoffs in a single coordinate of a product, such as the normal or
a tangential coordinate of a half-space, are the special cases where `L` is a coordinate
projection, possibly composed with a functional on that factor.

## Main declarations

* `TauCeti.linearCutoff`: the cutoff `x ↦ ψ (c (L x - s))`.
* `TauCeti.linearCutoff_eq_zero` and `TauCeti.linearCutoff_eq_one`: where it is zero and one.
* `TauCeti.contDiff_linearCutoff` and `TauCeti.hasFDerivAt_linearCutoff`: it is smooth, with
  derivative `ψ'(c (L x - s)) c L`.
* `TauCeti.tsupport_linearCutoff_subset`: for `0 ≤ c` its support lies in `{s ≤ L x}`.
* `TauCeti.exists_linearCutoff_bound`: it and its derivative are bounded by a common constant.
-/

public section

noncomputable section

open Set
open scoped ContDiff

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The cutoff `x ↦ ψ (c (L x - s))` along the linear functional `L`, where `ψ` is
`Real.smoothTransition`. For `0 < c` it vanishes where `L x ≤ s` and is one where
`L x ≥ s + c⁻¹`. -/
def linearCutoff (L : F →L[ℝ] ℝ) (c s : ℝ) (x : F) : ℝ :=
  Real.smoothTransition (c * (L x - s))

/-- The defining formula of the cutoff along a linear functional. -/
theorem linearCutoff_def (L : F →L[ℝ] ℝ) (c s : ℝ) (x : F) :
    linearCutoff L c s x = Real.smoothTransition (c * (L x - s)) :=
  (rfl)

/-- The cutoff along a linear functional is nonnegative. -/
theorem linearCutoff_nonneg (L : F →L[ℝ] ℝ) (c s : ℝ) (x : F) : 0 ≤ linearCutoff L c s x :=
  Real.smoothTransition.nonneg _

/-- The cutoff along a linear functional is at most one. -/
theorem linearCutoff_le_one (L : F →L[ℝ] ℝ) (c s : ℝ) (x : F) : linearCutoff L c s x ≤ 1 :=
  Real.smoothTransition.le_one _

/-- The cutoff along a linear functional is zero where `c (L x - s) ≤ 0`. -/
@[simp]
theorem linearCutoff_eq_zero {L : F →L[ℝ] ℝ} {c s : ℝ} {x : F} (hx : c * (L x - s) ≤ 0) :
    linearCutoff L c s x = 0 :=
  Real.smoothTransition.zero_of_nonpos hx

/-- The cutoff along a linear functional is one where `c (L x - s) ≥ 1`. -/
@[simp]
theorem linearCutoff_eq_one {L : F →L[ℝ] ℝ} {c s : ℝ} {x : F} (hx : 1 ≤ c * (L x - s)) :
    linearCutoff L c s x = 1 :=
  Real.smoothTransition.one_of_one_le hx

/-- The cutoff along a linear functional is smooth. -/
theorem contDiff_linearCutoff (L : F →L[ℝ] ℝ) (c s : ℝ) : ContDiff ℝ ∞ (linearCutoff L c s) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.mul (L.contDiff.sub contDiff_const))

/-- The derivative of the cutoff along `L` is `ψ'(c (L x - s)) c` times `L`. -/
theorem hasFDerivAt_linearCutoff (L : F →L[ℝ] ℝ) (c s : ℝ) (x : F) :
    HasFDerivAt (linearCutoff L c s)
      ((deriv Real.smoothTransition (c * (L x - s)) * c) • L) x :=
  ((L.hasFDerivAt.sub_const s).const_mul c).smoothTransition.congr_fderiv (by rw [smul_smul])

/-- For a nonnegative slope `c`, the cutoff along `L` has topological support in `{s ≤ L x}`. -/
theorem tsupport_linearCutoff_subset (L : F →L[ℝ] ℝ) {c : ℝ} (hc : 0 ≤ c) (s : ℝ) :
    tsupport (linearCutoff L c s) ⊆ {x | s ≤ L x} := by
  refine closure_minimal (fun x hx => ?_) (isClosed_le continuous_const L.continuous)
  by_contra hlt
  exact hx (linearCutoff_eq_zero (mul_nonpos_of_nonneg_of_nonpos hc
    (sub_nonpos.2 (not_le.1 hlt).le)))

/-- The cutoff along a linear functional and its derivative are bounded by a common constant. -/
theorem exists_linearCutoff_bound (L : F →L[ℝ] ℝ) (c s : ℝ) :
    ∃ M, 0 ≤ M ∧ (∀ x, |linearCutoff L c s x| ≤ M) ∧
      ∀ x, ‖fderiv ℝ (linearCutoff L c s) x‖ ≤ M := by
  obtain ⟨B, hB⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  refine ⟨max 1 (B * ‖c‖ * ‖L‖), zero_le_one.trans (le_max_left _ _), fun x => ?_, fun x => ?_⟩
  · rw [abs_of_nonneg (linearCutoff_nonneg L c s x)]
    exact (linearCutoff_le_one L c s x).trans (le_max_left _ _)
  · rw [(hasFDerivAt_linearCutoff L c s x).fderiv, norm_smul, norm_mul]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hB _) (norm_nonneg c))
      (norm_nonneg L)).trans (le_max_right _ _)

end TauCeti
