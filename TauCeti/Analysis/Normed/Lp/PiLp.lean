/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# Comparisons of finite product norms and distances

The finite `Lᵖ` norm respects coordinatewise bounds on norms, including when the two
families have different target spaces. This compares scalar evaluations of a vector
family with the vector family's `Lᵖ` norm. For constant fibres we deduce the bound for
the image of a family under a map of bounded growth, the norm of a family of multiples
of one vector, and the invariance of the norm under reindexing.

For `p ≥ 1`, the `Lᵖ` distance dominates the sup distance. In the other direction, the `L²`
distance is at most the square root of the number of coordinates times the sup distance.
These estimates give inclusions between balls in the two metrics. The corresponding
Cauchy–Schwarz estimate bounds the sum of coordinate norms by `√(card ι)` times the `L²` norm.
The coordinate spaces may be different seminormed groups, or pseudometric spaces for the
distance comparisons.

## Source

The coordinate-norm estimate is adapted from
`ForTauCeti/Analysis/Matrix/EntrywiseOpNorm.lean` in the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization).
Original copyright (c) 2026 Kitware, Inc.; Apache-2.0.
-/

public section

open scoped ENNReal

namespace PiLp

variable {ι : Type*} [Fintype ι] {p : ℝ≥0∞} {E F : ι → Type*}

/-- Coordinatewise domination of norms implies domination of finite `Lᵖ` norms.
The dominating family only needs a norm: the coordinate bounds ensure its nonnegativity. -/
theorem norm_mono [∀ i, SeminormedAddGroup (E i)] [∀ i, Norm (F i)]
    {x : PiLp p E} {y : PiLp p F}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [norm_eq_card, norm_eq_card]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    apply Set.Finite.toFinset_mono
    intro i hi hzero
    exact hi (le_antisymm (by simpa only [hzero] using h i) (norm_nonneg _))
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [norm_eq_ciSup, norm_eq_ciSup]
    exact ciSup_mono (Set.finite_range _).bddAbove h
  · simp only [norm_eq_sum (ENNReal.toReal_pos hp0 hp)]
    gcongr
    · exact Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _
    · exact h _

variable [∀ i, SeminormedAddCommGroup (E i)]

/-- Taking coordinate norms preserves the finite `Lᵖ` norm. -/
@[simp]
theorem norm_norm (x : PiLp p E) :
    ‖WithLp.toLp p (fun i ↦ ‖x i‖)‖ = ‖x‖ :=
  le_antisymm (norm_mono fun i ↦ by simp) (norm_mono fun i ↦ by simp)

/-- The sum of coordinate norms of a vector is at most `√(card ι)` times its `L²` norm. -/
theorem sum_norm_le_sqrt_card_mul_norm (x : PiLp 2 E) :
    ∑ i, ‖x i‖ ≤ Real.sqrt (Fintype.card ι) * ‖x‖ := by
  simpa [PiLp.norm_eq_of_L2] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun _ : ι ↦ 1) (fun i ↦ ‖x i‖)

section Constant

variable [Fact (1 ≤ p)] {E F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- Applying a map with `‖g v‖ ≤ C * ‖v‖` to each member of a finite family multiplies its
`Lᵖ` norm by at most `C`. -/
theorem norm_toLp_comp_le {g : E → F} {C : ℝ} (hC : 0 ≤ C) (hg : ∀ v, ‖g v‖ ≤ C * ‖v‖)
    (x : ι → E) : ‖WithLp.toLp p (fun i ↦ g (x i))‖ ≤ C * ‖WithLp.toLp p x‖ := by
  calc
    ‖WithLp.toLp p (fun i ↦ g (x i))‖ ≤ ‖C • WithLp.toLp p (fun i ↦ ‖x i‖)‖ :=
      norm_mono fun i ↦ by simpa [abs_of_nonneg hC] using hg (x i)
    _ = C * ‖WithLp.toLp p x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC, norm_norm (WithLp.toLp p x)]

/-- A finite family of multiples of one vector has `Lᵖ` norm equal to the `Lᵖ` norm of the
coefficients times the norm of the vector. -/
theorem norm_toLp_smul_const {𝕜 : Type*} [NormedField 𝕜] [NormedSpace 𝕜 F] (a : ι → 𝕜) (y : F) :
    ‖WithLp.toLp p (fun i ↦ a i • y)‖ = ‖WithLp.toLp p a‖ * ‖y‖ := by
  calc
    ‖WithLp.toLp p (fun i ↦ a i • y)‖ = ‖‖y‖ • WithLp.toLp p (fun i ↦ ‖a i‖)‖ :=
      le_antisymm (norm_mono fun i ↦ by simp [norm_smul, mul_comm])
        (norm_mono fun i ↦ by simp [norm_smul, mul_comm])
    _ = ‖WithLp.toLp p a‖ * ‖y‖ := by
      rw [norm_smul, _root_.norm_norm, norm_norm (WithLp.toLp p a), mul_comm]

/-- Reindexing a finite family along an equivalence preserves its `Lᵖ` norm. -/
theorem norm_toLp_comp_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (x : ι → E) :
    ‖WithLp.toLp p (x ∘ e)‖ = ‖WithLp.toLp p x‖ := by
  have he : LinearIsometryEquiv.piLpCongrLeft p ℤ E e.symm (WithLp.toLp p x) =
      WithLp.toLp p (x ∘ e) := by
    ext i
    simp [Equiv.piCongrLeft']
  rw [← he, LinearIsometryEquiv.norm_map]

end Constant

section PseudoMetricSpace

variable [Fact (1 ≤ p)] {β : ι → Type*} [∀ i, PseudoMetricSpace (β i)]

/-- The sup distance of the coordinate vectors is at most the `Lᵖ` distance, `p ≥ 1`. -/
theorem dist_ofLp_le (x y : PiLp p β) : dist (WithLp.ofLp x) (WithLp.ofLp y) ≤ dist x y := by
  simpa only [NNReal.coe_one, one_mul] using (lipschitzWith_ofLp p β).dist_le_mul x y

/-- The closed ball of radius `r` about `x` lies in the closed sup-metric ball of radius `r`
about `ofLp x`. -/
theorem closedBall_subset_preimage_ofLp_closedBall (x : PiLp p β) (r : ℝ) :
    Metric.closedBall x r ⊆ WithLp.ofLp ⁻¹' Metric.closedBall (WithLp.ofLp x) r := fun y hy ↦
  (dist_ofLp_le y x).trans hy

/-- The open ball of radius `r` about `x` lies in the open sup-metric ball of radius `r`
about `ofLp x`. -/
theorem ball_subset_preimage_ofLp_ball (x : PiLp p β) (r : ℝ) :
    Metric.ball x r ⊆ WithLp.ofLp ⁻¹' Metric.ball (WithLp.ofLp x) r := fun y hy ↦
  (dist_ofLp_le y x).trans_lt hy

/-- The `L²` distance is at most the square root of the coordinate count times the sup distance
between the coordinate vectors. -/
theorem dist_le_sqrt_card_mul_dist_ofLp (x y : PiLp 2 β) :
    dist x y ≤ Real.sqrt (Fintype.card ι) * dist (WithLp.ofLp x) (WithLp.ofLp y) := by
  simpa [NNReal.coe_rpow, Real.sqrt_eq_rpow] using
    (lipschitzWith_toLp 2 β).dist_le_mul (WithLp.ofLp x) (WithLp.ofLp y)

/-- A sup-metric closed ball of radius `r` pulls back into the `L²` closed ball of radius
`√(card ι) * r`. -/
theorem preimage_ofLp_closedBall_subset_closedBall (x : PiLp 2 β) (r : ℝ) :
    WithLp.ofLp ⁻¹' Metric.closedBall (WithLp.ofLp x) r ⊆
      Metric.closedBall x (Real.sqrt (Fintype.card ι) * r) := fun y hy ↦
  (dist_le_sqrt_card_mul_dist_ofLp y x).trans
    (mul_le_mul_of_nonneg_left hy (Real.sqrt_nonneg _))

/-- A sup-metric open ball of radius `r` pulls back into the `L²` open ball of radius
`√(card ι) * r`. The index type must be nonempty so that this scale factor is positive. -/
theorem preimage_ofLp_ball_subset_ball [Nonempty ι] (x : PiLp 2 β) (r : ℝ) :
    WithLp.ofLp ⁻¹' Metric.ball (WithLp.ofLp x) r ⊆
      Metric.ball x (Real.sqrt (Fintype.card ι) * r) := fun y hy ↦
  (dist_le_sqrt_card_mul_dist_ofLp y x).trans_lt
    (mul_lt_mul_of_pos_left hy (Real.sqrt_pos.2 (Nat.cast_pos.2 Fintype.card_pos)))

end PseudoMetricSpace

end PiLp
