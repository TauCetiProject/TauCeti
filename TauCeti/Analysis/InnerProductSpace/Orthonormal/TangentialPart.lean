/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Endomorphisms controlled by their values on tangential parts of a basis

Let `b` be an orthonormal basis of a finite-dimensional real inner product space, let `w` be a unit
vector, and write `τⱼ = bⱼ - ⟪bⱼ, w⟫ w` for the parts of the basis vectors orthogonal to `w`.
Every vector `h` is `∑ⱼ ⟪bⱼ, h⟫ τⱼ + ⟪w, h⟫ w`. Hence an endomorphism `S` which is symmetric
between `w` and each `τⱼ`, `⟪S w, τⱼ⟫ = ⟪S τⱼ, w⟫`, is determined by its values `S τⱼ` up to the
component `⟪S w, w⟫ w ⊗ w`, quantitatively:

* `ContinuousLinearMap.norm_apply_sub_inner_smul_le_sum`: `‖S w - ⟪S w, w⟫ w‖ ≤ ∑ⱼ ‖S τⱼ‖`;
* `ContinuousLinearMap.norm_sub_smul_smulRight_le`: `‖S - ⟪S w, w⟫ w ⊗ w‖ ≤ 2 ∑ⱼ ‖S τⱼ‖`.

At a flat boundary with unit normal `w`, the `S τⱼ` are the tangential columns of a Hessian, so
these bounds reduce the Hessian to its tangential columns and its normal-normal entry.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Let `b` be an orthonormal basis, `w` a unit vector and `τⱼ = bⱼ - ⟪bⱼ, w⟫ w`. If `S` is
symmetric between `w` and each `τⱼ`, then the coordinates of `S w - ⟪S w, w⟫ w` are the
`⟪S τⱼ, w⟫`, so its norm is at most `∑ⱼ ‖S τⱼ‖`. -/
theorem norm_apply_sub_inner_smul_le_sum (S : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) {w : E}
    (hw : ‖w‖ = 1) {τ : ι → E} (hτ : ∀ j, τ j = b j - ⟪b j, w⟫_ℝ • w)
    (hS : ∀ j, ⟪S w, τ j⟫_ℝ = ⟪S (τ j), w⟫_ℝ) :
    ‖S w - ⟪S w, w⟫_ℝ • w‖ ≤ ∑ j, ‖S (τ j)‖ := by
  have hcoord : ∀ j, ⟪b j, S w - ⟪S w, w⟫_ℝ • w⟫_ℝ = ⟪S (τ j), w⟫_ℝ := fun j => by
    rw [← hS j, hτ j]
    simp only [inner_sub_right, inner_smul_right]
    rw [real_inner_comm (S w)]
    ring
  calc ‖S w - ⟪S w, w⟫_ℝ • w‖ = ‖∑ j, ⟪b j, S w - ⟪S w, w⟫_ℝ • w⟫_ℝ • b j‖ := by
        rw [b.sum_repr']
    _ ≤ ∑ j, ‖⟪b j, S w - ⟪S w, w⟫_ℝ • w⟫_ℝ • b j‖ := norm_sum_le _ _
    _ ≤ ∑ j, ‖S (τ j)‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_smul, b.orthonormal.1 j, mul_one, hcoord, Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans (by rw [hw, mul_one])

/-- With `b`, `w`, `τⱼ` and `S` as in `ContinuousLinearMap.norm_apply_sub_inner_smul_le_sum`,
removing the component `⟪S w, w⟫ w ⊗ w` from `S` leaves an operator of norm at most `2 ∑ⱼ ‖S τⱼ‖`,
since every `h` is `∑ⱼ ⟪bⱼ, h⟫ τⱼ + ⟪w, h⟫ w`. -/
theorem norm_sub_smul_smulRight_le (S : E →L[ℝ] E) (b : OrthonormalBasis ι ℝ E) {w : E}
    (hw : ‖w‖ = 1) {τ : ι → E} (hτ : ∀ j, τ j = b j - ⟪b j, w⟫_ℝ • w)
    (hS : ∀ j, ⟪S w, τ j⟫_ℝ = ⟪S (τ j), w⟫_ℝ) :
    ‖S - ⟪S w, w⟫_ℝ • (innerSL ℝ w).smulRight w‖ ≤ 2 * ∑ j, ‖S (τ j)‖ := by
  have hSw := S.norm_apply_sub_inner_smul_le_sum b hw hτ hS
  -- Every `h` is `∑ⱼ ⟪bⱼ, h⟫ τⱼ + ⟪w, h⟫ w`.
  have hdec : ∀ h, ∑ j, ⟪b j, h⟫_ℝ • τ j + ⟪w, h⟫_ℝ • w = h := fun h => by
    have h3 : ∑ j, ⟪b j, h⟫_ℝ * ⟪b j, w⟫_ℝ = ⟪w, h⟫_ℝ := by
      rw [real_inner_comm h w, ← b.sum_inner_mul_inner h w]
      exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm (b j) h]
    simp only [hτ, smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul, b.sum_repr',
      h3, sub_add_cancel]
  refine opNorm_le_bound _ (mul_nonneg zero_le_two (Finset.sum_nonneg fun _ _ => norm_nonneg _))
    fun h => ?_
  have hSh : S h = ∑ j, ⟪b j, h⟫_ℝ • S (τ j) + ⟪w, h⟫_ℝ • S w := by
    conv_lhs => rw [← hdec h]
    simp only [map_add, map_sum, map_smul]
  have hS₁h : (S - ⟪S w, w⟫_ℝ • (innerSL ℝ w).smulRight w) h =
      ∑ j, ⟪b j, h⟫_ℝ • S (τ j) + ⟪w, h⟫_ℝ • (S w - ⟪S w, w⟫_ℝ • w) := by
    rw [sub_apply, smul_apply, smulRight_apply, innerSL_apply_apply, hSh]
    module
  rw [hS₁h]
  calc ‖∑ j, ⟪b j, h⟫_ℝ • S (τ j) + ⟪w, h⟫_ℝ • (S w - ⟪S w, w⟫_ℝ • w)‖
      ≤ ∑ j, ‖⟪b j, h⟫_ℝ • S (τ j)‖ + ‖⟪w, h⟫_ℝ • (S w - ⟪S w, w⟫_ℝ • w)‖ :=
        (norm_add_le _ _).trans (add_le_add_left (norm_sum_le _ _) _)
    _ ≤ ∑ j, ‖h‖ * ‖S (τ j)‖ + ‖h‖ * ∑ j, ‖S (τ j)‖ := by
        gcongr with j
        · rw [norm_smul, Real.norm_eq_abs]
          gcongr
          exact (abs_real_inner_le_norm _ _).trans (by rw [b.orthonormal.1 j, one_mul])
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul ((abs_real_inner_le_norm _ _).trans (by rw [hw, one_mul])) hSw
            (norm_nonneg _) (norm_nonneg _)
    _ = (2 * ∑ j, ‖S (τ j)‖) * ‖h‖ := by rw [← Finset.mul_sum]; ring

end ContinuousLinearMap
