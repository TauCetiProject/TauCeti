/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic

/-!
# Basic identities and norm bounds for `RCLike` fields

## Main results

* `RCLike.re_eq_self_of_im_eq_zero`: a scalar with zero imaginary part equals its real part.
* `TauCeti.RCLike.mul_conj_eq_one_iff`: a scalar times its conjugate is `1` exactly when it has
  norm `1`.
* `RCLike.norm_le_abs_re_add_abs_im`: `‖z‖ ≤ |re z| + |im z|`, the `RCLike` counterpart of
  `Complex.norm_le_abs_re_add_abs_im`.
* `RCLike.mem_unitary_iff_norm_eq_one`: an element of an `RCLike` field is unitary iff its norm
  is `1`.
* `RCLike.continuousSMul_of_continuousConstSMul`: on an `RCLike`-module with continuous addition
  and real scalar multiplication, continuous constant `K`-scalar multiplication upgrades to
  jointly continuous `K`-scalar multiplication.
* `RCLike.re_mem_Ioo_of_mem_ball`: for `z ∈ Metric.ball z₀ δ`,
  `re z ∈ Set.Ioo (re z₀ - δ) (re z₀ + δ)`.
* `RCLike.inv_re_le_two_mul_abs_im_inv`: off the real axis, `re z⁻¹ ≤ (2 * |im z|)⁻¹`.
* `RCLike.abs_re_sub_le_of_mem_closedBall`, `RCLike.abs_im_sub_le_of_mem_closedBall`,
  `RCLike.norm_le_abs_re_add_abs_im_add_of_mem_closedBall`, and
  `RCLike.mem_closedBall_of_abs_re_sub_add_abs_im_sub_le`: coordinate bounds on and membership
  in closed balls.
* `RCLike.sub_eq_ofReal_re_sub_of_im_eq`: horizontal differences are real casts.
* `RCLike.sum_mul_inv_le_sum_mul_re_sub_inv`: lower bound for weighted sums of
  `re (((σ : K) - ρ)⁻¹)` over real points `ρ ∈ S` with `0 < σ - re ρ ≤ D`.
* `RCLike.one_sub_re_le_norm_sub_one`: `1 - re z ≤ ‖z - 1‖`.
* `RCLike.norm_I_le_one`: `‖I‖ ≤ 1`, uniformly over `ℝ` (where `I = 0`) and `ℂ` (where `‖I‖ = 1`).
-/

public section

namespace RCLike

open ComplexConjugate

variable {K : Type*} [RCLike K]

/-- The norm of a scalar is at most the sum of the absolute values of its real and imaginary
parts. -/
theorem norm_le_abs_re_add_abs_im (z : K) : ‖z‖ ≤ |re z| + |im z| := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [norm_sq_eq_def]
  nlinarith [abs_mul_abs_self (re z), abs_mul_abs_self (im z), abs_nonneg (re z),
    abs_nonneg (im z)]

/-- The imaginary unit has norm at most `1`: it is either `0` (as over `ℝ`) or of norm `1` (as over
`ℂ`). -/
theorem norm_I_le_one : ‖(I : K)‖ ≤ 1 := by
  rw [norm_I]
  split_ifs <;> norm_num

/-- A scalar with zero imaginary part is the image of its real part. -/
theorem re_eq_self_of_im_eq_zero {z : K} (h : im z = 0) : (re z : K) = z :=
  conj_eq_iff_re.mp (conj_eq_iff_im.mpr h)

/-- An element of `ℝ` or `ℂ` is unitary if and only if it has norm `1`. -/
theorem mem_unitary_iff_norm_eq_one {z : K} : z ∈ unitary K ↔ ‖z‖ = 1 := by
  rw [Unitary.mem_iff_star_mul_self, star_def, conj_mul]
  constructor
  · intro h
    have hsq : ‖z‖ ^ 2 = 1 := by exact_mod_cast h
    nlinarith [norm_nonneg z]
  · intro h
    simp [h]

/-- On an `RCLike`-module whose addition and real scalar multiplication are jointly continuous,
continuous multiplication by constant `K`-scalars upgrades to joint continuity of `K`-scalar
multiplication. -/
theorem continuousSMul_of_continuousConstSMul {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] [Module ℝ M] [ContinuousSMul ℝ M] [Module K M] [IsScalarTower ℝ K M]
    [ContinuousConstSMul K M] : ContinuousSMul K M := by
  refine ⟨Continuous.congr (f := fun p : K × M ↦ re p.1 • p.2 + im p.1 • (I • p.2))
    (((continuous_re.comp continuous_fst).smul continuous_snd).add
      ((continuous_im.comp continuous_fst).smul
        ((continuous_const_smul (I : K)).comp continuous_snd)))
    fun p ↦ ?_⟩
  conv_rhs => rw [← re_add_im p.1]
  rw [add_smul, mul_smul, algebraMap_smul K (re p.1), algebraMap_smul K (im p.1)]

/-- The real part of any point in the open ball `Metric.ball z₀ δ` lies in
`Set.Ioo (re z₀ - δ) (re z₀ + δ)`. -/
theorem re_mem_Ioo_of_mem_ball {z z₀ : K} {δ : ℝ} (hz : z ∈ Metric.ball z₀ δ) :
    re z ∈ Set.Ioo (re z₀ - δ) (re z₀ + δ) := by
  simpa only [Real.ball_eq_Ioo, NNReal.coe_one, one_mul] using
    lipschitzWith_re.mapsTo_ball one_ne_zero z₀ δ hz

/-- Off the real axis, the real part of `z⁻¹` is at most `(2 * |im z|)⁻¹`. -/
theorem inv_re_le_two_mul_abs_im_inv {z : K} (hz : im z ≠ 0) :
    re z⁻¹ ≤ (2 * |im z|)⁻¹ := by
  have : 0 < |im z| := abs_pos.2 hz
  have : 0 < re z * re z + im z * im z :=
    add_pos_of_nonneg_of_pos (mul_self_nonneg (re z)) (mul_self_pos.2 hz)
  rw [inv_re, normSq_apply, div_le_iff₀ this, le_inv_mul_iff₀ (by positivity)]
  nlinarith [sq_nonneg (re z - |im z|), sq_abs (im z)]

/-- On `closedBall z₀ r`, the real part differs from `re z₀` by at most `r`. -/
theorem abs_re_sub_le_of_mem_closedBall {z z₀ : K} {r : ℝ}
    (hz : z ∈ Metric.closedBall z₀ r) : |re z - re z₀| ≤ r := by
  simpa only [← map_sub] using (abs_re_le_norm (z - z₀)).trans (by simpa [dist_eq_norm] using hz)

/-- On `closedBall z₀ r`, the imaginary part differs from `im z₀` by at most `r`. -/
theorem abs_im_sub_le_of_mem_closedBall {z z₀ : K} {r : ℝ}
    (hz : z ∈ Metric.closedBall z₀ r) : |im z - im z₀| ≤ r := by
  simpa only [← map_sub] using (abs_im_le_norm (z - z₀)).trans (by simpa [dist_eq_norm] using hz)

/-- On `closedBall z₀ r`, the norm of `z` is at most `|re z₀| + |im z₀| + r`. -/
theorem norm_le_abs_re_add_abs_im_add_of_mem_closedBall {z z₀ : K} {r : ℝ}
    (hz : z ∈ Metric.closedBall z₀ r) : ‖z‖ ≤ |re z₀| + |im z₀| + r :=
  (norm_le_of_mem_closedBall hz).trans (add_le_add_left (norm_le_abs_re_add_abs_im z₀) r)

/-- If `|re z - re w| + |im z - im w| ≤ r`, then `z ∈ Metric.closedBall w r`. -/
theorem mem_closedBall_of_abs_re_sub_add_abs_im_sub_le {z w : K} {r : ℝ}
    (h : |re z - re w| + |im z - im w| ≤ r) : z ∈ Metric.closedBall w r := by
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact (norm_le_abs_re_add_abs_im (z - w)).trans (by simpa [map_sub] using h)

/-- Two scalars with the same imaginary part differ by the real cast of the difference of their
real parts. -/
theorem sub_eq_ofReal_re_sub_of_im_eq {z w : K} (h : im z = im w) :
    z - w = ((re z - re w : ℝ) : K) :=
  RCLike.ext (by simp) (by simp [h])

/-- For nonnegative weights `w` on real points `ρ ∈ S` (`im ρ = 0`) satisfying
`0 < σ - re ρ ≤ D`, the weighted reciprocal sum `∑ ρ ∈ S, w ρ * re (((σ : K) - ρ)⁻¹)` is at
least `(∑ ρ ∈ S, w ρ) * D⁻¹`. -/
theorem sum_mul_inv_le_sum_mul_re_sub_inv {S : Finset K} {w : K → ℝ} {σ D : ℝ}
    (hw : ∀ ρ ∈ S, 0 ≤ w ρ) (hρ : ∀ ρ ∈ S, im ρ = 0 ∧ 0 < σ - re ρ ∧ σ - re ρ ≤ D) :
    (∑ ρ ∈ S, w ρ) * D⁻¹ ≤ ∑ ρ ∈ S, w ρ * re (((σ : K) - ρ)⁻¹) := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun ρ hρS ↦ ?_
  obtain ⟨him, hpos, hle⟩ := hρ ρ hρS
  have hdiff : (σ : K) - ρ = ((σ - re ρ : ℝ) : K) := by
    simpa using sub_eq_ofReal_re_sub_of_im_eq (z := (σ : K)) (w := ρ) (by simp [him])
  rw [hdiff, ← ofReal_inv, ofReal_re]
  exact mul_le_mul_of_nonneg_left (inv_anti₀ hpos hle) (hw ρ hρS)

/-- The real part of a scalar falls short of `1` by at most its distance to `1`. -/
theorem one_sub_re_le_norm_sub_one (z : K) : 1 - re z ≤ ‖z - 1‖ := by
  simpa [norm_sub_rev] using re_le_norm (1 - z)

end RCLike

namespace TauCeti

open ComplexConjugate

/-- A scalar times its conjugate is `1` exactly when the scalar has norm `1`. -/
@[simp]
theorem RCLike.mul_conj_eq_one_iff {K : Type*} [RCLike K] {z : K} :
    z * conj z = 1 ↔ ‖z‖ = 1 := by
  rw [RCLike.mul_conj]
  norm_cast
  exact pow_eq_one_iff_of_nonneg (norm_nonneg z) two_ne_zero

end TauCeti
