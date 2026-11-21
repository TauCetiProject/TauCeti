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
* `RCLike.norm_le_abs_re_add_abs_im`: `‖z‖ ≤ |re z| + |im z|`, the `RCLike` counterpart of
  `Complex.norm_le_abs_re_add_abs_im`.
* `RCLike.continuousSMul_of_continuousConstSMul`: on an `RCLike`-module with continuous addition
  and real scalar multiplication, continuous constant `K`-scalar multiplication upgrades to
  jointly continuous `K`-scalar multiplication.
* `RCLike.re_mem_Ioo_of_mem_ball`: for `z ∈ Metric.ball z₀ δ`,
  `re z ∈ Set.Ioo (re z₀ - δ) (re z₀ + δ)`.
-/

public section

namespace RCLike

variable {K : Type*} [RCLike K]

/-- The norm of a scalar is at most the sum of the absolute values of its real and imaginary
parts. -/
theorem norm_le_abs_re_add_abs_im (z : K) : ‖z‖ ≤ |re z| + |im z| := by
  refine le_of_pow_le_pow_left₀ two_ne_zero (by positivity) ?_
  rw [norm_sq_eq_def]
  nlinarith [abs_mul_abs_self (re z), abs_mul_abs_self (im z), abs_nonneg (re z),
    abs_nonneg (im z)]

/-- A scalar with zero imaginary part is the image of its real part. -/
theorem re_eq_self_of_im_eq_zero {z : K} (h : im z = 0) : (re z : K) = z :=
  conj_eq_iff_re.mp (conj_eq_iff_im.mpr h)

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

end RCLike
