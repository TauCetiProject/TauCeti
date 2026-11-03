/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, OpenAI GPT-5.6 Thinking, Claude Opus 5, OpenAI GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.Analysis.Normed.Algebra.Spectrum
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

/-!
# Coercive bounded operators

A uniformly coercive real part of the quadratic form makes a bounded operator
on a real or complex Hilbert space invertible. Self-adjointness is not needed.
The inverse follows from the real Lax–Milgram theorem after restricting scalars.
For complex operators the same argument applied to a scalar shift bounds the
real part of every spectral value below by the coercivity constant.

These facts supply the invertibility and spectral half-plane steps in
Lyapunov arguments comparing positive spectral subspaces.

## Provenance

Adapted from `ForTauCeti/Analysis/InnerProductSpace/CoerciveUnit.lean`
(Jon Crall and Claude Fable 5) and
`DavisKahan/InfiniteDimensional/TanTwoTheta/QuarterAcuteFormGap.lean`
(Jon Crall, OpenAI GPT-5.6 Thinking, Claude Opus 5), in the
[Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization),
Apache-2.0, copyright 2026 Kitware, Inc. The invertibility proof here reuses
Mathlib's real Lax–Milgram equivalence instead of reproducing its range argument.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A quadratic-form lower bound yields the corresponding norm lower bound. -/
theorem norm_smul_le_norm_apply_of_coercive (N : E →L[𝕜] E) {c : ℝ}
    (hcoer : ∀ z, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜) (z : E) :
    c * ‖z‖ ≤ ‖N z‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have h := (hcoer z).trans ((RCLike.re_le_norm _).trans (norm_inner_le_norm _ _))
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hz)).mp (by nlinarith [h])

/-- A bounded operator with a uniformly coercive real quadratic form is a unit. -/
theorem isUnit_of_coercive [CompleteSpace E] (N : E →L[𝕜] E) {c : ℝ}
    (hc : 0 < c) (hcoer : ∀ z, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜) : IsUnit N := by
  let := InnerProductSpace.rclikeToReal 𝕜 E
  let B : E →L[ℝ] E →L[ℝ] ℝ := (innerSL ℝ).comp (N.restrictScalars ℝ)
  have hB : IsCoercive B := ⟨c, hc, fun z ↦ by
    simpa [B, real_inner_eq_re_inner, pow_two, mul_assoc] using hcoer z⟩
  have hNB (z : E) : hB.continuousLinearEquivOfBilin z = N z := by
    apply ext_inner_right ℝ
    intro w
    simp [B, hB.continuousLinearEquivOfBilin_apply]
  rw [isUnit_iff_bijective]
  have hfun : ⇑hB.continuousLinearEquivOfBilin = ⇑N := funext hNB
  rw [← hfun]
  exact hB.continuousLinearEquivOfBilin.bijective

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- A uniform lower bound for the real quadratic form bounds real parts of spectral values below. -/
theorem le_re_of_mem_spectrum_of_coercive (N : E →L[ℂ] E) {c : ℝ}
    (hcoer : ∀ x, c * ‖x‖ ^ 2 ≤ (⟪N x, x⟫_ℂ).re)
    {z : ℂ} (hz : z ∈ spectrum ℂ N) : c ≤ z.re := by
  by_contra hnot
  have hgap : 0 < c - z.re := sub_pos.mpr (lt_of_not_ge hnot)
  have hunit : IsUnit (N - z • 1) := isUnit_of_coercive _ hgap fun x ↦ by
    have hx := hcoer x
    simp only [sub_apply, smul_apply, one_apply_eq_self, inner_sub_left,
      inner_smul_left, map_sub]
    simp only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.re_mul_ofReal,
      RCLike.conj_re]
    -- Normalize the RCLike real projection to the complex field projection for arithmetic.
    change (c - z.re) * ‖x‖ ^ 2 ≤ (⟪N x, x⟫_ℂ).re - z.re * ‖x‖ ^ 2
    nlinarith
  rw [spectrum.mem_iff] at hz
  exact hz (by simpa [Algebra.algebraMap_eq_smul_one] using hunit.neg)

end ContinuousLinearMap
