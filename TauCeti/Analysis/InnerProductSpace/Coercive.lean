/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, OpenAI GPT-5.6 Thinking, Claude Opus 5, OpenAI GPT-6
-/
module

public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic

/-!
# Coercive bounded operators

A uniformly coercive real part of the quadratic form makes a bounded operator
on a real or complex Hilbert space invertible. Self-adjointness is not needed.
The inverse follows from Mathlib’s operator invertibility criterion for a
uniform lower bound on the norm of the quadratic form.
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
Apache-2.0, copyright 2026 Kitware, Inc. The invertibility proof here applies
Mathlib's `ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map` directly.
-/

public section

open scoped InnerProductSpace

namespace ContinuousLinearMap

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A quadratic-form lower bound yields the corresponding norm lower bound. -/
theorem mul_norm_le_norm_apply_of_coercive (N : E →L[𝕜] E) {c : ℝ}
    (hcoer : ∀ z, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜) (z : E) :
    c * ‖z‖ ≤ ‖N z‖ := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · have h := (hcoer z).trans ((RCLike.re_le_norm _).trans (norm_inner_le_norm _ _))
    exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hz)).mp (by nlinarith [h])

/-- A bounded operator with a uniformly coercive real quadratic form is a unit. -/
theorem isUnit_of_coercive [CompleteSpace E] (N : E →L[𝕜] E) {c : ℝ}
    (hc : 0 < c) (hcoer : ∀ z, c * ‖z‖ ^ 2 ≤ RCLike.re ⟪N z, z⟫_𝕜) : IsUnit N := by
  apply isUnit_of_forall_le_norm_inner_map N (c := ⟨c, hc.le⟩) hc
  intro x
  exact (mul_comm _ _).le.trans ((hcoer x).trans (RCLike.re_le_norm _))

/-- If `C = R²`, `Rinv` is the two-sided inverse of the self-adjoint `R`, and
`C W + W† C = 2 B`, a quadratic-form lower bound `δ` for `B` gives the lower bound
`δ / (1 + ‖R‖²)` for `R W Rinv`. No positivity of `R` or nontriviality of the space
is required, and `δ = 0` is allowed. -/
theorem coercive_conj_of_lyapunov [CompleteSpace E]
    (B C W R Rinv : E →L[𝕜] E)
    (hR : IsSelfAdjoint R) (hRinv : IsSelfAdjoint Rinv)
    (hRR : R ∘L R = C)
    (hRinvR : Rinv ∘L R = ContinuousLinearMap.id 𝕜 E)
    (hRRinv : R ∘L Rinv = ContinuousLinearMap.id 𝕜 E)
    (hlyap : C ∘L W + star W ∘L C = B + B)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hBcoer : ∀ x, δ * ‖x‖ ^ 2 ≤ RCLike.re ⟪B x, x⟫_𝕜) :
    ∀ x, δ / (1 + ‖R‖ ^ 2) * ‖x‖ ^ 2 ≤
      RCLike.re ⟪(R ∘L W ∘L Rinv) x, x⟫_𝕜 := by
  let Z := R ∘L W ∘L Rinv
  have hRstar := hR.star_eq
  have hRinvstar := hRinv.star_eq
  have hZstar : star Z = Rinv ∘L star W ∘L R := by
    dsimp [Z]
    simp only [← ContinuousLinearMap.mul_def, star_mul, hRstar, hRinvstar, mul_assoc]
  have hleft : Rinv ∘L C = R := by
    rw [← hRR, ← ContinuousLinearMap.comp_assoc, hRinvR, ContinuousLinearMap.id_comp]
  have hright : C ∘L Rinv = R := by
    rw [← hRR, ContinuousLinearMap.comp_assoc, hRRinv, ContinuousLinearMap.comp_id]
  have hZherm :
      Z + star Z = (Rinv ∘L B ∘L Rinv) + (Rinv ∘L B ∘L Rinv) := by
    have hconj := congrArg (fun T : E →L[𝕜] E => Rinv ∘L T ∘L Rinv) hlyap
    simp only [ContinuousLinearMap.comp_add, ContinuousLinearMap.add_comp] at hconj
    simp only [← ContinuousLinearMap.comp_assoc, hleft] at hconj
    rw [ContinuousLinearMap.comp_assoc (Rinv ∘L star W) C Rinv, hright] at hconj
    rw [hZstar]
    simpa only [Z, ContinuousLinearMap.comp_assoc] using hconj
  intro x
  let y : E := Rinv x
  have hxy : R y = x := by
    dsimp [y]
    have := DFunLike.congr_fun hRRinv x
    simpa only [ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply] using this
  have hreal : RCLike.re ⟪Z x, x⟫_𝕜 = RCLike.re ⟪B y, y⟫_𝕜 := by
    have hsum := congrArg
      (fun T : E →L[𝕜] E => RCLike.re ⟪T x, x⟫_𝕜) hZherm
    simp only [add_apply, inner_add_left, map_add,
      ContinuousLinearMap.comp_apply] at hsum
    have hstarReal : RCLike.re ⟪star Z x, x⟫_𝕜 =
        RCLike.re ⟪Z x, x⟫_𝕜 := by
      rw [ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
      exact inner_re_symm x (Z x)
    have hRinvAdj : ContinuousLinearMap.adjoint Rinv = Rinv := by
      rw [← ContinuousLinearMap.star_eq_adjoint]
      exact hRinvstar
    have hRinvInner : RCLike.re ⟪Rinv (B y), x⟫_𝕜 =
        RCLike.re ⟪B y, y⟫_𝕜 := by
      rw [← hRinvAdj, ContinuousLinearMap.adjoint_inner_left]
    rw [hstarReal, hRinvInner] at hsum
    linarith
  have hB := hBcoer y
  have hnorm : ‖x‖ ≤ ‖R‖ * ‖y‖ := by
    rw [← hxy]
    exact R.le_opNorm y
  have hsq : ‖x‖ ^ 2 ≤ ‖R‖ ^ 2 * ‖y‖ ^ 2 := by
    nlinarith [hnorm, norm_nonneg x, norm_nonneg R, norm_nonneg y]
  rw [hreal]
  have hden : 0 < 1 + ‖R‖ ^ 2 := by positivity
  have hcoef : δ / (1 + ‖R‖ ^ 2) * ‖R‖ ^ 2 ≤ δ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    nlinarith [hδ]
  have hscaled : δ / (1 + ‖R‖ ^ 2) * ‖x‖ ^ 2 ≤ δ * ‖y‖ ^ 2 := by
    calc
      δ / (1 + ‖R‖ ^ 2) * ‖x‖ ^ 2 ≤
          δ / (1 + ‖R‖ ^ 2) * (‖R‖ ^ 2 * ‖y‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsq (div_nonneg hδ hden.le)
      _ = (δ / (1 + ‖R‖ ^ 2) * ‖R‖ ^ 2) * ‖y‖ ^ 2 := by ring
      _ ≤ δ * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖)
  exact hscaled.trans hB

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

/-- A positive invertible Lyapunov weight transports a coercive form bound to a spectral
half-plane bound, with the square-root similarity made explicit in the constant. -/
theorem le_re_of_mem_spectrum_of_positive_lyapunov
    (B C W : E →L[ℂ] E) (hC : IsStrictlyPositive C)
    (hlyap : C ∘L W + star W ∘L C = B + B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hB : ∀ x, δ * ‖x‖ ^ 2 ≤ (⟪B x, x⟫_ℂ).re)
    {z : ℂ} (hz : z ∈ spectrum ℂ W) :
    δ / (1 + ‖C ^ (1 / 2 : ℝ)‖ ^ 2) ≤ z.re := by
  let R := C ^ (1 / 2 : ℝ)
  let Rinv := C ^ (-(1 / 2 : ℝ))
  have hRinvR : Rinv ∘L R = ContinuousLinearMap.id ℂ E := by
    simpa only [R, Rinv, ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using
      CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hC
  have hRRinv : R ∘L Rinv = ContinuousLinearMap.id ℂ E := by
    simpa only [R, Rinv, ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using
      CFC.rpow_mul_rpow_neg (1 / 2 : ℝ) hC
  have hRR : R ∘L R = C := by
    simpa only [CFC.sqrt_eq_rpow, R, ContinuousLinearMap.mul_def] using
      CFC.sqrt_mul_sqrt_self C hC.nonneg
  let e := ContinuousLinearEquiv.equivOfInverse' R Rinv hRRinv hRinvR
  have he : e.conjContinuousAlgEquiv.toAlgEquiv W = R ∘L W ∘L Rinv := by
    ext x
    simp only [ContinuousAlgEquiv.coe_toAlgEquiv,
      ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
      ContinuousLinearEquiv.equivOfInverse'_apply, ContinuousLinearEquiv.symm_equivOfInverse',
      ContinuousLinearMap.comp_apply, e]
  have hz' : z ∈ spectrum ℂ (e.conjContinuousAlgEquiv.toAlgEquiv W) := by
    rwa [AlgEquiv.spectrum_eq]
  rw [he] at hz'
  exact le_re_of_mem_spectrum_of_coercive _
    (coercive_conj_of_lyapunov B C W R Rinv
      (CFC.rpow_nonneg (a := C) (y := (1 / 2 : ℝ))).isSelfAdjoint
      (CFC.rpow_nonneg (a := C) (y := (-(1 / 2 : ℝ)))).isSelfAdjoint
      hRR hRinvR hRRinv hlyap hδ hB) hz'

end ContinuousLinearMap
