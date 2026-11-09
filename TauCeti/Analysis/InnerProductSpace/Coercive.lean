/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5, OpenAI GPT-5.6 Thinking, Claude Opus 5, OpenAI GPT-6
-/
module

public import TauCeti.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.InnerProductSpace.QuadraticForm.Bounds
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

For an operator on a real inner product space, the quadratic form `⟪T v, v⟫` is bounded by
`‖T‖ ‖v‖²` (`ContinuousLinearMap.abs_inner_apply_le`), and the form `⟪S (A v), v⟫` of `S`
against `A` by `‖S‖ ‖A‖ ‖v‖²` (`ContinuousLinearMap.abs_inner_apply_apply_le`). Two consequences
bound the change of this form under a perturbation of `A`
(`ContinuousLinearMap.inner_apply_apply_sub_le`) and bound below the form
`⟪S (A v), v⟫ - ½ ⟪D v, v⟫` that appears when integrating against a family of quadratic forms
(`ContinuousLinearMap.neg_mul_norm_sq_le_inner_sub`).

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

/-- Conjugating a Lyapunov identity by an inverse self-adjoint square root gives the
Hermitian part of the similar operator. -/
theorem conj_add_star_of_lyapunov [CompleteSpace E]
    (B C W R Rinv : E →L[𝕜] E)
    (hR : IsSelfAdjoint R) (hRinv : IsSelfAdjoint Rinv)
    (hRR : R * R = C) (hRinvR : Rinv * R = 1) (hRRinv : R * Rinv = 1)
    (hlyap : C * W + star W * C = B + B) :
    R * W * Rinv + star (R * W * Rinv) =
      Rinv * B * Rinv + Rinv * B * Rinv := by
  have hleft : Rinv * C = R := by rw [← hRR, ← mul_assoc, hRinvR, one_mul]
  have hright : C * Rinv = R := by rw [← hRR, mul_assoc, hRRinv, mul_one]
  have hconj : Rinv * (C * W + star W * C) * Rinv =
      R * W * Rinv + Rinv * star W * R := by
    calc
      _ = (Rinv * C) * W * Rinv + Rinv * star W * (C * Rinv) := by noncomm_ring
      _ = _ := by rw [hleft, hright]
  rw [hlyap, mul_add, add_mul] at hconj
  simpa only [star_mul, hR.star_eq, hRinv.star_eq, mul_assoc] using hconj.symm

/-- If `C = R²`, `Rinv` is the two-sided inverse of the self-adjoint `R`, and
`C W + W† C = 2 B`, a quadratic-form lower bound `δ` for `B` gives the lower bound
`δ / (1 + ‖R‖²)` for `R W Rinv`. No positivity of `R` or nontriviality of the space
is required, and `δ = 0` is allowed. -/
theorem coercive_conj_of_lyapunov [CompleteSpace E]
    (B C W R Rinv : E →L[𝕜] E)
    (hR : IsSelfAdjoint R) (hRinv : IsSelfAdjoint Rinv)
    (hRR : R * R = C) (hRinvR : Rinv * R = 1) (hRRinv : R * Rinv = 1)
    (hlyap : C * W + star W * C = B + B)
    {δ : ℝ} (hδ : 0 ≤ δ) (hBcoer : B.LowerFormBoundOn ⊤ δ) :
    ∀ x, δ / (1 + ‖R‖ ^ 2) * ‖x‖ ^ 2 ≤
      RCLike.re ⟪(R * W * Rinv) x, x⟫_𝕜 := by
  intro x
  let y := Rinv x
  have hxy : R y = x := by
    simpa only [y, mul_apply_eq_comp, one_apply_eq_self] using DFunLike.congr_fun hRRinv x
  -- Transfer the quadratic form using the conjugated Lyapunov identity.
  have hreal : RCLike.re ⟪(R * W * Rinv) x, x⟫_𝕜 = RCLike.re ⟪B y, y⟫_𝕜 := by
    have hsum := congrArg (fun T : E →L[𝕜] E => RCLike.re ⟪T x, x⟫_𝕜)
      (conj_add_star_of_lyapunov B C W R Rinv hR hRinv hRR hRinvR hRRinv hlyap)
    simp only [add_apply, inner_add_left, map_add, re_inner_star_apply_self,
      mul_apply_eq_comp] at hsum
    have hRinvAdj : Rinv.adjoint = Rinv := by
      rw [← star_eq_adjoint]; exact hRinv.star_eq
    have hinner : RCLike.re ⟪Rinv (B y), x⟫_𝕜 = RCLike.re ⟪B y, y⟫_𝕜 := by
      rw [← hRinvAdj, adjoint_inner_left]
    rw [hinner] at hsum
    simp only [mul_apply_eq_comp]
    linarith
  -- The inverse change of variables costs at most the square of the operator norm.
  have hnorm : ‖x‖ ≤ ‖R‖ * ‖y‖ := by rw [← hxy]; exact R.le_opNorm y
  have hsq : ‖x‖ ^ 2 ≤ ‖R‖ ^ 2 * ‖y‖ ^ 2 := by
    nlinarith [hnorm, norm_nonneg x, norm_nonneg R, norm_nonneg y]
  have hden : 0 < 1 + ‖R‖ ^ 2 := by positivity
  have hcoef : δ / (1 + ‖R‖ ^ 2) * ‖R‖ ^ 2 ≤ δ := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    nlinarith [hδ]
  rw [hreal]
  calc
    δ / (1 + ‖R‖ ^ 2) * ‖x‖ ^ 2 ≤
        δ / (1 + ‖R‖ ^ 2) * (‖R‖ ^ 2 * ‖y‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (div_nonneg hδ hden.le)
    _ = (δ / (1 + ‖R‖ ^ 2) * ‖R‖ ^ 2) * ‖y‖ ^ 2 := by ring
    _ ≤ δ * ‖y‖ ^ 2 := mul_le_mul_of_nonneg_right hcoef (sq_nonneg ‖y‖)
    _ ≤ RCLike.re ⟪B y, y⟫_𝕜 := (lowerFormBoundOn_iff B ⊤ δ).mp hBcoer y Submodule.mem_top

section Real

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The quadratic form of a bounded operator `T` is bounded by `‖T‖ ‖v‖²`. -/
theorem abs_inner_apply_le (T : F →L[ℝ] F) (v : F) : |⟪T v, v⟫_ℝ| ≤ ‖T‖ * ‖v‖ ^ 2 :=
  calc |⟪T v, v⟫_ℝ| ≤ ‖T v‖ * ‖v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖T‖ * ‖v‖ * ‖v‖ := by gcongr; exact T.le_opNorm v
    _ = ‖T‖ * ‖v‖ ^ 2 := by ring

/-- The quadratic form of `S` against `A` is bounded by `‖S‖ ‖A‖ ‖v‖²`. -/
theorem abs_inner_apply_apply_le (S A : F →L[ℝ] F) (v : F) :
    |⟪S (A v), v⟫_ℝ| ≤ ‖S‖ * ‖A‖ * ‖v‖ ^ 2 :=
  ((S.comp A).abs_inner_apply_le v).trans
    (mul_le_mul_of_nonneg_right (S.opNorm_comp_le A) (sq_nonneg _))

/-- The quadratic form of `S` against `B` differs from that against `A` by at most
`‖S‖ ‖B - A‖ ‖v‖²`. -/
theorem inner_apply_apply_sub_le (S A B : F →L[ℝ] F) (v : F) :
    ⟪S (A v), v⟫_ℝ - ⟪S (B v), v⟫_ℝ ≤ ‖S‖ * ‖B - A‖ * ‖v‖ ^ 2 := by
  have h : ⟪S (A v), v⟫_ℝ - ⟪S (B v), v⟫_ℝ = -⟪S ((B - A) v), v⟫_ℝ := by
    simp only [sub_apply, map_sub, inner_sub_left]
    ring
  rw [h, neg_le]
  exact neg_le_of_abs_le (S.abs_inner_apply_apply_le (B - A) v)

/-- The quadratic form `⟪S (A v), v⟫ - ½ ⟪D v, v⟫` is at least `-(‖S‖ ‖A‖ + ‖D‖ / 2) ‖v‖²`. -/
theorem neg_mul_norm_sq_le_inner_sub (S A D : F →L[ℝ] F) (v : F) :
    -((‖S‖ * ‖A‖ + ‖D‖ / 2) * ‖v‖ ^ 2) ≤ ⟪S (A v), v⟫_ℝ - ⟪D v, v⟫_ℝ / 2 := by
  have h₁ := neg_le_of_abs_le (S.abs_inner_apply_apply_le A v)
  have h₂ := le_of_abs_le (D.abs_inner_apply_le v)
  linarith

end Real

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
    (hlyap : C * W + star W * C = B + B) {δ : ℝ} (hδ : 0 ≤ δ)
    (hB : B.LowerFormBoundOn ⊤ δ)
    {z : ℂ} (hz : z ∈ spectrum ℂ W) :
    δ / (1 + ‖C ^ (1 / 2 : ℝ)‖ ^ 2) ≤ z.re := by
  let R := C ^ (1 / 2 : ℝ)
  let Rinv := C ^ (-(1 / 2 : ℝ))
  have hRinvR : Rinv * R = 1 := CFC.rpow_neg_mul_rpow (1 / 2 : ℝ) hC
  have hRRinv : R * Rinv = 1 := CFC.rpow_mul_rpow_neg (1 / 2 : ℝ) hC
  have hRR : R * R = C := by
    simpa only [CFC.sqrt_eq_rpow, R] using CFC.sqrt_mul_sqrt_self C hC.nonneg
  -- The inverse-equivalence constructor uses composition; translate at this boundary only.
  let e := ContinuousLinearEquiv.equivOfInverse' R Rinv
    (by simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using hRRinv)
    (by simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using hRinvR)
  have he : e.conjContinuousAlgEquiv.toAlgEquiv W = R * W * Rinv := by
    ext x
    simp only [ContinuousAlgEquiv.coe_toAlgEquiv,
      ContinuousLinearEquiv.conjContinuousAlgEquiv_apply_apply,
      ContinuousLinearEquiv.equivOfInverse'_apply, ContinuousLinearEquiv.symm_equivOfInverse',
      mul_apply_eq_comp, e]
  have hz' : z ∈ spectrum ℂ (e.conjContinuousAlgEquiv.toAlgEquiv W) := by
    rwa [AlgEquiv.spectrum_eq]
  rw [he] at hz'
  exact le_re_of_mem_spectrum_of_coercive _
    (coercive_conj_of_lyapunov B C W R Rinv
      (CFC.rpow_nonneg (a := C) (y := (1 / 2 : ℝ))).isSelfAdjoint
      (CFC.rpow_nonneg (a := C) (y := (-(1 / 2 : ℝ)))).isSelfAdjoint
      hRR hRinvR hRRinv hlyap hδ hB) hz'

end ContinuousLinearMap
