/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Schwartz
public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Harmonic monomials times Gaussians

Multiplying a Gaussian `exp (-b ‖x‖²)`, with `Re b > 0`, by a harmonic monomial of degree one on a
real inner product space or of arbitrary angular degree on the complex plane gives a Schwartz
function whose Fourier transform is the same monomial times the dual Gaussian:

* on a finite-dimensional real inner product space `V` of dimension `d`, `x ↦ ⟪x, v⟫ exp (-b ‖x‖²)`
  is the Schwartz function `SchwartzMap.innerMulGaussian` and has Fourier transform
  `(π / b)^(d/2 + 1) (-i) ⟪ξ, v⟫ exp (-π² ‖ξ‖² / b)`
  (`TauCeti.fourier_inner_mul_cexp_neg_mul_norm_sq`); on `ℝ` this gives the degree-`0` and
  degree-`1` harmonic monomials `x^ε exp (-b x²)` for `ε ≤ 1`
  (`TauCeti.fourier_pow_mul_cexp_neg_mul_sq_of_le_one`);
* on `ℂ`, the polynomials `z^n` and `conj(z)^n` are harmonic on the real plane, and multiplying
  either by `exp (-b ‖z‖²)` gives a Schwartz function whose Fourier transform is the same monomial
  times `exp (-π² ‖ξ‖² / b)` with scalar `(π / b)^(n+1) (-i)^n`
  (`TauCeti.fourier_pow_mul_cexp_neg_mul_norm_sq`,
  `TauCeti.fourier_conj_pow_mul_cexp_neg_mul_norm_sq`).

These are the real- and complex-place factors of the polynomial-weighted theta kernels used in
Hecke's method. At `b = π y`, the scalar at a real place is `y^(-ε - 1/2) (-i)^ε` (`ε ≤ 1`) and at
a complex place is `y^(-n - 1) (-i)^n`, where both complex orientations occur according to the sign
of a character's angular frequency.

The linear inner-product identity differentiates `SchwartzMap.gaussian` in direction `v` and reads
the derivative on the Fourier side via Mathlib's `SchwartzMap.fourier_lineDerivOp_eq`. On `ℂ`, the
planar conjugate Wirtinger derivative kills `z^n`, turns the Gaussian into `-b z` times itself, and
acts as the Fourier multiplier `π i ξ`. The base Gaussian transform in both cases is Mathlib's
`fourier_gaussian_innerProductSpace` (S. Gouëzel).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§7–8, Hecke's lemma and the
  polynomial-weighted theta kernel.
-/

public noncomputable section

open Complex ComplexConjugate LineDeriv MeasureTheory
open scoped FourierTransform RealInnerProductSpace SchwartzMap Real

namespace TauCeti

/-- The Fréchet derivative of `x ↦ exp (-b ‖x‖²)` on a real inner product space, taking `v` to
`-2 b ⟪x, v⟫ exp (-b ‖x‖²)`. No positivity assumption on `b` is needed. -/
theorem hasFDerivAt_cexp_neg_mul_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : ℂ) (x : V) :
    HasFDerivAt (fun y : V ↦ cexp (-b * ‖y‖ ^ 2))
      ((((-2 * b) * cexp (-b * ‖x‖ ^ 2)) • (ofRealCLM.comp (innerSL ℝ x)))) x := by
  have hnorm := (ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_id x).norm_sq).const_mul (-b)
  have hexp := ((Complex.hasDerivAt_exp _).hasFDerivAt.restrictScalars ℝ).comp x hnorm
  convert hexp using 1
  · ext y
    simp [ofReal_pow]
  · ext v
    simp [ContinuousLinearMap.comp_apply, smul_eq_mul, ofReal_pow]
    ring

/-- The planar conjugate Wirtinger derivative of a complex Gaussian. No positivity assumption
is needed for this differential identity. -/
theorem conjWirtingerDeriv_cexp_neg_mul_norm_sq (b z : ℂ) :
    conjWirtingerDeriv (fun w : ℂ ↦ cexp (-b * ‖w‖ ^ 2)) z 1 =
      -b * z * cexp (-b * ‖z‖ ^ 2) := by
  have heq : (fun w : ℂ ↦ cexp (-b * ‖w‖ ^ 2)) =
      fun w ↦ cexp (-b * (w * conj w)) := by
    ext w
    rw [mul_conj, normSq_eq_norm_sq, ofReal_pow]
  rw [heq, conjWirtingerDeriv_apply]
  have h := ((hasFDerivAt_id z).mul conjCLE.hasFDerivAt).const_mul (-b)
  have hx := ((Complex.hasDerivAt_exp _).hasFDerivAt.restrictScalars ℝ).comp z h
  simp only [Function.comp_def, Pi.mul_apply, id_eq, conjCLE_apply] at hx
  rw [hx.fderiv]
  simp [ContinuousLinearMap.comp_apply, smul_eq_mul, mul_conj, normSq_eq_norm_sq,
    ofReal_pow]
  ring_nf
  simp only [I_sq]
  ring

/-- Multiplication by a holomorphic monomial does not add a term to the conjugate Wirtinger
derivative of a Gaussian. This is the raising relation for the angular Gaussian factors. -/
theorem conjWirtingerDeriv_pow_mul_cexp_neg_mul_norm_sq (b : ℂ) (n : ℕ) (z : ℂ) :
    conjWirtingerDeriv (fun w : ℂ ↦ w ^ n * cexp (-b * ‖w‖ ^ 2)) z 1 =
      -b * z ^ (n + 1) * cexp (-b * ‖z‖ ^ 2) := by
  have hd : DifferentiableAt ℝ (fun w : ℂ ↦ cexp (-b * ‖w‖ ^ 2)) z := by
    simp_rw [← ofReal_pow, ← normSq_eq_norm_sq, ← mul_conj]
    fun_prop
  rw [conjWirtingerDeriv_fun_mul (by fun_prop) hd]
  have hp : DifferentiableAt ℂ (fun w : ℂ ↦ w ^ n) z := by fun_prop
  simp only [hp.conjWirtingerDeriv_eq_zero, smul_zero, add_zero, smul_apply, smul_eq_mul,
    conjWirtingerDeriv_cexp_neg_mul_norm_sq]
  ring

end TauCeti

namespace SchwartzMap

section InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The Gaussian `exp (-b ‖x‖²)` on a real inner product space multiplied by the linear harmonic
polynomial `x ↦ ⟪x, v⟫`, as a Schwartz function. -/
def innerMulGaussian {b : ℂ} (hb : 0 < b.re) (v : V) : 𝓢(V, ℂ) :=
  smulLeftCLM ℂ (fun x : V ↦ ⟪x, v⟫) (gaussian hb)

/-- Evaluation of the linear-monomial Schwartz Gaussian. -/
@[simp]
theorem innerMulGaussian_apply {b : ℂ} (hb : 0 < b.re) (v x : V) :
    innerMulGaussian hb v x = (⟪x, v⟫ : ℂ) * cexp (-b * ‖x‖ ^ 2) := by
  rw [innerMulGaussian, smulLeftCLM_apply_apply (Function.hasTemperateGrowth_inner_left v),
    gaussian_apply, Complex.real_smul]

/-- At the zero direction, the linear-monomial Schwartz Gaussian vanishes. -/
@[simp]
theorem innerMulGaussian_zero {b : ℂ} (hb : 0 < b.re) :
    innerMulGaussian hb (0 : V) = 0 := by
  ext x
  simp

/-- Differentiating the Schwartz Gaussian in direction `v` multiplies it by `-2 b ⟪·, v⟫`. -/
theorem lineDerivOp_gaussian {b : ℂ} (hb : 0 < b.re) (v : V) :
    ∂_{v} (gaussian hb : 𝓢(V, ℂ)) = (-2 * b) • innerMulGaussian hb v := by
  ext x
  rw [lineDerivOp_apply_eq_fderiv, coe_gaussian,
    (TauCeti.hasFDerivAt_cexp_neg_mul_norm_sq b x).fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, ofRealCLM_apply,
    innerSL_apply_apply, innerMulGaussian_apply, smul_eq_mul]
  ring

end InnerProductSpace

/-- The complex-plane Gaussian multiplied by the harmonic monomial `z^n`, as a Schwartz
function. Its conjugate-monomial counterpart is obtained by composition with `Complex.conjLIE`. -/
def complexPowMulGaussian {b : ℂ} (hb : 0 < b.re) (n : ℕ) : 𝓢(ℂ, ℂ) :=
  smulLeftCLM ℂ (fun z : ℂ ↦ z ^ n) (gaussian hb)

/-- Evaluation of the harmonic-monomial Schwartz Gaussian. -/
@[simp]
theorem complexPowMulGaussian_apply {b : ℂ} (hb : 0 < b.re) (n : ℕ) (z : ℂ) :
    complexPowMulGaussian hb n z = z ^ n * cexp (-b * ‖z‖ ^ 2) := by
  have hg : (fun z : ℂ ↦ z ^ n).HasTemperateGrowth := by
    fun_prop
  rw [complexPowMulGaussian, smulLeftCLM_apply_apply hg, gaussian_apply, smul_eq_mul]

/-- Angular degree zero recovers the unweighted Schwartz Gaussian. -/
@[simp]
theorem complexPowMulGaussian_zero {b : ℂ} (hb : 0 < b.re) :
    complexPowMulGaussian hb 0 = (gaussian hb : 𝓢(ℂ, ℂ)) := by
  ext z
  simp

/-- The conjugate Wirtinger derivative raises the angular degree by one. -/
theorem conjWirtingerDerivCLM_complexPowMulGaussian {b : ℂ} (hb : 0 < b.re) (n : ℕ) :
    conjWirtingerDerivCLM ℂ (complexPowMulGaussian hb n) =
      -b • complexPowMulGaussian hb (n + 1) := by
  ext z
  simp only [conjWirtingerDerivCLM_apply, smul_apply,
    funext (complexPowMulGaussian_apply hb n), complexPowMulGaussian_apply, smul_eq_mul,
    TauCeti.conjWirtingerDeriv_pow_mul_cexp_neg_mul_norm_sq, mul_assoc]

end SchwartzMap

namespace TauCeti

/-- **The Fourier transform of a linear form times a Gaussian** on a finite-dimensional real inner
product space `V` of dimension `d`, for `Re b > 0`:
`𝓕 (x ↦ ⟪x, v⟫ exp (-b ‖x‖²)) ξ = (π / b)^(d/2 + 1) (-i) ⟪ξ, v⟫ exp (-π² ‖ξ‖² / b)`. -/
theorem fourier_inner_mul_cexp_neg_mul_norm_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {b : ℂ} (hb : 0 < b.re) (v ξ : V) :
    𝓕 (fun x : V ↦ (⟪x, v⟫ : ℂ) * cexp (-b * ‖x‖ ^ 2)) ξ =
      (π / b) ^ (Module.finrank ℝ V / 2 + 1 : ℂ) * (-I) * (⟪ξ, v⟫ : ℂ) *
        cexp (-π ^ 2 * ‖ξ‖ ^ 2 / b) := by
  have hb0 : b ≠ 0 := fun h ↦ by simp [h] at hb
  have h2b0 : -2 * b ≠ 0 := mul_ne_zero (by norm_num) hb0
  have hpb0 : (π : ℂ) / b ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) hb0
  have h := congrArg (fun f : 𝓢(V, ℂ) ↦ f ξ)
    (SchwartzMap.fourier_lineDerivOp_eq (SchwartzMap.gaussian hb : 𝓢(V, ℂ)) v)
  rw [SchwartzMap.lineDerivOp_gaussian, FourierTransform.fourier_smul, smul_apply, smul_apply,
    SchwartzMap.smulLeftCLM_apply_apply (Function.hasTemperateGrowth_inner_left v),
    SchwartzMap.fourier_coe, SchwartzMap.fourier_coe,
    funext (SchwartzMap.innerMulGaussian_apply hb v), SchwartzMap.coe_gaussian,
    fourier_gaussian_innerProductSpace hb, Complex.real_smul, smul_eq_mul, smul_eq_mul] at h
  apply mul_left_cancel₀ h2b0
  rw [h, cpow_add _ _ hpb0, cpow_one]
  field_simp

/-- **The Fourier transform of `x exp (-b x²)` on `ℝ`** for `Re b > 0`:
`𝓕 (x ↦ x exp (-b x²)) ξ = (π / b)^(3/2) (-i) ξ exp (-π² ξ² / b)`. -/
theorem fourier_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (x : ℂ) * cexp (-b * (x : ℂ) ^ 2)) ξ =
      (π / b) ^ (3 / 2 : ℂ) * (-I) * (ξ : ℂ) * cexp (-π ^ 2 * (ξ : ℂ) ^ 2 / b) := by
  have h := fourier_inner_mul_cexp_neg_mul_norm_sq (V := ℝ) hb 1 ξ
  have hfun : (fun x : ℝ ↦ (⟪x, (1 : ℝ)⟫ : ℂ) * cexp (-b * ‖x‖ ^ 2)) =
      fun x : ℝ ↦ (x : ℂ) * cexp (-b * (x : ℂ) ^ 2) := by
    ext x
    simp [Real.norm_eq_abs, sq_abs, ← ofReal_pow]
  have hexp : (Module.finrank ℝ ℝ / 2 + 1 : ℂ) = 3 / 2 := by
    rw [Module.finrank_self]
    norm_num
  rw [hfun, hexp] at h
  simpa [Real.norm_eq_abs, sq_abs, ← ofReal_pow] using h

/-- **The Fourier transform of the homogeneous harmonic monomials `x^ε exp (-b x²)` on `ℝ`**
(`ε ≤ 1`, the only degrees in which `x^ε` is harmonic in dimension one, and `Re b > 0`):
`𝓕 (x ↦ x^ε exp (-b x²)) ξ = (π / b)^(1/2 + ε) (-i)^ε ξ^ε exp (-π² ξ² / b)`. -/
theorem fourier_pow_mul_cexp_neg_mul_sq_of_le_one {b : ℂ} (hb : 0 < b.re) {ε : ℕ} (hε : ε ≤ 1)
    (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (x : ℂ) ^ ε * cexp (-b * (x : ℂ) ^ 2)) ξ =
      (π / b) ^ ((1 / 2 : ℂ) + ε) * (-I) ^ ε * (ξ : ℂ) ^ ε *
        cexp (-π ^ 2 * (ξ : ℂ) ^ 2 / b) := by
  interval_cases ε
  · have h := fourier_gaussian_innerProductSpace (V := ℝ) hb ξ
    have hfun : (fun x : ℝ ↦ cexp (-b * ‖x‖ ^ 2)) =
        fun x : ℝ ↦ (x : ℂ) ^ 0 * cexp (-b * (x : ℂ) ^ 2) := by
      ext x
      simp [Real.norm_eq_abs, sq_abs, ← ofReal_pow]
    rw [hfun, Module.finrank_self] at h
    simpa [Real.norm_eq_abs, sq_abs, ← ofReal_pow] using h
  · have hexp : ((1 / 2 : ℂ) + ((1 : ℕ) : ℂ)) = 3 / 2 := by norm_num
    rw [hexp]
    simp_rw [pow_one]
    exact fourier_mul_cexp_neg_mul_sq hb ξ

/-- The Fourier transform of `z^n exp (-b ‖z‖²)` for `Re b > 0`, with Mathlib's
`exp (-2πi ⟪z, ξ⟫)` convention. -/
theorem fourier_pow_mul_cexp_neg_mul_norm_sq {b : ℂ} (hb : 0 < b.re) (n : ℕ) (ξ : ℂ) :
    𝓕 (fun z : ℂ ↦ z ^ n * cexp (-b * ‖z‖ ^ 2)) ξ =
      (π / b) ^ (n + 1) * (-I) ^ n * ξ ^ n * cexp (-π ^ 2 * ‖ξ‖ ^ 2 / b) := by
  have hb0 : b ≠ 0 := fun h ↦ by simp [h] at hb
  have hcoe (k : ℕ) : (SchwartzMap.complexPowMulGaussian hb k : ℂ → ℂ) =
      fun z ↦ z ^ k * cexp (-b * ‖z‖ ^ 2) :=
    funext (SchwartzMap.complexPowMulGaussian_apply hb k)
  induction n with
  | zero =>
    simpa only [pow_zero, one_mul, zero_add, pow_one, mul_one, Complex.finrank_real_complex,
      Nat.cast_ofNat, div_self (by norm_num : (2 : ℂ) ≠ 0), cpow_one] using
      fourier_gaussian_innerProductSpace hb ξ
  | succ n ih =>
    have h := SchwartzMap.fourier_conjWirtingerDerivCLM_apply
      (SchwartzMap.complexPowMulGaussian hb n) ξ
    rw [SchwartzMap.conjWirtingerDerivCLM_complexPowMulGaussian,
      FourierTransform.fourier_smul] at h
    simp only [smul_apply, smul_eq_mul,
      SchwartzMap.fourier_coe, hcoe, ih] at h
    apply mul_left_cancel₀ (neg_ne_zero.mpr hb0)
    rw [h]
    simp only [pow_succ]
    field_simp

/-- The conjugate angular monomial has the same Fourier scalar as the holomorphic one.
Complex conjugation here acts on the variable, not on the Gaussian parameter. -/
theorem fourier_conj_pow_mul_cexp_neg_mul_norm_sq {b : ℂ} (hb : 0 < b.re) (n : ℕ) (ξ : ℂ) :
    𝓕 (fun z : ℂ ↦ conj z ^ n * cexp (-b * ‖z‖ ^ 2)) ξ =
      (π / b) ^ (n + 1) * (-I) ^ n * conj ξ ^ n * cexp (-π ^ 2 * ‖ξ‖ ^ 2 / b) := by
  have h := Real.fourier_comp_linearIsometry conjLIE
    (fun z : ℂ ↦ z ^ n * cexp (-b * ‖z‖ ^ 2)) ξ
  simpa only [Function.comp_def, conjLIE_apply, norm_conj,
    fourier_pow_mul_cexp_neg_mul_norm_sq hb] using h

end TauCeti
