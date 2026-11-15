/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Schwartz
public import TauCeti.Analysis.Distribution.SchwartzSpace.Gaussian
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Complex harmonic monomials times Gaussians

The polynomials `z^n` and `conj(z)^n` are harmonic on the real plane. Multiplying either by
`exp (-b ‖z‖²)`, with `Re b > 0`, gives a Schwartz function whose Fourier transform is the
same monomial times a Gaussian, with scalar `(π / b)^(n+1) (-i)^n`.

These are the complex-place factors of the polynomial-weighted theta kernels used in Hecke's
method. In particular, at `b = π y`, the scalar is `y^(-n-1) (-i)^n`: the extra `y^(-n)`
beyond the ordinary Gaussian transform records the angular degree. Both orientations are
needed, since the sign of a character's angular frequency selects the monomial or its conjugate.

The proof uses the planar conjugate Wirtinger derivative, which kills `z^n` and turns the
Gaussian into `-b z` times itself. Its Fourier multiplier is `π i ξ`. The initial Gaussian
transform is Mathlib's `fourier_gaussian_innerProductSpace` (S. Gouëzel).

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§7–8, Hecke's lemma and the
  polynomial-weighted theta kernel.
-/

public noncomputable section

open Complex ComplexConjugate MeasureTheory
open scoped FourierTransform SchwartzMap Real

namespace TauCeti

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
