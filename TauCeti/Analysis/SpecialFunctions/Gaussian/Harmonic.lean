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
# Harmonic polynomials times Gaussians in one and two real dimensions

Linear forms `x ↦ ⟪x, v⟫` on a real inner product space and the planar monomials `z^n` and
`conj(z)^n` on `ℂ` are harmonic. Multiplying any of them by the Gaussian `exp (-b ‖x‖²)` with
`Re b > 0` gives a Schwartz function whose Fourier transform is the same harmonic polynomial times
a Gaussian:

* on a finite-dimensional real inner product space `V` of dimension `d`, `⟪x, v⟫ exp (-b ‖x‖²)` has
  Fourier transform `(π / b)^(d/2 + 1) (-i) ⟪ξ, v⟫ exp (-π² ‖ξ‖² / b)`; on `ℝ` this covers
  `x^e exp (-b ‖x‖²)` for `e ≤ 1`;
* on `ℂ`, both `z^n exp (-b ‖z‖²)` and `conj(z)^n exp (-b ‖z‖²)` have Fourier scalar
  `(π / b)^(n + 1) (-i)^n`, packaged for a signed angular frequency `k : ℤ` by
  `TauCeti.complexHarmonicMonomial`.

These are the real-place and complex-place factors of the polynomial-weighted theta kernels used in
Hecke's method. At `b = π y`, the scalar is `y^(-e - 1/2) (-i)^e` at a real place and
`y^(-|k| - 1) (-i)^|k|` at a complex place: the extra `y^(-e)` or `y^(-|k|)` beyond the ordinary
Gaussian transform records the harmonic degree. Both planar orientations are needed, since the sign
of a character's angular frequency selects the monomial or its conjugate.

On `V`, the directional derivative `∂_v` turns `exp (-b ‖x‖²)` into `-2b ⟪x, v⟫ exp (-b ‖x‖²)` and
acts as multiplication by `2πi ⟪ξ, v⟫` on the Fourier side. On `ℂ`, the planar conjugate Wirtinger
derivative kills `z^n`, turns the Gaussian into `-b z` times itself, and has Fourier multiplier
`πi ξ`. The initial Gaussian transform is Mathlib's `fourier_gaussian_innerProductSpace`
(S. Gouëzel).

## Main definitions

* `TauCeti.complexHarmonicMonomial`: the signed planar harmonic monomial `conj(z)^k` (`k ≥ 0`) or
  `z^(-k)` (`k < 0`).
* `SchwartzMap.complexPowMulGaussian`, `SchwartzMap.complexHarmonicGaussian`,
  `SchwartzMap.innerMulGaussian`: harmonic polynomials times Gaussians as Schwartz functions.

## Main results

* `TauCeti.fourier_inner_mul_cexp_neg_mul_norm_sq`: Fourier transform of `⟪x, v⟫ exp (-b ‖x‖²)` on
  a finite-dimensional real inner product space.
* `TauCeti.fourier_mul_cexp_neg_mul_norm_sq_real` and
  `TauCeti.fourier_pow_mul_cexp_neg_mul_norm_sq_real`: 1D specializations on `ℝ` (`e ≤ 1`).
* `TauCeti.fourier_pow_mul_cexp_neg_mul_norm_sq`,
  `TauCeti.fourier_conj_pow_mul_cexp_neg_mul_norm_sq`, and
  `TauCeti.fourier_complexHarmonicMonomial_mul_cexp_neg_mul_norm_sq`: planar Fourier transforms.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §§3, 7–8, Hecke's lemma and the
  polynomial-weighted theta kernel.
-/

public noncomputable section

open Complex ComplexConjugate MeasureTheory
open scoped ContDiff FourierTransform LineDeriv Real RealInnerProductSpace SchwartzMap

namespace TauCeti

/-! ### Directional derivative of a Euclidean Gaussian -/

/-- The directional derivative of the Gaussian `x ↦ exp (-b ‖x‖²)` on a real inner product space
along `v` is `-2b ⟪x, v⟫ exp (-b ‖x‖²)`. No positivity assumption on `b` is needed for this
differential identity. -/
theorem fderiv_cexp_neg_mul_norm_sq {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (b : ℂ) (x v : V) :
    fderiv ℝ (fun y : V ↦ cexp (-b * ‖y‖ ^ 2)) x v = -2 * b * ⟪x, v⟫ * cexp (-b * ‖x‖ ^ 2) := by
  have hsq : (fun y : V ↦ cexp (-b * ‖y‖ ^ 2)) =
      fun y : V ↦ cexp (-b * ((‖y‖ ^ 2 : ℝ) : ℂ)) := by
    ext y
    simp
  rw [hsq]
  have hinner := (ofRealCLM.hasFDerivAt.comp x (hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul
    (-b)
  have hexp := ((Complex.hasDerivAt_exp _).hasFDerivAt.restrictScalars ℝ).comp x hinner
  simp only [Function.comp_def, ofRealCLM_apply] at hexp
  rw [hexp.fderiv]
  simp only [ofReal_pow, neg_mul, ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_apply,
    smul_apply, coe_innerSL_apply, ofRealCLM_apply, nsmul_eq_mul, Nat.cast_ofNat, smul_eq_mul,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply, neg_inj,
    mul_eq_mul_right_iff, exp_ne_zero, or_false]
  rw [real_inner_comm]
  ring

/-! ### Planar Wirtinger derivatives of Gaussians -/

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

/-! ### Signed planar harmonic monomials -/

/-- The signed planar harmonic monomial attached to an angular frequency `k : ℤ`:
`conj z ^ k` for `0 ≤ k` and `z ^ (-k)` for `k < 0`. Both orientations have homogeneous degree
`k.natAbs` and norm `‖z‖ ^ k.natAbs`, and multiplying by `(z / ‖z‖) ^ k` cancels the phase to
`‖z‖ ^ k.natAbs`. -/
def complexHarmonicMonomial (k : ℤ) (z : ℂ) : ℂ :=
  if 0 ≤ k then conj z ^ k.toNat else z ^ (-k).toNat

/-- The defining formula of `complexHarmonicMonomial`. -/
theorem complexHarmonicMonomial_def (k : ℤ) (z : ℂ) :
    complexHarmonicMonomial k z = if 0 ≤ k then conj z ^ k.toNat else z ^ (-k).toNat :=
  (rfl)

/-- For a nonnegative angular frequency, `complexHarmonicMonomial` is the conjugate monomial
`conj z ^ k.toNat`. -/
theorem complexHarmonicMonomial_of_nonneg {k : ℤ} (hk : 0 ≤ k) (z : ℂ) :
    complexHarmonicMonomial k z = conj z ^ k.toNat := by
  simp [complexHarmonicMonomial, hk]

/-- For a nonpositive angular frequency, `complexHarmonicMonomial` is the holomorphic monomial
`z ^ (-k).toNat`. At `k = 0` both formulas equal `1`. -/
theorem complexHarmonicMonomial_of_nonpos {k : ℤ} (hk : k ≤ 0) (z : ℂ) :
    complexHarmonicMonomial k z = z ^ (-k).toNat := by
  rcases hk.eq_or_lt with rfl | hk'
  · simp [complexHarmonicMonomial]
  · simp [complexHarmonicMonomial, not_le.mpr hk']

@[simp]
theorem complexHarmonicMonomial_zero (z : ℂ) : complexHarmonicMonomial 0 z = 1 := by
  simp [complexHarmonicMonomial]

@[simp]
theorem complexHarmonicMonomial_natCast (n : ℕ) (z : ℂ) :
    complexHarmonicMonomial n z = conj z ^ n := by
  simp [complexHarmonicMonomial]

@[simp]
theorem complexHarmonicMonomial_neg_natCast (n : ℕ) (z : ℂ) :
    complexHarmonicMonomial (-n) z = z ^ n := by
  rw [complexHarmonicMonomial_of_nonpos (Int.neg_nonpos_of_nonneg (Nat.cast_nonneg n))]
  simp

@[simp]
theorem complexHarmonicMonomial_one (k : ℤ) : complexHarmonicMonomial k 1 = 1 := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simp

/-- At the origin, `complexHarmonicMonomial k 0` is `1` for `k = 0` and `0` otherwise. -/
theorem complexHarmonicMonomial_zero_right (k : ℤ) :
    complexHarmonicMonomial k 0 = if k = 0 then 1 else 0 := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, zero_pow hn]
  · rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [hn, zero_pow hn]

/-- `complexHarmonicMonomial k` is completely multiplicative in the complex variable. -/
theorem complexHarmonicMonomial_mul (k : ℤ) (z w : ℂ) :
    complexHarmonicMonomial k (z * w) =
      complexHarmonicMonomial k z * complexHarmonicMonomial k w := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simp [mul_pow]

/-- On the real axis, both orientations agree with the `k.natAbs`-th power. -/
@[simp]
theorem complexHarmonicMonomial_ofReal (k : ℤ) (r : ℝ) :
    complexHarmonicMonomial k r = (r : ℂ) ^ k.natAbs := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simp

/-- The norm of `complexHarmonicMonomial k z` is `‖z‖ ^ k.natAbs`. -/
@[simp]
theorem norm_complexHarmonicMonomial (k : ℤ) (z : ℂ) :
    ‖complexHarmonicMonomial k z‖ = ‖z‖ ^ k.natAbs := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simp

/-- Negating the angular frequency conjugates the harmonic monomial. -/
theorem complexHarmonicMonomial_neg (k : ℤ) (z : ℂ) :
    complexHarmonicMonomial (-k) z = conj (complexHarmonicMonomial k z) := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simp

/-- Conjugating the variable negates the angular frequency of the harmonic monomial. -/
theorem complexHarmonicMonomial_conj (k : ℤ) (z : ℂ) :
    complexHarmonicMonomial k (conj z) = complexHarmonicMonomial (-k) z := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩ <;> simp

/-- Multiplying `complexHarmonicMonomial k z` by `(z / ‖z‖) ^ k` cancels the phase and leaves the
radial power `‖z‖ ^ k.natAbs` (including at `z = 0`, where both sides equal `1` for `k = 0` and `0`
otherwise). -/
theorem angular_mul_complexHarmonicMonomial (k : ℤ) (z : ℂ) :
    (z / ‖z‖) ^ k * complexHarmonicMonomial k z = (‖z‖ : ℂ) ^ k.natAbs := by
  rcases eq_or_ne z 0 with rfl | hz
  · rcases eq_or_ne k 0 with rfl | hk
    · simp
    · simp [zero_zpow k hk, complexHarmonicMonomial_zero_right, hk,
        zero_pow (Int.natAbs_ne_zero.mpr hk)]
  · have hnorm : (‖z‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
    rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩
    · simp only [zpow_natCast, complexHarmonicMonomial_natCast, Int.natAbs_natCast, ← mul_pow]
      congr 1
      rw [div_mul_eq_mul_div, mul_conj, normSq_eq_norm_sq, ofReal_pow, sq,
        mul_div_cancel_right₀ _ hnorm]
    · simp only [zpow_neg, zpow_natCast, complexHarmonicMonomial_neg_natCast, Int.natAbs_neg,
        Int.natAbs_natCast, ← inv_pow, inv_div, ← mul_pow, div_mul_cancel₀ _ hz]

@[fun_prop]
theorem contDiff_complexHarmonicMonomial (k : ℤ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (complexHarmonicMonomial k) := by
  rcases k.eq_nat_or_neg with ⟨m, rfl | rfl⟩
  · have heq : complexHarmonicMonomial (m : ℤ) = fun z : ℂ ↦ conjCLE z ^ m :=
      funext (complexHarmonicMonomial_natCast m)
    rw [heq]
    exact conjCLE.contDiff.pow m
  · have heq : complexHarmonicMonomial (-(m : ℤ)) = fun z : ℂ ↦ z ^ m :=
      funext (complexHarmonicMonomial_neg_natCast m)
    rw [heq]
    exact contDiff_id.pow m

@[fun_prop]
theorem continuous_complexHarmonicMonomial (k : ℤ) : Continuous (complexHarmonicMonomial k) :=
  (contDiff_complexHarmonicMonomial k (n := 0)).continuous

@[fun_prop]
theorem hasTemperateGrowth_complexHarmonicMonomial (k : ℤ) :
    (complexHarmonicMonomial k).HasTemperateGrowth := by
  rcases k.eq_nat_or_neg with ⟨m, rfl | rfl⟩
  · have heq : complexHarmonicMonomial (m : ℤ) = fun z : ℂ ↦ conjCLE z ^ m :=
      funext (complexHarmonicMonomial_natCast m)
    rw [heq]
    exact (conjCLE.toContinuousLinearMap.hasTemperateGrowth).pow m
  · have heq : complexHarmonicMonomial (-(m : ℤ)) = fun z : ℂ ↦ z ^ m :=
      funext (complexHarmonicMonomial_neg_natCast m)
    rw [heq]
    fun_prop

end TauCeti

namespace SchwartzMap

/-- The Euclidean Gaussian multiplied by the linear form `x ↦ ⟪x, v⟫`, as a Schwartz function. -/
def innerMulGaussian {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {b : ℂ} (hb : 0 < b.re) (v : V) : 𝓢(V, ℂ) :=
  smulLeftCLM ℂ (fun x : V ↦ (⟪x, v⟫ : ℂ)) (gaussian hb)

/-- The defining equation of `innerMulGaussian`. -/
theorem innerMulGaussian_def {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {b : ℂ} (hb : 0 < b.re) (v : V) :
    innerMulGaussian hb v = smulLeftCLM ℂ (fun x : V ↦ (⟪x, v⟫ : ℂ)) (gaussian hb) :=
  (rfl)

@[simp]
theorem innerMulGaussian_apply {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {b : ℂ} (hb : 0 < b.re) (v x : V) :
    innerMulGaussian hb v x = (⟪x, v⟫ : ℂ) * cexp (-b * ‖x‖ ^ 2) := by
  have hg : (fun x : V ↦ (⟪x, v⟫ : ℂ)).HasTemperateGrowth :=
    Complex.hasTemperateGrowth_ofReal.comp (by fun_prop : (inner ℝ · v : V → ℝ).HasTemperateGrowth)
  rw [innerMulGaussian, smulLeftCLM_apply_apply hg, gaussian_apply, smul_eq_mul]

/-- The directional derivative of `SchwartzMap.gaussian` along `v` is `-2b` times
`innerMulGaussian hb v`. -/
theorem lineDerivOp_gaussian {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {b : ℂ} (hb : 0 < b.re) (v : V) :
    ∂_{v} (gaussian (V := V) hb) = (-2 * b) • innerMulGaussian hb v := by
  ext x
  rw [lineDerivOp_apply_eq_fderiv, smul_apply, innerMulGaussian_apply, smul_eq_mul, coe_gaussian,
    TauCeti.fderiv_cexp_neg_mul_norm_sq, mul_assoc]

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

/-- The complex-plane Gaussian multiplied by the signed harmonic monomial
`TauCeti.complexHarmonicMonomial k`, as a Schwartz function. -/
def complexHarmonicGaussian {b : ℂ} (hb : 0 < b.re) (k : ℤ) : 𝓢(ℂ, ℂ) :=
  smulLeftCLM ℂ (TauCeti.complexHarmonicMonomial k) (gaussian hb)

/-- The defining equation of `complexHarmonicGaussian`. -/
theorem complexHarmonicGaussian_def {b : ℂ} (hb : 0 < b.re) (k : ℤ) :
    complexHarmonicGaussian hb k =
      smulLeftCLM ℂ (TauCeti.complexHarmonicMonomial k) (gaussian hb) :=
  (rfl)

@[simp]
theorem complexHarmonicGaussian_apply {b : ℂ} (hb : 0 < b.re) (k : ℤ) (z : ℂ) :
    complexHarmonicGaussian hb k z =
      TauCeti.complexHarmonicMonomial k z * cexp (-b * ‖z‖ ^ 2) := by
  rw [complexHarmonicGaussian,
    smulLeftCLM_apply_apply (TauCeti.hasTemperateGrowth_complexHarmonicMonomial k),
    gaussian_apply, smul_eq_mul]

@[simp]
theorem complexHarmonicGaussian_zero {b : ℂ} (hb : 0 < b.re) :
    complexHarmonicGaussian hb 0 = (gaussian hb : 𝓢(ℂ, ℂ)) := by
  ext z
  simp

end SchwartzMap

namespace TauCeti

/-! ### Fourier transforms of harmonic Gaussians -/

/-- **The Fourier transform of a linear form times a Gaussian** on a finite-dimensional real inner
product space `V` of dimension `d`, for `Re b > 0`:
`𝓕 (fun x ↦ ⟪x, v⟫ exp (-b ‖x‖²)) ξ = (π / b)^(d / 2 + 1) (-i) ⟪ξ, v⟫ exp (-π² ‖ξ‖² / b)`. -/
theorem fourier_inner_mul_cexp_neg_mul_norm_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    {b : ℂ} (hb : 0 < b.re) (v ξ : V) :
    𝓕 (fun x : V ↦ (⟪x, v⟫ : ℂ) * cexp (-b * ‖x‖ ^ 2)) ξ =
      (π / b) ^ (Module.finrank ℝ V / 2 + 1 : ℂ) * (-I) * ⟪ξ, v⟫ *
        cexp (-π ^ 2 * ‖ξ‖ ^ 2 / b) := by
  have hb0 : b ≠ 0 := fun h ↦ by simp [h] at hb
  have h2b : -2 * b ≠ 0 := mul_ne_zero (by norm_num) hb0
  have hpb : (π / b : ℂ) ≠ 0 := div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) hb0
  have h := SchwartzMap.fourier_lineDerivOp_apply (SchwartzMap.gaussian hb) v ξ
  rw [SchwartzMap.lineDerivOp_gaussian hb v, FourierTransform.fourier_smul] at h
  simp only [smul_apply, smul_eq_mul, SchwartzMap.fourier_coe,
    funext (SchwartzMap.innerMulGaussian_apply hb v), SchwartzMap.coe_gaussian,
    fourier_gaussian_innerProductSpace hb] at h
  apply mul_left_cancel₀ h2b
  rw [h, cpow_add _ _ hpb, cpow_one]
  field_simp

/-- The one-dimensional Fourier transform of `x exp (-b ‖x‖²)` on `ℝ` for `Re b > 0`. -/
theorem fourier_mul_cexp_neg_mul_norm_sq_real {b : ℂ} (hb : 0 < b.re) (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (x : ℂ) * cexp (-b * ‖x‖ ^ 2)) ξ =
      (π / b) ^ (3 / 2 : ℂ) * (-I) * ξ * cexp (-π ^ 2 * ‖ξ‖ ^ 2 / b) := by
  have h := fourier_inner_mul_cexp_neg_mul_norm_sq hb (1 : ℝ) ξ
  simp only [RCLike.inner_apply, conj_trivial, one_mul, Module.finrank_self, Nat.cast_one] at h
  rwa [show (1 / 2 + 1 : ℂ) = 3 / 2 by norm_num] at h

/-- The one-dimensional Fourier transform of `x^e exp (-b ‖x‖²)` on `ℝ` for `Re b > 0` and
`e ≤ 1` (the two harmonic degrees in dimension one). -/
theorem fourier_pow_mul_cexp_neg_mul_norm_sq_real {b : ℂ} (hb : 0 < b.re) {e : ℕ} (he : e ≤ 1)
    (ξ : ℝ) :
    𝓕 (fun x : ℝ ↦ (x : ℂ) ^ e * cexp (-b * ‖x‖ ^ 2)) ξ =
      (π / b) ^ ((e : ℂ) + 1 / 2) * (-I) ^ e * (ξ : ℂ) ^ e * cexp (-π ^ 2 * ‖ξ‖ ^ 2 / b) := by
  interval_cases e
  · simpa [Module.finrank_self] using fourier_gaussian_innerProductSpace hb ξ
  · simp_rw [Nat.cast_one, show (1 + 1 / 2 : ℂ) = 3 / 2 by norm_num, pow_one]
    exact fourier_mul_cexp_neg_mul_norm_sq_real hb ξ

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

/-- **The planar Fourier transform of a signed harmonic monomial times a Gaussian**: for any
`k : ℤ` and `Re b > 0`, `complexHarmonicMonomial k z * exp (-b ‖z‖²)` transforms into itself at `ξ`
with Gaussian parameter `π² / b` and scalar `(π / b) ^ (k.natAbs + 1) * (-I) ^ k.natAbs`. -/
theorem fourier_complexHarmonicMonomial_mul_cexp_neg_mul_norm_sq {b : ℂ} (hb : 0 < b.re)
    (k : ℤ) (ξ : ℂ) :
    𝓕 (fun z : ℂ ↦ complexHarmonicMonomial k z * cexp (-b * ‖z‖ ^ 2)) ξ =
      (π / b) ^ (k.natAbs + 1) * (-I) ^ k.natAbs * complexHarmonicMonomial k ξ *
        cexp (-π ^ 2 * ‖ξ‖ ^ 2 / b) := by
  rcases k.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simpa using fourier_conj_pow_mul_cexp_neg_mul_norm_sq hb n ξ
  · simpa using fourier_pow_mul_cexp_neg_mul_norm_sq hb n ξ

end TauCeti
