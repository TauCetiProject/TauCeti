/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Complex Gaussian exponential reproduction

The affine Gaussian integral on `ℂ` has independent holomorphic and antiholomorphic linear
terms. Finite products give its diagonal version on `ι → ℂ`, with no restriction on the finite
coordinate set. Conjugating any subset of the coordinates preserves the resulting exponential
reproducing identity. These are the Gaussian calculations underlying coherent states and the
Bargmann reproducing kernel; no space of holomorphic functions is constructed here.

## Main results

* `TauCeti.integral_cexp_neg_mul_norm_sq_add`: the scalar affine integral for `Re a > 0`.
* `TauCeti.integral_cexp_neg_sum_mul_norm_sq_add`: its finite-dimensional diagonal version.
* `TauCeti.integral_cexp_coordinate_conj` and `TauCeti.integrable_cexp_coordinate_conj`:
  integration and integrability after conjugating selected coordinates.
* `TauCeti.integral_cexp_reproducing`: exponential reproduction at any positive Gaussian scale.
* `TauCeti.integral_cexp_reproducing_pi`: reproduction in the `π` convention.
* `TauCeti.integral_cexp_gaussian_convolution`: the coherent-state kernel projection identity.

## Normalization

Write `N = Fintype.card ι` and `|z|² = ∑ i, ‖z i‖²`, the Euclidean square rather than the
square of the sup norm on `ι → ℂ`. At scale `t > 0` the Gaussian probability weight is
`(t/π)^N exp (-t |z|²) dz`. Thus `t = 1` uses `π^(-N) dz`, while `t = π` uses ordinary Lebesgue
measure and the weight `exp (-π |z|²)`. Explicitly, the coordinate dilation `u = √π z` has real
Jacobian `π^N`, so `π^(-N) du = dz` and `|u|² = π |z|²`. Dilation of the exponential parameters
by `√π` gives the two factors of `π` in `integral_cexp_reproducing_pi`. Real dilation commutes
with every coordinate conjugation. All integrals use Mathlib's native `MeasureTheory` measures.

## Provenance

`TauCeti.integral_cexp_neg_mul_norm_sq_add` adapts `New.Fock.integral_cexp_neg_star_mul`
(file `src/Lib/General/Analysis/GaussianIntegral.lean`) in grh-lean
(https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic, PBC).
The independent linear terms and the diagonal finite-product formulation are new here.
`TauCeti.integral_cexp_reproducing` and `TauCeti.integral_cexp_gaussian_convolution` adapt
`New.Fock.integral_exp_holomorphicCoord` and the convolution calculation in
`New.Fock.isVacuum_realVac` (file `src/Lib/Weil/Fock/Basic.lean`) in the same source.
The arbitrary positive scale is new here. The proofs use Mathlib's real Gaussian integral and
finite products in place of the source's general accretive-matrix theory.

## References

* V. Bargmann, *On a Hilbert space of analytic functions and an associated integral transform,
  part I*, Comm. Pure Appl. Math. 14 (1961), 187–214,
  https://doi.org/10.1002/cpa.3160140303.
-/

public section

open MeasureTheory Complex
open scoped ComplexConjugate
namespace TauCeti
/-- The affine complex Gaussian integral, with independent holomorphic and antiholomorphic
linear terms and a quadratic coefficient of positive real part. -/
theorem integral_cexp_neg_mul_norm_sq_add {a : ℂ} (ha : 0 < a.re) (b c : ℂ) :
    ∫ z : ℂ, exp (-a * (‖z‖ : ℂ) ^ 2 + b * z + c * conj z) =
      Real.pi / a * exp (b * c / a) := by
  -- In real coordinates the linear coefficients are b + c and i(b - c).
  let d : Fin 2 → ℂ := ![b + c, I * (b - c)]
  let g (v : Fin 2 → ℝ) : ℂ :=
    exp (-a * ∑ i, (v i : ℂ) ^ 2 + ∑ i, d i * v i)
  have h (z : ℂ) : exp (-a * (‖z‖ : ℂ) ^ 2 + b * z + c * conj z) =
      g (measurableEquivPi z) := by
    simp only [g, d, measurableEquivPi_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [← Complex.mul_conj']
    congr 1
    rw [← re_add_im z]
    simp only [map_add, map_mul, conj_ofReal, conj_I, add_re, add_im, mul_re, mul_im,
      ofReal_re, ofReal_im, I_re, I_im, mul_zero, mul_one, sub_zero, zero_add, add_zero]
    linear_combination a * (z.im : ℂ) ^ 2 * I_sq
  simp_rw [h]
  rw [volume_preserving_equiv_pi.integral_comp' g,
    GaussianFourier.integral_cexp_neg_mul_sum_add ha]
  simp only [Fintype.card_fin, Nat.cast_ofNat, div_self (two_ne_zero : (2 : ℂ) ≠ 0),
    cpow_one, d, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [mul_pow, I_sq]
  congr 2
  ring

/-- An affine complex Gaussian with quadratic coefficient of positive real part is integrable. -/
theorem integrable_cexp_neg_mul_norm_sq_add {a : ℂ} (ha : 0 < a.re) (b c : ℂ) :
    Integrable (fun z : ℂ ↦ exp (-a * (‖z‖ : ℂ) ^ 2 + b * z + c * conj z)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_cexp_neg_mul_norm_sq_add ha]
  exact mul_ne_zero (div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    (ne_of_apply_ne re (ne_of_gt ha))) (exp_ne_zero _)

variable {ι : Type*} [Fintype ι]

/-- The affine complex Gaussian integral for diagonal quadratic forms in finitely many
coordinates. The empty coordinate set is allowed. -/
theorem integral_cexp_neg_sum_mul_norm_sq_add {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).re) (b c : ι → ℂ) :
    ∫ z : ι → ℂ, exp (-∑ i, a i * (‖z i‖ : ℂ) ^ 2 +
      ∑ i, b i * z i + ∑ i, c i * conj (z i)) =
      (∏ i, Real.pi / a i) * exp (∑ i, b i * c i / a i) := by
  simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Complex.exp_sum]
  simp_rw [← neg_mul]
  rw [integral_fintype_prod_volume_eq_prod (f := fun i (z : ℂ) ↦
    exp (-a i * (‖z‖ : ℂ) ^ 2 + b i * z + c i * conj z))]
  simp_rw [integral_cexp_neg_mul_norm_sq_add (ha _)]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]

/-- Diagonal affine complex Gaussians are integrable when all quadratic coefficients have
positive real part. -/
theorem integrable_cexp_neg_sum_mul_norm_sq_add {a : ι → ℂ}
    (ha : ∀ i, 0 < (a i).re) (b c : ι → ℂ) :
    Integrable (fun z : ι → ℂ ↦ exp (-∑ i, a i * (‖z i‖ : ℂ) ^ 2 +
      ∑ i, b i * z i + ∑ i, c i * conj (z i))) := by
  simp_rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Complex.exp_sum]
  simp_rw [← neg_mul]
  exact Integrable.fintype_prod (f := fun i (z : ℂ) ↦
    exp (-a i * (‖z‖ : ℂ) ^ 2 + b i * z + c i * conj z))
    (fun i ↦ integrable_cexp_neg_mul_norm_sq_add (ha i) (b i) (c i))

/-- The exponential Gaussian integral is unchanged by conjugating any chosen coordinates.
The Boolean function `e` marks the coordinates to conjugate. -/
theorem integral_cexp_coordinate_conj {a : ℂ} (ha : 0 < a.re)
    (e : ι → Bool) (b c : ι → ℂ) :
    ∫ z : ι → ℂ,
      exp (∑ i, b i * (if e i then conj (z i) else z i)) *
      exp (∑ i, conj (if e i then conj (z i) else z i) * c i) *
      exp (-a * ∑ i, (‖z i‖ : ℂ) ^ 2) =
      (Real.pi / a) ^ Fintype.card ι * exp (∑ i, b i * c i / a) := by
  -- Conjugating a coordinate exchanges its two independent linear coefficients.
  let B i := if e i then c i else b i
  let C i := if e i then b i else c i
  have h (z : ι → ℂ) :
      (∑ i, b i * (if e i then conj (z i) else z i)) +
        (∑ i, conj (if e i then conj (z i) else z i) * c i) +
        (-a * ∑ i, (‖z i‖ : ℂ) ^ 2) =
      -∑ i, a * (‖z i‖ : ℂ) ^ 2 + ∑ i, B i * z i + ∑ i, C i * conj (z i) := by
    simp only [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases h : e i <;> simp [B, C, h] <;> ring
  simp_rw [← exp_add, h]
  rw [integral_cexp_neg_sum_mul_norm_sq_add (fun _ ↦ ha)]
  simp only [Finset.prod_const, Finset.card_univ]
  congr 2
  apply Finset.sum_congr rfl
  intro i _
  cases h : e i <;> simp [B, C, h, mul_comm]

/-- The exponential reproducing integrand is integrable, including after conjugation of
any chosen coordinates. -/
theorem integrable_cexp_coordinate_conj {a : ℂ} (ha : 0 < a.re)
    (e : ι → Bool) (b c : ι → ℂ) :
    Integrable (fun z : ι → ℂ ↦
      exp (∑ i, b i * (if e i then conj (z i) else z i)) *
      exp (∑ i, conj (if e i then conj (z i) else z i) * c i) *
      exp (-a * ∑ i, (‖z i‖ : ℂ) ^ 2)) := by
  apply Integrable.of_integral_ne_zero
  rw [integral_cexp_coordinate_conj ha]
  exact mul_ne_zero (pow_ne_zero _ (div_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    (ne_of_apply_ne re (ne_of_gt ha)))) (exp_ne_zero _)

/-- Gaussian integration reproduces exponentials in partially conjugated complex coordinates.
The measure is `(t / π)^N` times Lebesgue measure; its Gaussian weight is `exp (-t |z|²)`.
At `t = 1` this is the convention with Lebesgue measure divided by `π^N`. -/
theorem integral_cexp_reproducing {t : ℝ} (ht : 0 < t)
    (e : ι → Bool) (b w : ι → ℂ) :
    ∫ z : ι → ℂ,
      exp (∑ i, b i * (if e i then conj (z i) else z i)) *
      exp ((t : ℂ) * ∑ i, conj (if e i then conj (z i) else z i) * w i) *
      exp (-(t : ℂ) * ∑ i, (‖z i‖ : ℂ) ^ 2)
      ∂(ENNReal.ofReal ((t / Real.pi) ^ Fintype.card ι) • volume) =
      exp (∑ i, b i * w i) := by
  have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
  have hscale : ((t / Real.pi : ℝ) : ℂ) ^ Fintype.card ι *
      ((Real.pi : ℂ) / t) ^ Fintype.card ι = 1 := by
    rw [← mul_pow]
    push_cast
    field_simp [ht.ne', Real.pi_ne_zero]
    simp
  have h := integral_cexp_coordinate_conj (by simpa using ht : 0 < (t : ℂ).re)
    e b (fun i ↦ t * w i)
  simp only [Finset.mul_sum, ← mul_assoc, mul_comm _ (t : ℂ)] at h ⊢
  rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
  rw [h]
  simp only [mul_assoc, mul_div_cancel_left₀ _ ht0]
  rw [← mul_assoc, ofReal_pow, hscale, one_mul]

/-- Exponential reproduction for the weight `exp (-π |z|²)` and ordinary Lebesgue measure,
with the factor `π` in both linear exponents. -/
theorem integral_cexp_reproducing_pi (e : ι → Bool) (b w : ι → ℂ) :
    ∫ z : ι → ℂ,
      exp ((Real.pi : ℂ) * ∑ i, b i * (if e i then conj (z i) else z i)) *
      exp ((Real.pi : ℂ) * ∑ i, conj (if e i then conj (z i) else z i) * w i) *
      exp (-(Real.pi : ℂ) * ∑ i, (‖z i‖ : ℂ) ^ 2) =
      exp ((Real.pi : ℂ) * ∑ i, b i * w i) := by
  simpa only [div_self Real.pi_ne_zero, one_pow,
    ENNReal.ofReal_one, one_smul, Finset.mul_sum, mul_assoc] using
    integral_cexp_reproducing Real.pi_pos e (fun i ↦ (Real.pi : ℂ) * b i) w

/-- The Gaussian coherent-state kernel is idempotent under normalized convolution.
Here `K(x,y) = exp (-t |x|²/2 - t |y|²/2 + t ∑ conj(yᵢ) xᵢ)`; the identity is
`∫ K(x,z) K(z,y) (t/π)^N dz = K(x,y)`. -/
theorem integral_cexp_gaussian_convolution {t : ℝ} (ht : 0 < t) (x y : ι → ℂ) :
    ∫ z : ι → ℂ,
      exp (-(t : ℂ) / 2 * ∑ i, (‖x i‖ : ℂ) ^ 2 -
        (t : ℂ) / 2 * ∑ i, (‖z i‖ : ℂ) ^ 2 + t * ∑ i, conj (z i) * x i) *
      exp (-(t : ℂ) / 2 * ∑ i, (‖z i‖ : ℂ) ^ 2 -
        (t : ℂ) / 2 * ∑ i, (‖y i‖ : ℂ) ^ 2 + t * ∑ i, conj (y i) * z i)
      ∂(ENNReal.ofReal ((t / Real.pi) ^ Fintype.card ι) • volume) =
      exp (-(t : ℂ) / 2 * ∑ i, (‖x i‖ : ℂ) ^ 2 -
        (t : ℂ) / 2 * ∑ i, (‖y i‖ : ℂ) ^ 2 + t * ∑ i, conj (y i) * x i) := by
  -- Factor out the two external Gaussians, leaving an exponential reproducing integral.
  let A (u : ι → ℂ) := -(t : ℂ) / 2 * ∑ i, (‖u i‖ : ℂ) ^ 2
  have h (z : ι → ℂ) :
      exp (-(t : ℂ) / 2 * ∑ i, (‖x i‖ : ℂ) ^ 2 -
        (t : ℂ) / 2 * ∑ i, (‖z i‖ : ℂ) ^ 2 + t * ∑ i, conj (z i) * x i) *
      exp (-(t : ℂ) / 2 * ∑ i, (‖z i‖ : ℂ) ^ 2 -
        (t : ℂ) / 2 * ∑ i, (‖y i‖ : ℂ) ^ 2 + t * ∑ i, conj (y i) * z i) =
      exp (A x + A y) *
        (exp (∑ i, (t : ℂ) * conj (y i) * z i) *
          exp ((t : ℂ) * ∑ i, conj (z i) * x i) *
          exp (-(t : ℂ) * ∑ i, (‖z i‖ : ℂ) ^ 2)) := by
    simp only [← exp_add, A, ← Finset.mul_sum, mul_assoc]
    congr 1
    ring
  have hr := integral_cexp_reproducing ht (fun _ ↦ false) (fun i ↦ t * conj (y i)) x
  simp only [Bool.false_eq_true, ↓reduceIte] at hr
  simp_rw [h]
  rw [integral_const_mul, hr, ← exp_add]
  simp only [A, mul_assoc, ← Finset.mul_sum]
  congr 1
  ring

end TauCeti
