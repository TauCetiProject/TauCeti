/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta
import TauCeti.Analysis.SpecialFunctions.Beta.Basic
import TauCeti.MeasureTheory.Function.BoundedSupportExponential
import TauCeti.MeasureTheory.Function.PolynomialMemLp
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity

/-!
# The Jacobi measure

The Jacobi polynomials `Pₙ^{(α,β)}` are orthogonal for the weight `(1 - x) ^ α * (1 + x) ^ β` on
the interval `(-1, 1)`. This file defines the corresponding measure `Polynomial.jacobiMeasure α β`,
Lebesgue measure on `Set.Ioo (-1) 1` weighted by that density, and records the facts about it that
the Jacobi orthogonality relation and the Jacobi `L²` bases consume.

On `(-1, 1)` both `1 - x` and `1 + x` are positive, so the real powers are the classical ones. The
affine substitution `x = 2t - 1` turns the weight into `2 ^ (α + β)` times the integrand of Euler's
Beta integral, so every mixed moment is a value of the Beta function `ProbabilityTheory.beta`:

`∫ (1 - x) ^ s (1 + x) ^ t ∂(jacobiMeasure α β) = 2 ^ (s + α + (t + β) + 1) B(s + α + 1, t + β + 1)`

whenever `-1 < s + α` and `-1 < t + β`. At `s = t = 0` this is the total mass
`2 ^ (α + β + 1) * B(α + 1, β + 1)`, and the measure is finite exactly when `-1 < α` and
`-1 < β`: otherwise the density is not integrable at `1` or at `-1`. The moment formula holds
for all parameters, including those where the measure is infinite.

Being finite and concentrated on `(-1, 1)` for `-1 < α`, `-1 < β`, the measure has every
exponential moment `∫ exp (a * |x|) < ∞`. This is the hypothesis of the moment-determinacy
argument behind `TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`, the density of
polynomials in `L²(jacobiMeasure α β)`. At `α = β = 0` the measure is Lebesgue measure on
`(-1, 1)`, the Legendre case.

## Main definitions

* `Polynomial.jacobiMeasure α β`: the measure `(1 - x) ^ α (1 + x) ^ β dx` on `(-1, 1)`.

## Main statements

* `Polynomial.integrableOn_jacobiWeight_iff`, `Polynomial.integral_jacobiWeight`: the weight is
  integrable on `(-1, 1)` iff `-1 < α` and `-1 < β`, with integral
  `2 ^ (α + β + 1) B(α + 1, β + 1)`.
* `Polynomial.integral_jacobiMeasure`: integration against the Jacobi measure as a weighted
  integral over `Set.Ioo (-1) 1`.
* `Polynomial.integral_one_sub_rpow_mul_one_add_rpow_jacobiMeasure`: the mixed moments.
* `Polynomial.jacobiMeasure_univ`: the total mass is `2 ^ (α + β + 1) B(α + 1, β + 1)`.
* `Polynomial.isFiniteMeasure_jacobiMeasure_iff`: the measure is finite iff `-1 < α` and `-1 < β`.
* `Polynomial.integrable_exp_mul_abs_jacobiMeasure`: the finite exponential moments.
* `Polynomial.integrable_eval_jacobiMeasure`: polynomials are integrable.
* `Polynomial.jacobiMeasure_zero_zero`: at `α = β = 0` the measure is Lebesgue measure on
  `(-1, 1)`.

## References

* DLMF, *NIST Digital Library of Mathematical Functions*, <https://dlmf.nist.gov>, Table 18.3.1
  (the Jacobi weight) and 5.12.1 (Euler's Beta integral).
* G. Szegő, *Orthogonal Polynomials*, AMS Colloquium Publications 23, Ch. IV.
-/

public section

open MeasureTheory ProbabilityTheory Real Set

namespace Polynomial

/-! ### The Jacobi weight on `(-1, 1)` -/

/-- Along `x = 2t - 1` the Jacobi weight on `[0, 1]` is `2 ^ (a + b)` times the integrand of the
Beta integral `B(b + 1, a + 1)`, in the shape of `TauCeti.integral_rpow_mul_one_sub_rpow`. -/
private theorem jacobiWeight_two_mul_sub_one (a b : ℝ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - (2 * t - 1)) ^ a * (1 + (2 * t - 1)) ^ b =
      2 ^ (a + b) * (t ^ (b + 1 - 1) * (1 - t) ^ (a + 1 - 1)) := by
  have h1 : 1 - (2 * t - 1) = 2 * (1 - t) := by ring
  have h2 : 1 + (2 * t - 1) = 2 * t := by ring
  rw [h1, h2, mul_rpow zero_le_two (sub_nonneg.2 ht.2), mul_rpow zero_le_two ht.1,
    rpow_add two_pos, add_sub_cancel_right, add_sub_cancel_right]
  ring

/-- The substitution `x = 2t - 1` identifies interval integrability of the Jacobi weight on
`[-1, 1]` with that of the Beta integrand on `[0, 1]`. -/
private theorem intervalIntegrable_jacobiWeight_iff (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => (1 - x) ^ a * (1 + x) ^ b) volume (-1) 1 ↔
      IntervalIntegrable (fun t : ℝ => t ^ (b + 1 - 1) * (1 - t) ^ (a + 1 - 1)) volume 0 1 := by
  set w : ℝ → ℝ := fun x => (1 - x) ^ a * (1 + x) ^ b
  have h := (IntervalIntegrable.comp_mul_left_iff (f := fun x => w (x - 1)) (a := -1 + 1)
    (b := 1 + 1) two_ne_zero).trans
    (IntervalIntegrable.comp_sub_right_iff (f := w) (a := -1) (b := 1) (c := 1))
  have e0 : (-1 + 1 : ℝ) / 2 = 0 := by norm_num
  have e1 : (1 + 1 : ℝ) / 2 = 1 := by norm_num
  rw [e0, e1] at h
  rw [← h, intervalIntegrable_congr (g := fun t => 2 ^ (a + b) *
    (t ^ (b + 1 - 1) * (1 - t) ^ (a + 1 - 1))) fun t ht => jacobiWeight_two_mul_sub_one a b
      (Ioc_subset_Icc_self ((uIoc_of_le (zero_le_one : (0 : ℝ) ≤ 1)) ▸ ht))]
  refine ⟨fun hg => ?_, fun hg => hg.const_mul _⟩
  have := hg.const_mul (2 ^ (a + b))⁻¹
  simp_rw [← mul_assoc, inv_mul_cancel₀ (rpow_pos_of_pos two_pos (a + b)).ne', one_mul] at this
  exact this

/-- **The Jacobi weight is integrable exactly in the orthogonality range**: the function
`(1 - x) ^ a * (1 + x) ^ b` is integrable on `(-1, 1)` iff `-1 < a` and `-1 < b`. For `a ≤ -1` it
fails at `1`, and for `b ≤ -1` at `-1`. -/
theorem integrableOn_jacobiWeight_iff {a b : ℝ} :
    IntegrableOn (fun x : ℝ => (1 - x) ^ a * (1 + x) ^ b) (Ioo (-1) 1) ↔ -1 < a ∧ -1 < b := by
  rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num),
    intervalIntegrable_jacobiWeight_iff, intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one,
    TauCeti.integrableOn_rpow_mul_one_sub_rpow_iff]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **The Jacobi weight integral.** For `-1 < a` and `-1 < b`,
`∫₋₁¹ (1 - x) ^ a (1 + x) ^ b dx = 2 ^ (a + b + 1) B(a + 1, b + 1)`, by the substitution
`x = 2t - 1` in Euler's Beta integral. -/
theorem integral_jacobiWeight {a b : ℝ} (ha : -1 < a) (hb : -1 < b) :
    ∫ x in Ioo (-1) 1, (1 - x) ^ a * (1 + x) ^ b = 2 ^ (a + b + 1) * beta (a + 1) (b + 1) := by
  have h := intervalIntegral.smul_integral_comp_mul_add
    (fun x : ℝ => (1 - x) ^ a * (1 + x) ^ b) (a := 0) (b := 1) 2 (-1)
  have e0 : (2 : ℝ) * 0 + -1 = -1 := by norm_num
  have e1 : (2 : ℝ) * 1 + -1 = 1 := by norm_num
  rw [e0, e1] at h
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num), ← h,
    intervalIntegral.integral_congr (g := fun t => 2 ^ (a + b) *
      (t ^ (b + 1 - 1) * (1 - t) ^ (a + 1 - 1))) fun t ht => by
        simpa only [← sub_eq_add_neg] using jacobiWeight_two_mul_sub_one a b
          ((uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)) ▸ ht),
    intervalIntegral.integral_const_mul,
    TauCeti.integral_rpow_mul_one_sub_rpow (by linarith) (by linarith), beta_comm, smul_eq_mul,
    rpow_add two_pos (a + b) 1, rpow_one]
  ring

/-! ### The measure -/

/-- The **Jacobi measure** with parameters `α` and `β`: Lebesgue measure on `(-1, 1)` weighted by
`(1 - x) ^ α * (1 + x) ^ β`, the orthogonality measure of the Jacobi polynomials. It is finite
exactly when `-1 < α` and `-1 < β` (`Polynomial.isFiniteMeasure_jacobiMeasure_iff`). -/
noncomputable def jacobiMeasure (α β : ℝ) : Measure ℝ :=
  (volume.restrict (Ioo (-1) 1)).withDensity fun x => ENNReal.ofReal ((1 - x) ^ α * (1 + x) ^ β)

/-- Unfolds `Polynomial.jacobiMeasure` to the weighted restricted Lebesgue measure, the shape in
which `TauCeti.hilbertBasisOfWeightedMeasure` takes its measure. -/
theorem jacobiMeasure_def (α β : ℝ) :
    jacobiMeasure α β =
      (volume.restrict (Ioo (-1) 1)).withDensity
        fun x => ENNReal.ofReal ((1 - x) ^ α * (1 + x) ^ β) :=
  (rfl)

/-- The Jacobi measure is sigma-finite for all parameters, unlike `IsFiniteMeasure`, which needs
`-1 < α` and `-1 < β`. -/
instance sigmaFinite_jacobiMeasure (α β : ℝ) : SigmaFinite (jacobiMeasure α β) := by
  rw [jacobiMeasure_def]
  infer_instance

/-- At `α = β = 0` the Jacobi measure is Lebesgue measure on `(-1, 1)`, the orthogonality
measure of the Legendre polynomials. -/
@[simp]
theorem jacobiMeasure_zero_zero : jacobiMeasure 0 0 = volume.restrict (Ioo (-1) 1) := by
  simp only [jacobiMeasure_def, rpow_zero, mul_one, ENNReal.ofReal_one]
  exact withDensity_one

/-- The Jacobi weight `(1 - x) ^ α * (1 + x) ^ β` is a.e. measurable for Lebesgue measure on
`(-1, 1)`. -/
theorem aemeasurable_jacobiWeight (α β : ℝ) :
    AEMeasurable (fun x : ℝ => (1 - x) ^ α * (1 + x) ^ β) (volume.restrict (Ioo (-1) 1)) := by
  fun_prop

/-- The Jacobi weight `(1 - x) ^ α * (1 + x) ^ β` is positive at every point of `(-1, 1)`. -/
theorem ae_pos_jacobiWeight (α β : ℝ) :
    ∀ᵐ x ∂(volume.restrict (Ioo (-1 : ℝ) 1)), 0 < (1 - x) ^ α * (1 + x) ^ β :=
  ae_restrict_of_forall_mem measurableSet_Ioo fun _ hx =>
    mul_pos (rpow_pos_of_pos (by linarith [hx.2]) α) (rpow_pos_of_pos (by linarith [hx.1]) β)

/-- The Jacobi measure is concentrated on `(-1, 1)`. -/
theorem ae_mem_Ioo_jacobiMeasure (α β : ℝ) : ∀ᵐ x ∂jacobiMeasure α β, x ∈ Ioo (-1 : ℝ) 1 :=
  (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioo)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {α β : ℝ}

/-- Integration against the Jacobi measure is integration over `(-1, 1)` against the weight
`(1 - x) ^ α * (1 + x) ^ β`. No integrability is needed: when the integrand is not integrable
both sides are `0`. -/
theorem integral_jacobiMeasure (f : ℝ → E) :
    ∫ x, f x ∂jacobiMeasure α β = ∫ x in Ioo (-1) 1, ((1 - x) ^ α * (1 + x) ^ β) • f x :=
  TauCeti.MeasureTheory.integral_withDensity_ofReal (aemeasurable_jacobiWeight α β)
    ((ae_pos_jacobiWeight α β).mono fun _ hx => hx.le) f

/-- A function is integrable against the Jacobi measure iff its product with the weight
`(1 - x) ^ α * (1 + x) ^ β` is integrable on `(-1, 1)`. -/
theorem integrable_jacobiMeasure_iff {f : ℝ → E} :
    Integrable f (jacobiMeasure α β) ↔
      IntegrableOn (fun x => ((1 - x) ^ α * (1 + x) ^ β) • f x) (Ioo (-1) 1) :=
  TauCeti.MeasureTheory.integrable_withDensity_ofReal_iff (aemeasurable_jacobiWeight α β)
    ((ae_pos_jacobiWeight α β).mono fun _ hx => hx.le)

/-! ### Moments -/

/-- On `(-1, 1)` the weighted mixed power is the Jacobi weight with shifted exponents. -/
private theorem jacobiWeight_smul_one_sub_rpow_mul_one_add_rpow (s t : ℝ) {x : ℝ}
    (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ((1 - x) ^ α * (1 + x) ^ β) • ((1 - x) ^ s * (1 + x) ^ t) =
      (1 - x) ^ (s + α) * (1 + x) ^ (t + β) := by
  rw [smul_eq_mul, rpow_add (by linarith [hx.2]), rpow_add (by linarith [hx.1])]
  ring

/-- The mixed power `(1 - x) ^ s * (1 + x) ^ t` is integrable against the Jacobi measure when
`-1 < s + α` and `-1 < t + β`. -/
theorem integrable_one_sub_rpow_mul_one_add_rpow_jacobiMeasure {s t : ℝ} (hs : -1 < s + α)
    (ht : -1 < t + β) :
    Integrable (fun x : ℝ => (1 - x) ^ s * (1 + x) ^ t) (jacobiMeasure α β) := by
  rw [integrable_jacobiMeasure_iff]
  exact (integrableOn_jacobiWeight_iff.2 ⟨hs, ht⟩).congr_fun
    (fun x hx => (jacobiWeight_smul_one_sub_rpow_mul_one_add_rpow s t hx).symm) measurableSet_Ioo

/-- **The mixed moments of the Jacobi measure** are values of the Beta function: for
`-1 < s + α` and `-1 < t + β`, the integral `∫ (1 - x) ^ s (1 + x) ^ t ∂(jacobiMeasure α β)` is
`2 ^ (s + α + (t + β) + 1) B(s + α + 1, t + β + 1)`. -/
theorem integral_one_sub_rpow_mul_one_add_rpow_jacobiMeasure {s t : ℝ} (hs : -1 < s + α)
    (ht : -1 < t + β) :
    ∫ x, (1 - x) ^ s * (1 + x) ^ t ∂jacobiMeasure α β =
      2 ^ (s + α + (t + β) + 1) * beta (s + α + 1) (t + β + 1) := by
  rw [integral_jacobiMeasure, ← integral_jacobiWeight hs ht]
  exact setIntegral_congr_fun measurableSet_Ioo fun x hx =>
    jacobiWeight_smul_one_sub_rpow_mul_one_add_rpow s t hx

/-- The mixed monomial `(1 - x) ^ i * (1 + x) ^ j` is integrable against the Jacobi measure when
`-1 < i + α` and `-1 < j + β`. -/
theorem integrable_one_sub_pow_mul_one_add_pow_jacobiMeasure {i j : ℕ} (hi : -1 < i + α)
    (hj : -1 < j + β) :
    Integrable (fun x : ℝ => (1 - x) ^ i * (1 + x) ^ j) (jacobiMeasure α β) := by
  simpa only [rpow_natCast] using
    integrable_one_sub_rpow_mul_one_add_rpow_jacobiMeasure (s := i) (t := j) hi hj

/-- The integer mixed moments of the Jacobi measure:
`∫ (1 - x) ^ i (1 + x) ^ j ∂(jacobiMeasure α β) = 2 ^ (i + α + (j + β) + 1) B(i + α + 1, j + β + 1)`
when `-1 < i + α` and `-1 < j + β`. -/
theorem integral_one_sub_pow_mul_one_add_pow_jacobiMeasure {i j : ℕ} (hi : -1 < i + α)
    (hj : -1 < j + β) :
    ∫ x, (1 - x) ^ i * (1 + x) ^ j ∂jacobiMeasure α β =
      2 ^ (i + α + (j + β) + 1) * beta (i + α + 1) (j + β + 1) := by
  simpa only [rpow_natCast] using
    integral_one_sub_rpow_mul_one_add_rpow_jacobiMeasure (s := i) (t := j) hi hj

/-! ### Total mass and finiteness -/

/-- The total mass of the Jacobi measure, as a real number, is `2 ^ (α + β + 1) B(α + 1, β + 1)`
when `-1 < α` and `-1 < β`. -/
theorem jacobiMeasure_real_univ (hα : -1 < α) (hβ : -1 < β) :
    (jacobiMeasure α β).real univ = 2 ^ (α + β + 1) * beta (α + 1) (β + 1) := by
  simpa using integral_one_sub_rpow_mul_one_add_rpow_jacobiMeasure (α := α) (β := β) (s := 0)
    (t := 0) (by linarith) (by linarith)

/-- **The Jacobi measure is finite exactly when `-1 < α` and `-1 < β`.** For `α ≤ -1` the density
is not integrable at `1`, and for `β ≤ -1` not at `-1`. -/
theorem isFiniteMeasure_jacobiMeasure_iff :
    IsFiniteMeasure (jacobiMeasure α β) ↔ -1 < α ∧ -1 < β := by
  rw [← integrable_const_iff_isFiniteMeasure (one_ne_zero (α := ℝ)), integrable_jacobiMeasure_iff,
    ← integrableOn_jacobiWeight_iff]
  simp only [smul_eq_mul, mul_one]

/-- The Jacobi measure is finite when `-1 < α` and `-1 < β`. -/
theorem isFiniteMeasure_jacobiMeasure (hα : -1 < α) (hβ : -1 < β) :
    IsFiniteMeasure (jacobiMeasure α β) :=
  isFiniteMeasure_jacobiMeasure_iff.2 ⟨hα, hβ⟩

/-- **The total mass of the Jacobi measure** is `2 ^ (α + β + 1) B(α + 1, β + 1)` when `-1 < α`
and `-1 < β`. -/
theorem jacobiMeasure_univ (hα : -1 < α) (hβ : -1 < β) :
    jacobiMeasure α β univ = ENNReal.ofReal (2 ^ (α + β + 1) * beta (α + 1) (β + 1)) := by
  have := isFiniteMeasure_jacobiMeasure hα hβ
  rw [← jacobiMeasure_real_univ hα hβ, ofReal_measureReal (measure_ne_top _ _)]

/-! ### Exponential moments and polynomials -/

/-- **The finite exponential moments of the Jacobi measure.** For `-1 < α` and `-1 < β` and every
real `a`, the function `exp (a * |x|)` is integrable against `jacobiMeasure α β`, since the measure
is finite and concentrated on `(-1, 1)`. Any `0 < a` supplies the exponential-moment hypothesis of
`TauCeti.orthogonal_span_range_bareNormalizedLp_eq_bot`. -/
theorem integrable_exp_mul_abs_jacobiMeasure (hα : -1 < α) (hβ : -1 < β) (a : ℝ) :
    Integrable (fun x : ℝ => exp (a * |x|)) (jacobiMeasure α β) := by
  have := isFiniteMeasure_jacobiMeasure hα hβ
  simpa only [smul_eq_mul, mul_one, RCLike.ofReal_real_eq_id, id_eq] using
    (integrable_const (1 : ℝ)).exp_abs_smul_of_ae_abs_le (𝕜 := ℝ) a 1
      ((ae_mem_Ioo_jacobiMeasure α β).mono fun x hx => abs_le.2 ⟨hx.1.le, hx.2.le⟩)

/-- Every real polynomial is integrable against the Jacobi measure when `-1 < α` and `-1 < β`. -/
theorem integrable_eval_jacobiMeasure (hα : -1 < α) (hβ : -1 < β) (q : ℝ[X]) :
    Integrable (fun x : ℝ => q.eval x) (jacobiMeasure α β) := by
  have := isFiniteMeasure_jacobiMeasure hα hβ
  refine TauCeti.integrable_eval_of_forall_integrable_pow (fun k => ?_) q
  refine Integrable.of_bound (by fun_prop) 1 ((ae_mem_Ioo_jacobiMeasure α β).mono fun x hx => ?_)
  rw [norm_pow, Real.norm_eq_abs]
  exact pow_le_one₀ (abs_nonneg x) (abs_le.2 ⟨hx.1.le, hx.2.le⟩)

end Polynomial
