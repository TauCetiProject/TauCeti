/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.BetaPrime.Basic
public import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Distributions.FisherSnedecor.Moments
import TauCeti.Probability.Distributions.Affine

/-!
# Moments of the beta-prime distribution

The beta-prime law with positive shapes `a, b` has real-power moment
`beta (a + q) (b - q) / beta a b` exactly for `-a < q < b`. The two bounds describe
the singularity at zero and the polynomial tail, respectively. This file proves the sharp
criterion, its natural-power specializations, the mean and variance, and the exact
exponential-integrability domain `Iic 0`.

The beta-prime law is the odds-map image of `betaMeasure a b`, and equals the law of
`(a / b) * Y` for `Y` with law `fisherSnedecorMeasure (2 * a) (2 * b)`. These
integrability criteria identify which powers and exponentials have finite expectation.

## References

* N. L. Johnson, S. Kotz, and N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley (1995), chapter 25.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

variable {a b : ℝ}

private lemma rpow_odds_ae_betaMeasure (a b q : ℝ) :
    (fun u ↦ (fisherSnedecorMap 2 2 u) ^ q) =ᵐ[betaMeasure a b]
      fun u ↦ u ^ q * (1 - u) ^ (-q) := by
  filter_upwards [ae_mem_Ioo_betaMeasure a b] with u hu
  simp only [fisherSnedecorMap_def, div_self (by norm_num : (2 : ℝ) ≠ 0), one_mul]
  rw [Real.div_rpow hu.1.le (sub_pos.mpr hu.2).le,
    Real.rpow_neg (sub_pos.mpr hu.2).le, div_eq_mul_inv]

/-- A real power of a beta-prime variable is integrable exactly between the two shape
thresholds, with divergence at both endpoints. -/
@[simp]
theorem integrable_rpow_betaPrimeMeasure_iff (ha : 0 < a) (hb : 0 < b) (q : ℝ) :
    Integrable (fun x : ℝ ↦ x ^ q) (betaPrimeMeasure a b) ↔ -a < q ∧ q < b := by
  rw [betaPrimeMeasure_eq_map ha hb,
    integrable_map_measure (by fun_prop) (measurable_fisherSnedecorMap 2 2).aemeasurable]
  simp only [Function.comp_def]
  rw [integrable_congr (rpow_odds_ae_betaMeasure a b q),
    integrable_rpow_mul_one_sub_rpow_betaMeasure_iff ha hb]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- Every finite real-power moment of a beta-prime law is a quotient of beta functions. -/
@[simp]
theorem integral_rpow_betaPrimeMeasure (ha : 0 < a) (hb : 0 < b) {q : ℝ}
    (hqa : -a < q) (hqb : q < b) :
    ∫ x, x ^ q ∂betaPrimeMeasure a b = beta (a + q) (b - q) / beta a b := by
  rw [betaPrimeMeasure_eq_map ha hb,
    integral_map (measurable_fisherSnedecorMap 2 2).aemeasurable (by fun_prop),
    integral_congr_ae (rpow_odds_ae_betaMeasure a b q),
    integral_rpow_mul_one_sub_rpow_betaMeasure ha hb (by linarith) (by linarith),
    sub_eq_add_neg]

/-- A natural power is integrable under a valid beta-prime law exactly below its second
shape parameter. -/
@[simp]
theorem integrable_pow_betaPrimeMeasure_iff (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (betaPrimeMeasure a b) ↔ (n : ℝ) < b := by
  have hna : -a < (n : ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) n]
  simpa only [Real.rpow_natCast, and_iff_right hna] using
    integrable_rpow_betaPrimeMeasure_iff ha hb (n : ℝ)

/-- The natural moments of a beta-prime law, including order zero. -/
@[simp]
theorem integral_pow_betaPrimeMeasure (ha : 0 < a) (n : ℕ) (hn : (n : ℝ) < b) :
    ∫ x, x ^ n ∂betaPrimeMeasure a b = beta (a + n) (b - n) / beta a b := by
  simpa only [Real.rpow_natCast] using
    integral_rpow_betaPrimeMeasure ha (lt_of_le_of_lt (Nat.cast_nonneg (α := ℝ) n) hn)
      (by linarith [Nat.cast_nonneg (α := ℝ) n] : -a < (n : ℝ)) hn

/-- The beta-prime mean exists exactly when the second shape exceeds one. -/
@[simp]
theorem integrable_id_betaPrimeMeasure_iff (ha : 0 < a) (hb : 0 < b) :
    Integrable id (betaPrimeMeasure a b) ↔ 1 < b := by
  simpa only [pow_one, Nat.cast_one, Function.id_def] using
    integrable_pow_betaPrimeMeasure_iff ha hb 1

/-- The second beta-prime moment exists exactly when the second shape exceeds two. -/
theorem integrable_sq_betaPrimeMeasure_iff (ha : 0 < a) (hb : 0 < b) :
    Integrable (fun x : ℝ ↦ x ^ 2) (betaPrimeMeasure a b) ↔ 2 < b := by
  simpa only [Nat.cast_ofNat] using integrable_pow_betaPrimeMeasure_iff ha hb 2

/-- The mean of a beta-prime law is `a / (b - 1)` when it is integrable. -/
@[simp]
theorem integral_id_betaPrimeMeasure (ha : 0 < a) (hb : 1 < b) :
    ∫ x, x ∂betaPrimeMeasure a b = a / (b - 1) := by
  let _ := isProbabilityMeasure_fisherSnedecorMeasure
    (m := 2 * a) (n := 2 * b) (by positivity) (by linarith)
  have h := integral_id_map_affine
    (μ := fisherSnedecorMeasure (2 * a) (2 * b)) (a := 0) (b := a / b)
    ((integrable_id_fisherSnedecorMeasure_iff (by positivity) (by linarith)).2 (by linarith))
  simp only [zero_add] at h
  rw [betaPrimeMeasure_eq_map_fisherSnedecorMeasure ha (by linarith),
    h, integral_id_fisherSnedecorMeasure (by positivity) (by linarith)]
  field_simp

/-- The second raw moment of a beta-prime law. -/
@[simp high]
theorem integral_sq_betaPrimeMeasure (ha : 0 < a) (hb : 2 < b) :
    ∫ x, x ^ 2 ∂betaPrimeMeasure a b = a * (a + 1) / ((b - 1) * (b - 2)) := by
  rw [betaPrimeMeasure_eq_map_fisherSnedecorMeasure ha (by linarith),
    integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul, integral_sq_fisherSnedecorMeasure (by positivity) (by linarith)]
  have hb₁ : 2 * b - 2 = 2 * (b - 1) := by ring
  have hb₂ : 2 * b - 4 = 2 * (b - 2) := by ring
  rw [hb₁, hb₂]
  field_simp

/-- The variance of a beta-prime law with finite second moment. -/
@[simp]
theorem variance_id_betaPrimeMeasure (ha : 0 < a) (hb : 2 < b) :
    variance id (betaPrimeMeasure a b) =
      a * (a + b - 1) / ((b - 2) * (b - 1) ^ 2) := by
  let _ := isProbabilityMeasure_fisherSnedecorMeasure
    (m := 2 * a) (n := 2 * b) (by positivity) (by linarith)
  have h := variance_id_map_affine
    (μ := fisherSnedecorMeasure (2 * a) (2 * b)) (a := 0) (b := a / b)
  simp only [zero_add] at h
  rw [betaPrimeMeasure_eq_map_fisherSnedecorMeasure ha (by linarith),
    h, variance_id_fisherSnedecorMeasure (by positivity) (by linarith)]
  have hb₁ : 2 * b - 2 = 2 * (b - 1) := by ring
  have hb₂ : 2 * b - 4 = 2 * (b - 2) := by ring
  rw [hb₁, hb₂]
  field_simp

/-- Beta-prime laws have finite exponential moments exactly at nonpositive rates. -/
@[simp]
theorem integrable_exp_mul_id_betaPrimeMeasure_iff (ha : 0 < a) (hb : 0 < b) (t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x)) (betaPrimeMeasure a b) ↔ t ≤ 0 := by
  rw [betaPrimeMeasure_eq_map_fisherSnedecorMeasure ha hb,
    integrable_map_measure (by fun_prop) (by fun_prop)]
  simp only [Function.comp_def, ← mul_assoc]
  rw [integrable_exp_mul_id_fisherSnedecorMeasure_iff (by positivity) (by positivity),
    mul_nonpos_iff]
  simp [not_le_of_gt (div_pos ha hb), (div_pos ha hb).le]

/-- The exact exponential-integrability domain of a valid beta-prime law is the
nonpositive half-line. -/
@[simp]
theorem integrableExpSet_id_betaPrimeMeasure (ha : 0 < a) (hb : 0 < b) :
    integrableExpSet id (betaPrimeMeasure a b) = Iic 0 := by
  ext t
  simpa [integrableExpSet, id_eq] using integrable_exp_mul_id_betaPrimeMeasure_iff ha hb t

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- A beta-prime random variable has the same sharp real-power integrability thresholds. -/
theorem integrable_rpow_iff_of_hasLaw_betaPrimeMeasure
    (hX : HasLaw X (betaPrimeMeasure a b) P) (ha : 0 < a) (hb : 0 < b) (q : ℝ) :
    Integrable (fun ω ↦ X ω ^ q) P ↔ -a < q ∧ q < b := by
  rw [← integrable_rpow_betaPrimeMeasure_iff ha hb, ← hX.map_eq,
    integrable_map_measure (by fun_prop) hX.aemeasurable]
  simp only [Function.comp_def]

/-- Real-power moments of a random variable with a beta-prime law. -/
theorem integral_rpow_of_hasLaw_betaPrimeMeasure
    (hX : HasLaw X (betaPrimeMeasure a b) P) (ha : 0 < a) (hb : 0 < b) {q : ℝ}
    (hqa : -a < q) (hqb : q < b) :
    ∫ ω, X ω ^ q ∂P = beta (a + q) (b - q) / beta a b := by
  calc
    _ = ∫ x, x ^ q ∂betaPrimeMeasure a b :=
      hX.integral_comp (f := fun x : ℝ ↦ x ^ q) (by fun_prop)
    _ = _ := integral_rpow_betaPrimeMeasure ha hb hqa hqb

/-- The expectation of a beta-prime random variable with finite first moment. -/
theorem integral_of_hasLaw_betaPrimeMeasure (hX : HasLaw X (betaPrimeMeasure a b) P)
    (ha : 0 < a) (hb : 1 < b) :
    ∫ ω, X ω ∂P = a / (b - 1) := by
  rw [hX.integral_eq, integral_id_betaPrimeMeasure ha hb]

/-- The variance of a beta-prime random variable with finite second moment. -/
theorem variance_of_hasLaw_betaPrimeMeasure (hX : HasLaw X (betaPrimeMeasure a b) P)
    (ha : 0 < a) (hb : 2 < b) :
    variance X P = a * (a + b - 1) / ((b - 2) * (b - 1) ^ 2) := by
  rw [hX.variance_eq, variance_id_betaPrimeMeasure ha hb]

end RandomVariables

end TauCeti.Probability
