/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Beta.Square
import TauCeti.Probability.Distributions.Beta.Reflection
import TauCeti.Probability.Distributions.Affine
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.MeasureTheory.Integral.OddSymmetric
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Weighted moments of centered symmetric Beta laws

For positive shape `a`, centering a `Beta(a, a)` variable by `x ↦ -1 + 2 * x` gives a symmetric
variable `Z` in `(-1, 1)`. Its square has law `Beta(1 / 2, a)`, so the mixed absolute-power moment
`E[|Z| ^ q * (1 - Z ^ 2) ^ r]` is a beta quotient, finite exactly when `-1 < q` and
`0 < a + r`. Signed natural powers have the same value at even orders and vanish at odd
orders. The endpoint thresholds include divergence at equality.

The finite-product results evaluate the factors arising when polynomials in correlation
matrix entries are expanded in independent partial correlations. They allow arbitrary real
weights on the residual factors `1 - Z ^ 2`, including the half-integer powers in Cholesky
coordinates and the negative powers needed for determinant moments. Empty products are
included.

The proofs reuse `betaMeasure_map_centered_sq` and the mixed real-power moments of the
ordinary Beta law.

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989–2001.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti.Probability

variable {a q r : ℝ}

/-- A centered symmetric Beta variable of positive shape `a` has density
`(1 - z ^ 2) ^ (a - 1) / B(1 / 2, a)` on `(-1, 1)`. -/
theorem betaMeasure_map_centered_eq_withDensity (ha : 0 < a) :
    (betaMeasure a a).map (fun x ↦ -1 + 2 * x) =
      volume.withDensity ((Set.Ioo (-1) 1).indicator fun z ↦
        ENNReal.ofReal ((1 - z ^ 2) ^ (a - 1) / beta (1 / 2) a)) := by
  rw [betaMeasure, map_affine_withDensity_volume _ (by norm_num : (2 : ℝ) ≠ 0)]
  congr 1
  funext z
  rw [affineDensity_apply, betaPDF, sub_neg_eq_add]
  by_cases hz : z ∈ Set.Ioo (-1) 1
  · have hx : 0 < (z + 1) / 2 ∧ (z + 1) / 2 < 1 := by
      constructor <;> linarith [hz.1, hz.2]
    have hprod : ((z + 1) / 2) ^ (a - 1) * (1 - (z + 1) / 2) ^ (a - 1) =
        (1 - z ^ 2) ^ (a - 1) / (2 : ℝ) ^ (2 * a - 2) := by
      rw [← mul_rpow hx.1.le (by linarith)]
      have hid : (z + 1) / 2 * (1 - (z + 1) / 2) = (1 - z ^ 2) / 2 ^ 2 := by ring
      rw [hid, div_rpow (by nlinarith [hz.1, hz.2]) (by norm_num),
        ← rpow_natCast 2 2, ← rpow_mul (by norm_num)]
      congr 2
      ring
    have hpow : (2 : ℝ) ^ (2 * a - 1) = 2 * (2 : ℝ) ^ (2 * a - 2) := by
      rw [show 2 * a - 1 = (2 * a - 2) + 1 by ring, rpow_add (by norm_num)]
      simp [mul_comm]
    rw [Set.indicator_of_mem hz, ← ENNReal.ofReal_mul (by norm_num), betaPDFReal,
      ite_eq_left hx, mul_assoc (1 / beta a a), hprod,
      beta_one_half_left_eq_two_rpow_mul_beta_self ha, hpow]
    congr 1
    have := (beta_pos ha ha).ne'
    field_simp
    ring
  · have hx : ¬ (0 < (z + 1) / 2 ∧ (z + 1) / 2 < 1) := fun h ↦
      hz ⟨by linarith [h.1], by linarith [h.2]⟩
    rw [Set.indicator_of_notMem hz, betaPDFReal, ite_eq_right hx, ENNReal.ofReal_zero, mul_zero]

/-- The sharp integrability criterion for mixed absolute and residual powers of a centered
symmetric Beta variable. Both endpoint equalities belong to the divergent side. -/
@[simp]
theorem integrable_abs_rpow_mul_one_sub_sq_rpow_map_centered_betaMeasure_iff (ha : 0 < a) :
    Integrable (fun z : ℝ ↦ |z| ^ q * (1 - z ^ 2) ^ r)
      ((betaMeasure a a).map (fun x ↦ -1 + 2 * x)) ↔ -1 < q ∧ 0 < a + r := by
  have h := integrable_rpow_mul_one_sub_rpow_betaMeasure_iff
    (q := q / 2) (s := r) (by norm_num : (0 : ℝ) < 1 / 2) ha
  have hmap : ((betaMeasure a a).map (fun x ↦ -1 + 2 * x)).map (fun z ↦ z ^ 2) =
      betaMeasure (1 / 2) a := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    exact betaMeasure_map_centered_sq ha
  rw [← hmap,
    integrable_map_measure (by fun_prop) (by fun_prop)] at h
  simp only [Function.comp_def, rpow_div_two_eq_sqrt q (sq_nonneg _), sqrt_sq_eq_abs] at h
  exact h.trans (and_congr_left fun _ ↦ by constructor <;> intro hq <;> linarith)

/-- A mixed absolute-power moment of a centered symmetric Beta variable is a quotient of
beta values. The strict inequalities guarantee absolute integrability. -/
theorem integral_abs_rpow_mul_one_sub_sq_rpow_map_centered_betaMeasure (ha : 0 < a)
    (hq : -1 < q) (hr : 0 < a + r) :
    ∫ z, |z| ^ q * (1 - z ^ 2) ^ r
      ∂((betaMeasure a a).map (fun x ↦ -1 + 2 * x)) =
      beta ((q + 1) / 2) (a + r) / beta (1 / 2) a := by
  have h := integral_rpow_mul_one_sub_rpow_betaMeasure
    (q := q / 2) (s := r) (by norm_num : (0 : ℝ) < 1 / 2) ha (by linarith) hr
  have hmap : ((betaMeasure a a).map (fun x ↦ -1 + 2 * x)).map (fun z ↦ z ^ 2) =
      betaMeasure (1 / 2) a := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    exact betaMeasure_map_centered_sq ha
  rw [← hmap,
    integral_map (by fun_prop) (by fun_prop)] at h
  simp only [rpow_div_two_eq_sqrt q (sq_nonneg _), sqrt_sq_eq_abs] at h
  have he : (1 / 2 : ℝ) + q / 2 = (q + 1) / 2 := by ring
  simpa only [he] using h

/-- Multiplication by a natural power does not change the residual-power threshold for a
centered symmetric Beta law. In particular, an odd integrand still requires this condition
for its expectation to be an absolutely convergent integral. -/
@[simp]
theorem integrable_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure_iff (ha : 0 < a) (n : ℕ) :
    Integrable (fun z : ℝ ↦ z ^ n * (1 - z ^ 2) ^ r)
      ((betaMeasure a a).map (fun x ↦ -1 + 2 * x)) ↔ 0 < a + r := by
  rw [← integrable_norm_iff (by fun_prop)]
  have hnorm : (fun z : ℝ ↦ ‖z ^ n * (1 - z ^ 2) ^ r‖) =ᵐ[
      (betaMeasure a a).map (fun x ↦ -1 + 2 * x)]
      (fun z : ℝ ↦ |z| ^ (n : ℝ) * (1 - z ^ 2) ^ r) := by
    apply (ae_map_iff (by fun_prop) (by measurability)).2
    filter_upwards [ae_mem_Ioo_betaMeasure a a] with x hx
    have hx' : 0 ≤ 1 - (-1 + 2 * x) ^ 2 := by nlinarith [hx.1, hx.2]
    rw [norm_mul, Real.norm_eq_abs, abs_pow, Real.norm_eq_abs,
      abs_of_nonneg (rpow_nonneg hx' r), rpow_natCast]
  rw [integrable_congr hnorm]
  rw [integrable_abs_rpow_mul_one_sub_sq_rpow_map_centered_betaMeasure_iff ha,
    and_iff_right (by have := Nat.cast_nonneg (α := ℝ) n; linarith : (-1 : ℝ) < (n : ℝ))]

/-- Weighted natural moments of a centered symmetric Beta variable. Even orders are beta
quotients; odd orders vanish by symmetry. The hypothesis excludes totalized divergent
integrals, including at odd orders. -/
theorem integral_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure (ha : 0 < a) (hr : 0 < a + r)
    (n : ℕ) :
    ∫ z, z ^ n * (1 - z ^ 2) ^ r
      ∂((betaMeasure a a).map (fun x ↦ -1 + 2 * x)) =
      if Even n then beta (((n : ℝ) + 1) / 2) (a + r) / beta (1 / 2) a else 0 := by
  split_ifs with hn
  · simpa only [rpow_natCast, hn.pow_abs] using
      integral_abs_rpow_mul_one_sub_sq_rpow_map_centered_betaMeasure ha
        (by have := Nat.cast_nonneg (α := ℝ) n; linarith : (-1 : ℝ) < (n : ℝ)) hr
  · let ν := (betaMeasure a a).map (fun x ↦ -1 + 2 * x)
    have hneg : ν.map (fun z ↦ -z) = ν := by
      calc
        _ = ((betaMeasure a a).map (fun x ↦ 1 - x)).map (fun x ↦ -1 + 2 * x) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          congr 1
          funext x
          dsimp
          ring
        _ = _ := by rw [betaMeasure_map_one_sub]
    let _ : ν.IsNegInvariant := ⟨hneg⟩
    exact integral_eq_zero_of_odd fun z ↦ by
      simp [(Nat.not_even_iff_odd.1 hn).neg_pow, neg_mul]

/-- Products of weighted natural powers of independent centered symmetric Beta variables
are integrable when every residual exponent is above its endpoint threshold. -/
theorem integrable_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure {ι : Type*} [Fintype ι]
    (a r : ι → ℝ) (n : ι → ℕ) (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < a i + r i) :
    Integrable (fun z : ι → ℝ ↦ ∏ i, z i ^ n i * (1 - z i ^ 2) ^ r i)
      (Measure.pi fun i ↦ (betaMeasure (a i) (a i)).map (fun x ↦ -1 + 2 * x)) := by
  let (i : ι) : IsProbabilityMeasure (betaMeasure (a i) (a i)) :=
    isProbabilityMeasureBeta (ha i) (ha i)
  exact Integrable.fintype_prod (μ := fun i ↦
    (betaMeasure (a i) (a i)).map (fun x ↦ -1 + 2 * x)) fun i ↦
    (integrable_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure_iff (ha i) (n i)).2 (hr i)

/-- Finite mixed moments of independent centered symmetric Beta variables factor into beta
quotients. Any odd coordinate power makes the moment zero. The formula includes empty
index types and arbitrary real residual exponents in the exact integrability range. -/
theorem integral_prod_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure {ι : Type*} [Fintype ι]
    (a r : ι → ℝ) (n : ι → ℕ) (ha : ∀ i, 0 < a i) (hr : ∀ i, 0 < a i + r i) :
    ∫ z : ι → ℝ, (∏ i, z i ^ n i * (1 - z i ^ 2) ^ r i)
      ∂(Measure.pi fun i ↦ (betaMeasure (a i) (a i)).map (fun x ↦ -1 + 2 * x)) =
      ∏ i, if Even (n i) then
        beta (((n i : ℝ) + 1) / 2) (a i + r i) / beta (1 / 2) (a i) else 0 := by
  let (i : ι) : IsProbabilityMeasure (betaMeasure (a i) (a i)) :=
    isProbabilityMeasureBeta (ha i) (ha i)
  rw [integral_fintype_prod_eq_prod (fun i (z : ℝ) ↦ z ^ n i * (1 - z ^ 2) ^ r i)]
  exact Finset.prod_congr rfl fun i _ ↦
    integral_pow_mul_one_sub_sq_rpow_map_centered_betaMeasure (ha i) (hr i) (n i)

end TauCeti.Probability
