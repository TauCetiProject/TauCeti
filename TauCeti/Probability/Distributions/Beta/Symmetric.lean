/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Beta.Square
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Probability.Distributions.Beta.Reflection
import TauCeti.Probability.Distributions.Affine
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

private theorem half_mul_betaPDFReal_symmetric (ha : 0 < a) {z : ℝ}
    (hz : z ∈ Set.Ioo (-1 : ℝ) 1) :
    (1 / 2 : ℝ) * betaPDFReal a a ((z + 1) / 2) =
      (1 - z ^ 2) ^ (a - 1) / beta (1 / 2) a := by
  have hu : 0 < (z + 1) / 2 := by linarith [hz.1]
  have hv : 0 < (1 - z) / 2 := by linarith [hz.2]
  have hw : 0 < 1 - z ^ 2 := by
    nlinarith [mul_pos (show 0 < z + 1 by linarith) (show 0 < 1 - z by linarith)]
  rw [betaPDFReal, ite_eq_left ⟨hu, by linarith [hz.2]⟩,
    show 1 - (z + 1) / 2 = (1 - z) / 2 by ring,
    mul_assoc, ← Real.mul_rpow hu.le hv.le]
  have huv : (z + 1) / 2 * ((1 - z) / 2) = (1 - z ^ 2) / 4 := by ring
  rw [huv, Real.div_rpow hw.le (by norm_num : (0 : ℝ) ≤ 4),
    ProbabilityTheory.beta_one_half_left_eq_two_rpow_mul_beta_self ha]
  have hfour : (4 : ℝ) ^ (a - 1) = 2 ^ (2 * (a - 1)) := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  rw [hfour]
  have hbeta : beta a a ≠ 0 := (beta_pos ha ha).ne'
  have htwo : (2 : ℝ) ^ (2 * a - 1) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
  field_simp
  calc
    (2 : ℝ) ^ (2 * a - 1) = 2 ^ (1 + 2 * (a - 1)) := by congr 1; ring
    _ = 2 ^ (1 : ℝ) * 2 ^ (2 * (a - 1)) :=
      Real.rpow_add (by norm_num : (0 : ℝ) < 2) 1 (2 * (a - 1))
    _ = 2 * 2 ^ (2 * (a - 1)) := by rw [Real.rpow_one]

/-- The density of a centered symmetric Beta law on `(-1, 1)`.

For positive shape `a`, the affine image of `Beta(a, a)` under `x ↦ -1 + 2x` has density
`(1 - z²) ^ (a - 1) / B(1/2, a)` with respect to Lebesgue measure on the open interval. -/
theorem map_centered_betaMeasure_eq_withDensity (ha : 0 < a) :
    (betaMeasure a a).map (fun x ↦ -1 + 2 * x) =
      (volume.restrict (Set.Ioo (-1 : ℝ) 1)).withDensity
        (fun z ↦ ENNReal.ofReal ((1 - z ^ 2) ^ (a - 1) / beta (1 / 2) a)) := by
  rw [betaMeasure, map_affine_withDensity_volume (a := -1) (b := 2) _ (by norm_num),
    ← withDensity_indicator measurableSet_Ioo]
  apply withDensity_congr_ae
  filter_upwards with z
  by_cases hz : z ∈ Set.Ioo (-1 : ℝ) 1
  · rw [Set.indicator_of_mem hz, affineDensity_apply]
    norm_num [abs_of_nonneg]
    rw [betaPDF, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2),
      half_mul_betaPDFReal_symmetric ha hz]
  · rw [Set.indicator_of_notMem hz, affineDensity_apply]
    norm_num [abs_of_nonneg]
    by_cases hzlo : z ≤ -1
    · rw [betaPDF_eq_zero_of_nonpos (by linarith)]
    · have hzhi : 1 ≤ z := by
        apply le_of_not_gt
        intro h
        exact hz ⟨lt_of_not_ge hzlo, h⟩
      rw [betaPDF_eq_zero_of_one_le (by linarith)]

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
  · exact integral_eq_zero_of_odd fun z ↦ by
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

/-- Centered symmetric Beta variables lie in the closed unit cube almost surely. -/
theorem ae_abs_le_one_pi_centered_betaMeasure {ι : Type*} [Fintype ι]
    {a : ι → ℝ} (ha : ∀ ij, 0 < a ij) :
    ∀ᵐ z ∂(Measure.pi fun ij ↦
      (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)), ∀ ij, |z ij| ≤ 1 := by
  have (ij : ι) : IsProbabilityMeasure (betaMeasure (a ij) (a ij)) :=
    isProbabilityMeasureBeta (ha ij) (ha ij)
  apply ae_all_iff.2
  intro ij
  apply (Measure.tendsto_eval_ae_ae (α := fun _ ↦ ℝ) (μ := fun ij ↦
    (betaMeasure (a ij) (a ij)).map (fun x ↦ -1 + 2 * x)) (i := ij)).eventually
      (p := fun x : ℝ ↦ |x| ≤ 1)
  apply (ae_map_iff (by fun_prop) (by measurability)).2
  filter_upwards [ae_mem_Ioo_betaMeasure (a ij) (a ij)] with x hx
  rw [abs_le]
  constructor <;> linarith [hx.1, hx.2]

end TauCeti.Probability
