/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.BetaNegativeBinomial.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Analysis.SpecialFunctions.Gamma
import TauCeti.Data.Nat.Factorial.Basic
import TauCeti.Probability.Distributions.Dirac
import TauCeti.Probability.Moments.IntegrableExpMul

/-!
# Moments of beta-negative-binomial laws

For positive negative-binomial shape `r` and Beta shapes `a, b`, the masses decay as
`k ^ (-(a + 1))`. Consequently, a natural moment of order `n` exists exactly when `n < a`.
The factorial moments are
`E[(X)ₙ] = (r (r + 1) ⋯ (r + n - 1)) * beta (a - n) (b + n) / beta a b`.
They give the mean and variance, and the sharp moment threshold excludes every positive
exponential moment. At shape zero the law is Dirac at zero and all moments are finite.

The factorial-moment calculation shifts the weighted masses to another normalized
beta-negative-binomial law. The tail comparison uses the Gamma-ratio asymptotics in
`Real.isEquivalent_Gamma_natCast_add_one_add`, as in the Yule–Simon moment development.

## Reference

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
  2005, Chapter 6.
-/

public section

noncomputable section

open Asymptotics Filter MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Nat Topology

namespace TauCeti.Probability

variable {r a b : ℝ}

private theorem isEquivalent_betaNegativeBinomialWeightReal (hr : 0 < r) :
    (fun k : ℕ => betaNegativeBinomialWeightReal r a b k) ~[atTop]
      fun k => Gamma (a + r) / (Gamma r * beta a b) * (k : ℝ) ^ (-(a + 1)) := by
  have hΓ := ((isEquivalent_Gamma_natCast_add_one_add (r - 1)).mul
    (isEquivalent_Gamma_natCast_add_one_add (b - 1))).div
      ((isEquivalent_Gamma_natCast_add_one_add 0).mul
        (isEquivalent_Gamma_natCast_add_one_add (a + r + b - 1)))
  have h := (IsEquivalent.refl (u := fun _ : ℕ =>
    Gamma (a + r) / (Gamma r * beta a b))).mul hΓ
  refine (h.congr_left ?_).congr_right ?_
  · filter_upwards [] with k
    simp only [Pi.mul_apply, Pi.div_apply]
    rw [betaNegativeBinomialWeightReal_of_ne_zero hr.ne']
    simp only [beta]
    rw [show (k : ℝ) + 1 + (r - 1) = r + k by ring,
      show (k : ℝ) + 1 + (b - 1) = b + k by ring,
      show (k : ℝ) + 1 + (a + r + b - 1) = a + r + (b + k) by ring]
    simp only [add_zero, Gamma_nat_eq_factorial, add_assoc]
    ring
  · filter_upwards [eventually_ne_atTop 0] with k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    have hfac : (k ! : ℝ) ≠ 0 := by positivity
    simp only [Pi.mul_apply, Pi.div_apply, rpow_zero]
    congr 1
    conv_rhs =>
      rw [show -(a + 1) = ((r - 1) + (b - 1)) - (a + r + b - 1) by ring,
        rpow_sub hk', rpow_add hk']
    field_simp

/-- The natural moments of the real cast law exist exactly below the first Beta shape,
except that shape zero is Dirac and has every moment. This includes moment order zero. -/
@[simp]
theorem integrable_pow_map_cast_betaNegativeBinomialMeasure_iff
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n)
        ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) ↔
      r = 0 ∨ (n : ℝ) < a := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [betaNegativeBinomialMeasure_zero ha hb,
      Measure.map_dirac' (by fun_prop : Measurable (Nat.cast : ℕ → ℝ))]
    simp only [Nat.cast_zero, true_or, iff_true]
    exact integrable_dirac (by simp)
  rw [MeasurableEmbedding.natCast.integrable_map_iff,
    betaNegativeBinomialMeasure_eq_sum_dirac hr.le ha hb,
    integrable_sum_dirac_iff (betaNegativeBinomialWeight_ne_top r a b)]
  simp only [betaNegativeBinomialWeight_toReal hr.le ha hb, Function.comp_apply, norm_pow,
    Real.norm_natCast, ne_of_gt hr, false_or]
  have hC : Gamma (a + r) / (Gamma r * beta a b) ≠ 0 :=
    (div_pos (Gamma_pos_of_pos (by positivity))
      (mul_pos (Gamma_pos_of_pos hr) (beta_pos ha hb))).ne'
  have h := (isEquivalent_betaNegativeBinomialWeightReal (a := a) (b := b) hr).mul
    (IsEquivalent.refl (u := fun k : ℕ => (k : ℝ) ^ n))
  have heq : (fun k : ℕ =>
      (Gamma (a + r) / (Gamma r * beta a b) * (k : ℝ) ^ (-(a + 1))) * (k : ℝ) ^ n) =ᶠ[atTop]
        fun k => Gamma (a + r) / (Gamma r * beta a b) * (k : ℝ) ^ ((n : ℝ) - (a + 1)) := by
    filter_upwards [eventually_ne_atTop 0] with k hk
    have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
    rw [mul_assoc, ← rpow_natCast, ← rpow_add hk']
    congr 2
    ring
  have hs := (h.congr_right heq).summable_iff_nat
  rw [Pi.mul_def] at hs
  rw [hs, summable_mul_left_iff hC, summable_nat_rpow]
  constructor <;> intro h <;> linarith

/-- Falling factorials have the same sharp integrability threshold as ordinary natural moments. -/
@[simp]
theorem integrable_descFactorial_betaNegativeBinomialMeasure_iff
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) (n : ℕ) :
    Integrable (fun k : ℕ => (k.descFactorial n : ℝ)) (betaNegativeBinomialMeasure r a b) ↔
      r = 0 ∨ (n : ℝ) < a := by
  rw [← integrable_pow_map_cast_betaNegativeBinomialMeasure_iff hr ha hb n,
    MeasurableEmbedding.natCast.integrable_map_iff,
    betaNegativeBinomialMeasure_eq_sum_dirac hr ha hb,
    integrable_sum_dirac_iff (betaNegativeBinomialWeight_ne_top r a b),
    integrable_sum_dirac_iff (betaNegativeBinomialWeight_ne_top r a b)]
  simp only [Function.comp_apply, norm_pow, Real.norm_natCast]
  exact ((IsEquivalent.refl (u := fun k => (betaNegativeBinomialWeight r a b k).toReal)).mul
    (isEquivalent_descFactorial n)).summable_iff_nat

private theorem betaNegativeBinomialWeightReal_mul_descFactorial
    (hr : 0 < r) (hb : 0 < b) {n : ℕ} (hn : (n : ℝ) < a) (k : ℕ) :
    betaNegativeBinomialWeightReal r a b (k + n) * ((k + n).descFactorial n : ℝ) =
      (Gamma (r + n) / Gamma r * beta (a - n) (b + n) / beta a b) *
        betaNegativeBinomialWeightReal (r + n) (a - n) (b + n) k := by
  have hrn : 0 < r + n := by positivity
  have hfac : ((k + n) ! : ℝ) = k ! * ((k + n).descFactorial n : ℝ) := by
    rw [← Nat.factorial_mul_descFactorial (Nat.le_add_left n k), Nat.add_sub_cancel]
    push_cast
    ring
  have hd : ((k + n).descFactorial n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.descFactorial_eq_zero_iff_lt.not.mpr (by omega))
  have hbeta : beta (a - n) (b + n) ≠ 0 := by
    exact (beta_pos (sub_pos.mpr hn) (by positivity)).ne'
  rw [betaNegativeBinomialWeightReal_of_ne_zero hr.ne',
    betaNegativeBinomialWeightReal_of_ne_zero hrn.ne', hfac]
  simp only [Nat.cast_add]
  rw [show a - (n : ℝ) + (r + n) = a + r by ring,
    show b + (k + n : ℝ) = b + n + k by ring,
    show r + (k + n : ℝ) = r + n + k by ring]
  field_simp

/-- The falling-factorial moments of a beta-negative-binomial law on their exact finiteness
domain, including moment order zero and negative-binomial shape zero. -/
theorem integral_descFactorial_betaNegativeBinomialMeasure
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) {n : ℕ} (hn : r = 0 ∨ (n : ℝ) < a) :
    ∫ k : ℕ, (k.descFactorial n : ℝ) ∂betaNegativeBinomialMeasure r a b =
      (∏ j ∈ Finset.range n, (r + j)) * beta (a - n) (b + n) / beta a b := by
  rcases hr.eq_or_lt with rfl | hr
  · cases n <;>
      simp [betaNegativeBinomialMeasure_zero ha hb, Finset.prod_range_succ',
        (beta_pos ha hb).ne']
  have hn := hn.resolve_left hr.ne'
  have hrn : 0 < r + n := by positivity
  have hbn : 0 < b + n := by positivity
  have hsum := hasSum_betaNegativeBinomialWeightReal hrn.le (sub_pos.mpr hn) hbn
  have hmoment : HasSum (fun k => betaNegativeBinomialWeightReal r a b k *
      (k.descFactorial n : ℝ))
        (Gamma (r + n) / Gamma r * beta (a - n) (b + n) / beta a b) := by
    rw [← hasSum_nat_add_iff' n]
    have hlow : ∑ k ∈ Finset.range n, betaNegativeBinomialWeightReal r a b k *
        (k.descFactorial n : ℝ) = 0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [Nat.descFactorial_eq_zero_iff_lt.mpr (Finset.mem_range.mp hk)]
      simp
    rw [hlow, sub_zero]
    simpa only [betaNegativeBinomialWeightReal_mul_descFactorial hr hb hn, mul_one] using
      hsum.mul_left (Gamma (r + n) / Gamma r * beta (a - n) (b + n) / beta a b)
  rw [betaNegativeBinomialMeasure_eq_sum_dirac hr.le ha hb,
    integral_sum_dirac (betaNegativeBinomialWeight_ne_top r a b)]
  simp only [smul_eq_mul, betaNegativeBinomialWeight_toReal hr.le ha hb]
  rw [hmoment.tsum_eq,
    (div_eq_iff (Gamma_pos_of_pos hr).ne').mpr (prod_range_add_mul_Gamma hr n).symm]

/-- The mean of the real cast beta-negative-binomial law, including shape zero. -/
@[simp]
theorem integral_id_map_cast_betaNegativeBinomialMeasure
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) (hfinite : r = 0 ∨ 1 < a) :
    ∫ x, x ∂((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) =
      r * b / (a - 1) := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [betaNegativeBinomialMeasure_zero ha hb,
      Measure.map_dirac' (by fun_prop : Measurable (Nat.cast : ℕ → ℝ))]
    simp
  have ha1 := hfinite.resolve_left hr.ne'
  have h := integral_descFactorial_betaNegativeBinomialMeasure hr.le ha hb
    (n := 1) (Or.inr (by simpa using ha1))
  simp only [Nat.descFactorial_one, Finset.prod_range_one, Nat.cast_zero, add_zero,
    Nat.cast_one] at h
  rw [MeasurableEmbedding.natCast.integral_map, h]
  rw [mul_div_assoc, beta_comm (a - 1) (b + 1), beta_comm a b,
    beta_add_one_sub_one_div hb ha1]
  ring

/-- A beta-negative-binomial law has a finite first moment exactly when `a > 1`,
or when its negative-binomial shape is zero. -/
@[simp]
theorem integrable_id_map_cast_betaNegativeBinomialMeasure_iff
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    Integrable id ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) ↔
      r = 0 ∨ 1 < a := by
  simpa only [pow_one, Nat.cast_one, Function.id_def] using
    integrable_pow_map_cast_betaNegativeBinomialMeasure_iff hr ha hb 1

/-- A beta-negative-binomial law has a finite second moment exactly when `a > 2`,
or when its negative-binomial shape is zero. -/
@[simp]
theorem memLp_two_id_map_cast_betaNegativeBinomialMeasure_iff
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    MemLp id 2 ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) ↔
      r = 0 ∨ 2 < a := by
  rw [memLp_two_iff_integrable_sq (by fun_prop)]
  simp only [id_eq]
  exact integrable_pow_map_cast_betaNegativeBinomialMeasure_iff hr ha hb 2

/-- The second raw moment of the real cast beta-negative-binomial law, including shape zero. -/
theorem integral_sq_id_map_cast_betaNegativeBinomialMeasure
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) (hfinite : r = 0 ∨ 2 < a) :
    ∫ x : ℝ, x ^ 2 ∂((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) =
      r * (r + 1) * (b * (b + 1) / ((a - 1) * (a - 2))) + r * b / (a - 1) := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [betaNegativeBinomialMeasure_zero ha hb,
      Measure.map_dirac' (by fun_prop : Measurable (Nat.cast : ℕ → ℝ))]
    simp
  have ha2 := hfinite.resolve_left hr.ne'
  have ha1 : 1 < a := by linarith
  have hfirst := (integrable_id_map_cast_betaNegativeBinomialMeasure_iff hr.le ha hb).mpr
    (Or.inr ha1)
  rw [MeasurableEmbedding.natCast.integrable_map_iff] at hfirst
  simp only [Function.comp_def, id_eq] at hfirst
  have hdesc := (integrable_descFactorial_betaNegativeBinomialMeasure_iff hr.le ha hb 2).mpr
    (Or.inr ha2)
  have h := integral_descFactorial_betaNegativeBinomialMeasure hr.le ha hb
    (n := 2) (Or.inr (by simpa using ha2))
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, Nat.cast_zero, Nat.cast_one,
    Nat.cast_ofNat, add_zero, one_mul] at h
  have hbeta : beta (a - 2) (b + 2) / beta a b =
      b * (b + 1) / ((a - 1) * (a - 2)) := by
    rw [beta_comm (a - 2) (b + 2), beta_comm a b, beta_add_two_sub_two_div hb ha2]
  have hmean := integral_id_map_cast_betaNegativeBinomialMeasure hr.le ha hb (Or.inr ha1)
  rw [MeasurableEmbedding.natCast.integral_map] at hmean
  rw [MeasurableEmbedding.natCast.integral_map]
  simp_rw [← Nat.cast_pow, Nat.sq_eq_descFactorial_two_add, Nat.cast_add]
  rw [integral_add hdesc hfirst, hmean, h]
  rw [mul_div_assoc, mul_div_assoc, hbeta]

/-- The variance of the real cast beta-negative-binomial law, including shape zero. -/
@[simp]
theorem variance_id_map_cast_betaNegativeBinomialMeasure
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) (hfinite : r = 0 ∨ 2 < a) :
    variance id ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) =
      r * b * (a + b - 1) * (a + r - 1) / ((a - 1) ^ 2 * (a - 2)) := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [betaNegativeBinomialMeasure_zero ha hb,
      Measure.map_dirac' (by fun_prop : Measurable (Nat.cast : ℕ → ℝ))]
    simp
  have ha2 := hfinite.resolve_left hr.ne'
  have ha1 : 1 < a := by linarith
  have := isProbabilityMeasure_betaNegativeBinomialMeasure hr.le ha hb
  have hmem := (memLp_two_id_map_cast_betaNegativeBinomialMeasure_iff hr.le ha hb).mpr
    (Or.inr ha2)
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_sq_id_map_cast_betaNegativeBinomialMeasure hr.le ha hb (Or.inr ha2),
    integral_id_map_cast_betaNegativeBinomialMeasure hr.le ha hb (Or.inr ha1)]
  have h1 : a - 1 ≠ 0 := by linarith
  have h2 : a - 2 ≠ 0 := by linarith
  field_simp
  ring

/-- Positive-shape beta-negative-binomial laws have exponential moments exactly at
nonpositive arguments; shape zero has every exponential moment. -/
@[simp]
theorem integrableExpSet_id_map_cast_betaNegativeBinomialMeasure
    (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b) :
    integrableExpSet id ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) =
      if r = 0 then univ else Iic 0 := by
  rcases hr.eq_or_lt with rfl | hr
  · rw [betaNegativeBinomialMeasure_zero ha hb,
      Measure.map_dirac' (by fun_prop : Measurable (Nat.cast : ℕ → ℝ))]
    simp
  rw [ite_eq_right hr.ne']
  have := isProbabilityMeasure_betaNegativeBinomialMeasure hr.le ha hb
  have hnonneg : ∀ᵐ x ∂((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)),
      (0 : ℝ) ≤ id x :=
    MeasurableEmbedding.natCast.ae_map_iff.2 (Eventually.of_forall fun k => Nat.cast_nonneg k)
  refine integrableExpSet_eq_Iic_of_not_integrable_pow aemeasurable_id hnonneg ⌈a⌉₊ ?_
  intro hi
  have h := (integrable_pow_map_cast_betaNegativeBinomialMeasure_iff hr.le ha hb ⌈a⌉₊).mp hi
  exact (Nat.le_ceil a).not_gt (h.resolve_left hr.ne')

/-- The mean of a natural-valued beta-negative-binomial variable after real casting. -/
theorem integral_of_hasLaw_betaNegativeBinomialMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℕ} (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (hfinite : r = 0 ∨ 1 < a) (hX : HasLaw X (betaNegativeBinomialMeasure r a b) P) :
    ∫ ω, (X ω : ℝ) ∂P = r * b / (a - 1) := by
  have hcast : HasLaw (fun ω => (X ω : ℝ))
      ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) P :=
    (hasLaw_map (by fun_prop)).comp hX
  rw [hcast.integral_eq, integral_id_map_cast_betaNegativeBinomialMeasure hr ha hb hfinite]

/-- The variance of a natural-valued beta-negative-binomial variable after real casting. -/
theorem variance_of_hasLaw_betaNegativeBinomialMeasure {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℕ} (hr : 0 ≤ r) (ha : 0 < a) (hb : 0 < b)
    (hfinite : r = 0 ∨ 2 < a) (hX : HasLaw X (betaNegativeBinomialMeasure r a b) P) :
    variance (fun ω => (X ω : ℝ)) P =
      r * b * (a + b - 1) * (a + r - 1) / ((a - 1) ^ 2 * (a - 2)) := by
  have hcast : HasLaw (fun ω => (X ω : ℝ))
      ((betaNegativeBinomialMeasure r a b).map (Nat.cast : ℕ → ℝ)) P :=
    (hasLaw_map (by fun_prop)).comp hX
  rw [hcast.variance_eq, variance_id_map_cast_betaNegativeBinomialMeasure hr ha hb hfinite]

end TauCeti.Probability
