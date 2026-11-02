/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.Cdf
public import TauCeti.Probability.Distributions.Uniform.Finite
public import TauCeti.Probability.GeneratingFunction
public import TauCeti.Probability.Quantile.Discrete
import Mathlib.Algebra.Field.GeomSum
import Mathlib.NumberTheory.Bernoulli
import Mathlib.Order.Interval.Finset.Nat

/-!
# The uniform distribution on an integer interval

For integers `a ≤ b`, the discrete uniform law on `{a, …, b}` is Mathlib's conditional counting
measure `ProbabilityTheory.uniformOn (Set.Icc a b)` on `ℤ`. It gives mass `1 / N` to each of the
`N = b - a + 1` integers of the interval; for `b < a` the interval is empty and the measure is
zero. No new definition is introduced: this file computes the elementary theory of this measure.

## Main results

* `TauCeti.Probability.uniformOn_Icc_int_apply_singleton` and
  `TauCeti.Probability.support_uniformOn_Icc_int`: the native masses and the support.
* `TauCeti.Probability.map_add_const_uniformOn_Icc_int` and
  `TauCeti.Probability.map_neg_uniformOn_Icc_int`: integer translations shift the endpoints and
  reflection negates and exchanges them.
* `TauCeti.Probability.map_toNat_sub_uniformOn_Icc_int`: translating by `-a` gives the uniform
  law on `{0, …, N - 1} ⊆ ℕ`, whose probability generating function is
  `TauCeti.Probability.pgf_uniformOn_Iio`.
* `TauCeti.Probability.integral_intCast_uniformOn_Icc` and
  `TauCeti.Probability.variance_intCast_uniformOn_Icc`: mean `(a + b) / 2` and variance
  `(N ^ 2 - 1) / 12`.
* `TauCeti.Probability.mgf_intCast_uniformOn_Icc` and
  `TauCeti.Probability.charFun_map_intCast_uniformOn_Icc`: finite geometric sums for the moment
  generating and characteristic functions.
* `TauCeti.Probability.cdf_map_intCast_uniformOn_Icc` and
  `TauCeti.Probability.quantile_map_intCast_uniformOn_Icc`: the cdf of the real cast law and its
  lower quantile `a + ⌈N u⌉ - 1`.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set Topology
open scoped ENNReal

namespace TauCeti.Probability

variable (a b : ℤ)

/-! ### Masses and transport -/

/-- The uniform law on a nonempty integer interval is a probability measure. -/
theorem isProbabilityMeasure_uniformOn_Icc_int {a b : ℤ} (h : a ≤ b) :
    IsProbabilityMeasure (uniformOn (Icc a b : Set ℤ)) :=
  isProbabilityMeasure_uniformOn (finite_Icc a b) (nonempty_Icc.mpr h)

/-- The uniform law on an empty integer interval is the zero measure. -/
theorem uniformOn_Icc_int_of_lt {a b : ℤ} (h : b < a) : uniformOn (Icc a b : Set ℤ) = 0 := by
  rw [Icc_eq_empty_of_lt h, uniformOn_empty_meas]

/-- Each integer of `Icc a b` has mass `1 / (b + 1 - a)`; every other integer has mass zero. -/
@[simp]
theorem uniformOn_Icc_int_apply_singleton (k : ℤ) :
    uniformOn (Icc a b : Set ℤ) {k} =
      if k ∈ Icc a b then (((b + 1 - a).toNat : ℝ≥0∞))⁻¹ else 0 := by
  simpa only [Finset.coe_Icc, Finset.mem_Icc, mem_Icc, Int.card_Icc] using
    Finset.uniformOn_coe_finset_apply_singleton (Finset.Icc a b) k

/-- The topological support of the uniform law on `Icc a b` is the interval itself. -/
@[simp]
theorem support_uniformOn_Icc_int : (uniformOn (Icc a b : Set ℤ)).support = Icc a b := by
  rw [← Finset.coe_Icc, Finset.support_uniformOn_coe_finset]

/-- An integer translation of the uniform law on `Icc a b` is uniform on the translated
interval. -/
@[simp]
theorem map_add_const_uniformOn_Icc_int (c : ℤ) :
    (uniformOn (Icc a b : Set ℤ)).map (· + c) = uniformOn (Icc (a + c) (b + c) : Set ℤ) := by
  refine BijOn.map_uniformOn ⟨fun k hk ↦ ?_, fun k _ l _ hkl ↦ ?_, fun k hk ↦ ?_⟩
  · simp only [mem_Icc] at hk ⊢
    omega
  · simpa using hkl
  · simp only [mem_Icc] at hk
    exact ⟨k - c, by simp only [mem_Icc]; omega, by simp⟩

/-- Reflection maps the uniform law on `Icc a b` to the uniform law on `Icc (-b) (-a)`. -/
@[simp]
theorem map_neg_uniformOn_Icc_int :
    (uniformOn (Icc a b : Set ℤ)).map (fun k ↦ -k) = uniformOn (Icc (-b) (-a) : Set ℤ) := by
  refine BijOn.map_uniformOn ⟨fun k hk ↦ ?_, fun k _ l _ hkl ↦ ?_, fun k hk ↦ ?_⟩
  · simp only [mem_Icc] at hk ⊢
    omega
  · simpa using hkl
  · simp only [mem_Icc] at hk
    exact ⟨-k, by simp only [mem_Icc]; omega, by simp⟩

/-- Translating the uniform law on `Icc a b` by `-a` gives the uniform law on the natural numbers
below `b + 1 - a`. -/
theorem map_toNat_sub_uniformOn_Icc_int :
    (uniformOn (Icc a b : Set ℤ)).map (fun k ↦ (k - a).toNat) =
      uniformOn (Iio (b + 1 - a).toNat : Set ℕ) := by
  refine BijOn.map_uniformOn ⟨fun k hk ↦ ?_, fun k hk l hl hkl ↦ ?_, fun j hj ↦ ?_⟩
  · simp only [mem_Icc, mem_Iio] at hk ⊢
    omega
  · simp only [mem_Icc] at hk hl
    simp only at hkl
    omega
  · simp only [mem_Iio] at hj
    exact ⟨a + j, by simp only [mem_Icc]; omega, by simp⟩

/-! ### Integration -/

/-- Every function is integrable against the uniform law on an integer interval. -/
@[simp]
theorem integrable_uniformOn_Icc_int {E : Type*} [SeminormedAddGroup E] (f : ℤ → E) :
    Integrable f (uniformOn (Icc a b : Set ℤ)) := by
  rw [← Finset.coe_Icc]
  exact Finset.integrable_uniformOn_finset _ f

/-- Integration against the uniform law on `Icc a b` is the average over the interval. -/
theorem integral_uniformOn_Icc_int {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℤ → E) :
    ∫ k, f k ∂uniformOn (Icc a b : Set ℤ) =
      (((b + 1 - a).toNat : ℝ))⁻¹ • ∑ k ∈ Finset.Icc a b, f k := by
  rw [← Finset.coe_Icc, Finset.integral_uniformOn_finset, Int.card_Icc]

/-- The average over `Icc a b`, reindexed by the offset from the left endpoint. -/
private theorem integral_uniformOn_Icc_int_eq_sum_range {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℤ → E) :
    ∫ k, f k ∂uniformOn (Icc a b : Set ℤ) =
      (((b + 1 - a).toNat : ℝ))⁻¹ • ∑ j ∈ Finset.range (b + 1 - a).toNat, f (a + j) := by
  simp [integral_uniformOn_Icc_int, Int.Icc_eq_finset_map]

/-- The mean of the uniform law on `Icc a b` is the midpoint `(a + b) / 2`. -/
theorem integral_intCast_uniformOn_Icc {a b : ℤ} (h : a ≤ b) :
    ∫ k : ℤ, (k : ℝ) ∂uniformOn (Icc a b : Set ℤ) = (a + b) / 2 := by
  have hN : (((b + 1 - a).toNat : ℕ) : ℝ) = b - a + 1 := by norm_cast; omega
  have hsum_id (N : ℕ) : ∑ j ∈ Finset.range N, (j : ℝ) = N * (N - 1) / 2 := by
    have := congrArg (Rat.cast : ℚ → ℝ) (sum_range_pow N 1)
    norm_num [Finset.sum_range_succ] at this
    rw [this]
    ring
  rw [integral_uniformOn_Icc_int_eq_sum_range]
  simp only [Int.cast_add, Int.cast_natCast, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, hsum_id, smul_eq_mul, hN]
  have hpos : (b - a + 1 : ℝ) ≠ 0 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    positivity
  field_simp
  ring

/-- The variance of the uniform law on `Icc a b` is `(N ^ 2 - 1) / 12`, where `N = b - a + 1`
is the number of integers in the interval. -/
theorem variance_intCast_uniformOn_Icc {a b : ℤ} (h : a ≤ b) :
    variance (Int.cast : ℤ → ℝ) (uniformOn (Icc a b : Set ℤ)) =
      ((b - a + 1 : ℝ) ^ 2 - 1) / 12 := by
  have := isProbabilityMeasure_uniformOn_Icc_int h
  rw [variance_eq_integral (by fun_prop), integral_intCast_uniformOn_Icc h,
    integral_uniformOn_Icc_int_eq_sum_range]
  have hN : (((b + 1 - a).toNat : ℕ) : ℝ) = b - a + 1 := by norm_cast; omega
  have hsum_id (N : ℕ) : ∑ j ∈ Finset.range N, (j : ℝ) = N * (N - 1) / 2 := by
    have := congrArg (Rat.cast : ℚ → ℝ) (sum_range_pow N 1)
    norm_num [Finset.sum_range_succ] at this
    rw [this]
    ring
  have hsum_sq (N : ℕ) :
      ∑ j ∈ Finset.range N, (j : ℝ) ^ 2 = N * (N - 1) * (2 * N - 1) / 6 := by
    have := congrArg (Rat.cast : ℚ → ℝ) (sum_range_pow N 2)
    norm_num [Finset.sum_range_succ] at this
    rw [this]
    ring
  set N := (b + 1 - a).toNat
  have hsum : ∑ j ∈ Finset.range N, (((a + j : ℤ) : ℝ) - (a + b) / 2) ^ 2 =
      ∑ j ∈ Finset.range N, ((j : ℝ) ^ 2 - (b - a) * j + (b - a) ^ 2 / 4) := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast
    ring
  rw [hsum, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    hsum_sq, hsum_id, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    hN, smul_eq_mul]
  have hpos : (b - a + 1 : ℝ) ≠ 0 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    positivity
  field_simp
  ring

/-! ### Generating functions -/

/-- The probability generating function of the uniform law on `{0, …, N - 1}` is the
normalized finite geometric sum. -/
theorem pgf_uniformOn_Iio (N : ℕ) (z : ℝ) :
    pgf id (uniformOn (Iio N : Set ℕ)) z = (N : ℝ)⁻¹ * ∑ j ∈ Finset.range N, z ^ j := by
  rw [pgf_def, ← Finset.coe_range, Finset.integral_uniformOn_finset, Finset.card_range]
  simp

/-- Away from `z = 1`, the probability generating function of the uniform law on
`{0, …, N - 1}` is `(z ^ N - 1) / (N (z - 1))`. -/
theorem pgf_uniformOn_Iio_of_ne_one (N : ℕ) {z : ℝ} (hz : z ≠ 1) :
    pgf id (uniformOn (Iio N : Set ℕ)) z = (z ^ N - 1) / (N * (z - 1)) := by
  rw [pgf_uniformOn_Iio, geom_sum_eq hz, mul_comm (N : ℝ), ← div_div, inv_mul_eq_div]

/-- Every exponential moment of the uniform law on an integer interval is finite. -/
@[simp]
theorem integrableExpSet_intCast_uniformOn_Icc :
    integrableExpSet (Int.cast : ℤ → ℝ) (uniformOn (Icc a b : Set ℤ)) = univ := by
  ext t
  simp [integrableExpSet]

/-- Away from `t = 0`, the moment generating function of the uniform law on `Icc a b` is the
finite geometric sum `e ^ (t a) (e ^ (t N) - 1) / (N (e ^ t - 1))`, where `N = b - a + 1`. At
`t = 0` it is `1`, by `ProbabilityTheory.mgf_zero`. -/
theorem mgf_intCast_uniformOn_Icc {a b : ℤ} (h : a ≤ b) {t : ℝ} (ht : t ≠ 0) :
    mgf (Int.cast : ℤ → ℝ) (uniformOn (Icc a b : Set ℤ)) t =
      exp (t * a) * (exp (t * (b - a + 1)) - 1) / ((b - a + 1) * (exp t - 1)) := by
  have hexp : exp t ≠ 1 := fun h ↦ ht (Real.exp_eq_one_iff t |>.mp h)
  rw [mgf, integral_uniformOn_Icc_int_eq_sum_range]
  have hterm (j : ℕ) : exp (t * ((a + j : ℤ) : ℝ)) = exp (t * a) * exp t ^ j := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    push_cast
    ring_nf
  simp only [hterm, ← Finset.mul_sum, smul_eq_mul]
  have hN : (((b + 1 - a).toNat : ℕ) : ℝ) = b - a + 1 := by norm_cast; omega
  rw [geom_sum_eq hexp, ← Real.exp_nat_mul, hN,
    mul_comm (b - a + 1 : ℝ) t]
  have hpos : (b - a + 1 : ℝ) ≠ 0 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    positivity
  have hexp' : rexp t - 1 ≠ 0 := sub_ne_zero.mpr hexp
  field_simp

/-- Away from `t = 0`, the cumulant generating function of the uniform law on `Icc a b` is the
linear term `t a` plus the logarithm of the positive geometric ratio. -/
theorem cgf_intCast_uniformOn_Icc {a b : ℤ} (h : a ≤ b) {t : ℝ} (ht : t ≠ 0) :
    cgf (Int.cast : ℤ → ℝ) (uniformOn (Icc a b : Set ℤ)) t =
      t * a + log ((exp (t * (b - a + 1)) - 1) / ((b - a + 1) * (exp t - 1))) := by
  have hN : (0 : ℝ) < b - a + 1 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith
  have hratio : 0 < (exp (t * (b - a + 1)) - 1) / ((b - a + 1) * (exp t - 1)) := by
    rcases ht.lt_or_gt with ht | ht
    · refine div_pos_of_neg_of_neg ?_ (mul_neg_of_pos_of_neg hN ?_)
      · rw [sub_neg, Real.exp_lt_one_iff]
        exact mul_neg_of_neg_of_pos ht hN
      · rwa [sub_neg, Real.exp_lt_one_iff]
    · refine div_pos ?_ (mul_pos hN ?_)
      · rw [sub_pos, Real.one_lt_exp_iff]
        exact mul_pos ht hN
      · rwa [sub_pos, Real.one_lt_exp_iff]
  rw [cgf, mgf_intCast_uniformOn_Icc h ht, mul_div_assoc,
    Real.log_mul (Real.exp_pos _).ne' hratio.ne', Real.log_exp]

/-- The characteristic function of the real cast of the uniform law on `Icc a b` is the
average of the characters over the interval. -/
theorem charFun_map_intCast_uniformOn_Icc (t : ℝ) :
    charFun ((uniformOn (Icc a b : Set ℤ)).map (Int.cast : ℤ → ℝ)) t =
      (((b + 1 - a).toNat : ℂ))⁻¹ *
        ∑ k ∈ Finset.Icc a b, Complex.exp ((t : ℂ) * k * Complex.I) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop), integral_uniformOn_Icc_int,
    Complex.real_smul]
  push_cast
  ring

/-- When `e ^ (i t) ≠ 1`, the characteristic function of the real cast of the uniform law on
`Icc a b` is the finite geometric sum `e ^ (i t a) (e ^ (i t N) - 1) / (N (e ^ (i t) - 1))`,
where `N = b - a + 1`. -/
theorem charFun_map_intCast_uniformOn_Icc_of_exp_ne_one {a b : ℤ} (h : a ≤ b) {t : ℝ}
    (ht : Complex.exp ((t : ℂ) * Complex.I) ≠ 1) :
    charFun ((uniformOn (Icc a b : Set ℤ)).map (Int.cast : ℤ → ℝ)) t =
      Complex.exp ((t : ℂ) * a * Complex.I) *
        (Complex.exp ((t : ℂ) * (b - a + 1) * Complex.I) - 1) /
          ((b - a + 1) * (Complex.exp ((t : ℂ) * Complex.I) - 1)) := by
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
    integral_uniformOn_Icc_int_eq_sum_range]
  have hterm (j : ℕ) : Complex.exp ((t : ℂ) * (((a + j : ℤ) : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((t : ℂ) * a * Complex.I) * Complex.exp ((t : ℂ) * Complex.I) ^ j := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    push_cast
    ring_nf
  have hN : ((((b + 1 - a).toNat : ℕ) : ℝ) : ℂ) = (b : ℂ) - a + 1 := by norm_cast; omega
  have hpow : Complex.exp ((t : ℂ) * Complex.I) ^ (b + 1 - a).toNat =
      Complex.exp ((t : ℂ) * (b - a + 1) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    rw [← Complex.ofReal_natCast, hN]
    ring
  simp only [hterm, ← Finset.mul_sum, geom_sum_eq ht, Complex.real_smul, hpow]
  rw [Complex.ofReal_inv, hN]
  field_simp

/-! ### Cumulative distribution function and quantiles -/

/-- The cumulative mass of the uniform law on `Icc a b` up to an integer `k`: zero below `a`,
`(k - a + 1) / N` on the interval, and one above `b`, where `N = b - a + 1`. -/
theorem uniformOn_Icc_int_real_Iic {a b : ℤ} (h : a ≤ b) (k : ℤ) :
    (uniformOn (Icc a b : Set ℤ)).real (Iic k) =
      if k < a then (0 : ℝ) else if k ≤ b then (k - a + 1 : ℝ) / (b - a + 1) else 1 := by
  classical
  rw [measureReal_def, ← uniformOn_inter_self (finite_Icc a b)]
  split_ifs with hka hkb
  · have hempty : Icc a b ∩ Iic k = ∅ := by
      ext j
      simp only [mem_inter_iff, mem_Icc, mem_Iic, mem_empty_iff_false, iff_false]
      omega
    simp [hempty]
  · have hinter : Icc a b ∩ Iic k = Icc a k := by
      ext j
      simp only [mem_inter_iff, mem_Icc, mem_Iic]
      omega
    have hsub : Finset.Icc a k ⊆ Finset.Icc a b := Finset.Icc_subset_Icc_right hkb
    have hNk : (((k + 1 - a).toNat : ℕ) : ℝ) = k - a + 1 := by norm_cast; omega
    have hN : (((b + 1 - a).toNat : ℕ) : ℝ) = b - a + 1 := by norm_cast; omega
    rw [hinter, ← Finset.coe_Icc, ← Finset.coe_Icc, uniformOn_apply_finset,
      Finset.inter_eq_right.mpr hsub, Int.card_Icc, Int.card_Icc, ENNReal.toReal_div,
      ENNReal.toReal_natCast, ENNReal.toReal_natCast,
      hNk, hN]
  · rw [inter_eq_left.mpr (fun j hj ↦ by simp only [mem_Icc] at hj; simp only [mem_Iic]; omega),
      uniformOn_self (finite_Icc a b) (nonempty_Icc.mpr h)]
    simp

/-- The cdf of the real cast of the uniform law on `Icc a b`, evaluated through the integer
floor of its argument. -/
theorem cdf_map_intCast_uniformOn_Icc {a b : ℤ} (h : a ≤ b) (x : ℝ) :
    cdf ((uniformOn (Icc a b : Set ℤ)).map (Int.cast : ℤ → ℝ)) x =
      if ⌊x⌋ < a then (0 : ℝ) else if ⌊x⌋ ≤ b then (⌊x⌋ - a + 1 : ℝ) / (b - a + 1) else 1 := by
  have := isProbabilityMeasure_uniformOn_Icc_int h
  rw [Measure.cdf_map_intCast, uniformOn_Icc_int_real_Iic h]

/-- For `0 < u < 1`, the lower quantile of the real cast of the uniform law on `Icc a b` is
`a + ⌈N u⌉ - 1`, where `N = b - a + 1`. -/
theorem quantile_map_intCast_uniformOn_Icc {a b : ℤ} (h : a ≤ b) {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((uniformOn (Icc a b : Set ℤ)).map (Int.cast : ℤ → ℝ)).quantile u =
      ((a + ⌈(b - a + 1 : ℝ) * u⌉ - 1 : ℤ) : ℝ) := by
  have := isProbabilityMeasure_uniformOn_Icc_int h
  have hN : (0 : ℝ) < b - a + 1 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith
  set c := ⌈(b - a + 1 : ℝ) * u⌉ with hc
  have hc1 : 1 ≤ c := Int.one_le_ceil_iff.mpr (mul_pos hN hu.1)
  have hcN : c ≤ b - a + 1 := by
    rw [hc, Int.ceil_le]
    push_cast
    nlinarith [hu.2]
  rw [Measure.quantile_map_intCast_eq_iff _ hu]
  simp_rw [uniformOn_Icc_int_real_Iic h]
  refine ⟨?_, fun j hj ↦ ?_⟩
  · simp only [mem_ofPred_eq]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), le_div_iff₀ hN]
    have : (b - a + 1 : ℝ) * u ≤ c := Int.le_ceil _
    push_cast
    linarith
  · simp only [mem_ofPred_eq] at hj
    split_ifs at hj with hja hjb
    · linarith [hu.1]
    · rw [le_div_iff₀ hN] at hj
      have : c ≤ j - a + 1 := by
        rw [hc, Int.ceil_le]
        push_cast
        linarith
      omega
    · omega

/-- As the level tends to zero from above, the lower quantile tends to the left endpoint `a`. -/
theorem tendsto_quantile_map_intCast_uniformOn_Icc_nhdsGT_zero {a b : ℤ} (h : a ≤ b) :
    Tendsto ((uniformOn (Icc a b : Set ℤ)).map (Int.cast : ℤ → ℝ)).quantile (𝓝[>] 0)
      (𝓝 a) := by
  have hN : (1 : ℝ) ≤ b - a + 1 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith
  have hN0 : (0 : ℝ) < b - a + 1 := zero_lt_one.trans_le hN
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (inv_pos.mpr hN0)] with u hu
  rw [quantile_map_intCast_uniformOn_Icc h ⟨hu.1, hu.2.trans_le (inv_le_one_of_one_le₀ hN)⟩]
  have hlt : (b - a + 1 : ℝ) * u < 1 :=
    calc (b - a + 1 : ℝ) * u < (b - a + 1) * (b - a + 1 : ℝ)⁻¹ := mul_lt_mul_of_pos_left hu.2 hN0
      _ = 1 := mul_inv_cancel₀ hN0.ne'
  have hc : ⌈(b - a + 1 : ℝ) * u⌉ = 1 := by
    rw [Int.ceil_eq_iff]
    constructor
    · norm_num
      exact mul_pos hN0 hu.1
    · norm_num
      exact hlt.le
  rw [hc]
  simp

/-- As the level tends to one from below, the lower quantile tends to the right endpoint `b`. -/
theorem tendsto_quantile_map_intCast_uniformOn_Icc_nhdsLT_one {a b : ℤ} (h : a ≤ b) :
    Tendsto ((uniformOn (Icc a b : Set ℤ)).map (Int.cast : ℤ → ℝ)).quantile (𝓝[<] 1)
      (𝓝 b) := by
  have hN : (1 : ℝ) ≤ b - a + 1 := by
    have : (a : ℝ) ≤ b := by exact_mod_cast h
    linarith
  have hN0 : (0 : ℝ) < b - a + 1 := zero_lt_one.trans_le hN
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (sub_lt_self (1 : ℝ) (inv_pos.mpr hN0))] with u hu
  have hu0 : 0 < u := (sub_nonneg.mpr (inv_le_one_of_one_le₀ hN)).trans_lt hu.1
  rw [quantile_map_intCast_uniformOn_Icc h ⟨hu0, hu.2⟩]
  have hlow : (b - a + 1 : ℝ) - 1 < (b - a + 1) * u := by
    have h3 : (b - a + 1 : ℝ) * (1 - (b - a + 1 : ℝ)⁻¹) < (b - a + 1) * u :=
      mul_lt_mul_of_pos_left hu.1 hN0
    rwa [mul_sub, mul_one, mul_inv_cancel₀ hN0.ne'] at h3
  have hc : ⌈(b - a + 1 : ℝ) * u⌉ = b - a + 1 := by
    rw [Int.ceil_eq_iff]
    push_cast
    constructor
    · linarith
    · nlinarith [hu.2]
  rw [hc]
  push_cast
  ring_nf

end TauCeti.Probability
