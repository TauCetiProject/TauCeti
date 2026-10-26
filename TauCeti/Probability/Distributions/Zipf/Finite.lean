/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Probability.Distributions.Uniform.Finite
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.MeasureTheory.Measure.Support
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.IntegrableExpMul
public import TauCeti.Probability.GeneratingFunction
public import TauCeti.Probability.Quantile.Discrete
public import TauCeti.Probability.Distributions.Zipf.Basic
public import Mathlib.MeasureTheory.Measure.TotalVariation.Basic
import TauCeti.Probability.Cdf
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# Finite Zipf distributions

The finite Zipf law on `1, …, N` assigns mass proportional to `k ^ (-s)`.
Unlike the infinite Zipf law, it is defined for every real exponent, including zero and
negative exponents. At exponent zero it is uniform; at `N = 0` it is the zero measure.

This file provides normalization, singleton masses, support, parameter measurability, and
finite-sum integration. Every function on the finite support is integrable, giving all
natural moments and the probability generating, moment generating, and characteristic
functions as finite sums. Cumulative masses give the real cdf and least-crossing quantiles,
whose one-sided limits are the support endpoints. For `s > 1`, conditioning the infinite
Zipf law gives the finite law, and the discarded tail mass gives an exact total variation
distance and convergence as `N` tends to infinity.

## References

* N. L. Johnson, A. W. Kemp, and S. Kotz, *Univariate Discrete Distributions*, 3rd ed.,
  Wiley, 2005, on finite power-law distributions.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Topology
open scoped ENNReal

namespace TauCeti.Probability

/-- The normalizing sum for the finite Zipf law on `1, …, N`. -/
def finiteZipfNormalizer (N : ℕ) (s : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-s)

/-- The defining finite sum of the normalizer. -/
theorem finiteZipfNormalizer_def (N : ℕ) (s : ℝ) :
    finiteZipfNormalizer N s = ∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (-s) := (rfl)

/-- The empty normalizing sum is zero. -/
@[simp]
theorem finiteZipfNormalizer_zero_left (s : ℝ) : finiteZipfNormalizer 0 s = 0 := by
  simp [finiteZipfNormalizer]

/-- The normalizing sum is nonnegative at every exponent. -/
theorem finiteZipfNormalizer_nonneg (N : ℕ) (s : ℝ) : 0 ≤ finiteZipfNormalizer N s := by
  exact Finset.sum_nonneg fun k _ ↦ Real.rpow_nonneg (Nat.cast_nonneg k) _

/-- A nonempty finite Zipf support has a positive normalizer, for every real exponent. -/
theorem finiteZipfNormalizer_pos {N : ℕ} (hN : 0 < N) (s : ℝ) :
    0 < finiteZipfNormalizer N s := by
  apply Finset.sum_pos' (fun k _ ↦ Real.rpow_nonneg (Nat.cast_nonneg k) _)
  exact ⟨1, Finset.mem_Icc.mpr ⟨le_rfl, hN⟩, by simp⟩

/-- At exponent zero the normalizer is the support size. -/
@[simp]
theorem finiteZipfNormalizer_zero_right (N : ℕ) : finiteZipfNormalizer N 0 = N := by
  simp [finiteZipfNormalizer, Nat.card_Icc]

/-- The finite Zipf law, normalized on the positive integers at most `N`.
The empty support gives zero, and all real exponents are allowed. -/
def finiteZipfMeasure (N : ℕ) (s : ℝ) : Measure ℕ :=
  ∑ k ∈ Finset.Icc 1 N,
    ENNReal.ofReal ((k : ℝ) ^ (-s) / finiteZipfNormalizer N s) • Measure.dirac k

/-- The finite Zipf law is its finite weighted Dirac sum. -/
theorem finiteZipfMeasure_eq_sum_dirac (N : ℕ) (s : ℝ) :
    finiteZipfMeasure N s = ∑ k ∈ Finset.Icc 1 N,
      ENNReal.ofReal ((k : ℝ) ^ (-s) / finiteZipfNormalizer N s) • Measure.dirac k := (rfl)

/-- There is no probability law on an empty finite Zipf support. -/
@[simp]
theorem finiteZipfMeasure_zero_left (s : ℝ) : finiteZipfMeasure 0 s = 0 := by
  simp [finiteZipfMeasure]

/-- A singleton Zipf support gives the point mass at one at every exponent. -/
@[simp]
theorem finiteZipfMeasure_one_left (s : ℝ) : finiteZipfMeasure 1 s = Measure.dirac 1 := by
  simp [finiteZipfMeasure, finiteZipfNormalizer]

/-- Every finite Zipf measure is finite, including the empty-support case. -/
instance (N : ℕ) (s : ℝ) : IsFiniteMeasure (finiteZipfMeasure N s) := by
  constructor
  simp only [finiteZipfMeasure_eq_sum_dirac, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply_of_mem (mem_univ _), mul_one]
  exact ENNReal.sum_lt_top.mpr fun _ _ ↦ ENNReal.ofReal_lt_top

/-- A finite Zipf law is a probability measure whenever its support is nonempty. -/
theorem isProbabilityMeasure_finiteZipfMeasure {N : ℕ} (hN : 0 < N) (s : ℝ) :
    IsProbabilityMeasure (finiteZipfMeasure N s) := by
  constructor
  rw [finiteZipfMeasure_eq_sum_dirac, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul,
    mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ ↦
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) (finiteZipfNormalizer_nonneg N s)),
    ← Finset.sum_div, ← finiteZipfNormalizer_def,
    div_self (finiteZipfNormalizer_pos hN s).ne', ENNReal.ofReal_one]

/-- Nonempty support is exactly the probability parameter range. -/
@[simp]
theorem isProbabilityMeasure_finiteZipfMeasure_iff (N : ℕ) (s : ℝ) :
    IsProbabilityMeasure (finiteZipfMeasure N s) ↔ 0 < N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [isProbabilityMeasure_iff]
  · exact iff_of_true (isProbabilityMeasure_finiteZipfMeasure hN s) hN

/-- Singleton masses are the normalized powers inside `1, …, N`, and zero outside. -/
@[simp]
theorem finiteZipfMeasure_singleton (N : ℕ) (s : ℝ) (k : ℕ) :
    finiteZipfMeasure N s {k} =
      if k ∈ Finset.Icc 1 N then
        ENNReal.ofReal ((k : ℝ) ^ (-s) / finiteZipfNormalizer N s) else 0 := by
  classical
  rw [finiteZipfMeasure_eq_sum_dirac, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (measurableSet_singleton k), Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq']

/-- The real singleton masses, including the empty-support case. -/
@[simp]
theorem finiteZipfMeasure_real_singleton (N : ℕ) (s : ℝ) (k : ℕ) :
    (finiteZipfMeasure N s).real {k} =
      if k ∈ Finset.Icc 1 N then (k : ℝ) ^ (-s) / finiteZipfNormalizer N s else 0 := by
  rw [measureReal_def, finiteZipfMeasure_singleton]
  split_ifs <;> simp [ENNReal.toReal_ofReal,
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg k) _) (finiteZipfNormalizer_nonneg N s)]

/-- Positive singleton mass is equivalent to membership in the specified support. -/
theorem finiteZipfMeasure_singleton_ne_zero_iff (N : ℕ) (s : ℝ) (k : ℕ) :
    finiteZipfMeasure N s {k} ≠ 0 ↔ k ∈ Finset.Icc 1 N := by
  rw [finiteZipfMeasure_singleton]
  split_ifs with hk
  · have hk' : 0 < (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
    have hN : 0 < N := (zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1).trans_le
      (Finset.mem_Icc.mp hk).2
    simp [div_pos (Real.rpow_pos_of_pos hk' _) (finiteZipfNormalizer_pos hN s), hk]
  · simp [hk]

/-- A finite Zipf variable lies almost surely in its finite support. -/
theorem ae_mem_Icc_finiteZipfMeasure (N : ℕ) (s : ℝ) :
    ∀ᵐ k ∂finiteZipfMeasure N s, k ∈ Finset.Icc 1 N := by
  rw [ae_iff]
  simp [finiteZipfMeasure, Measure.finsetSum_apply, Measure.smul_apply,
    Set.indicator_apply]
  omega

/-- The exact topological support in the discrete native carrier. -/
theorem support_finiteZipfMeasure (N : ℕ) (s : ℝ) :
    (finiteZipfMeasure N s).support = Icc 1 N := by
  ext k
  rw [Measure.mem_support_iff_forall]
  constructor
  · intro h
    have hk := (finiteZipfMeasure_singleton_ne_zero_iff N s k).mp
      (h {k} (by simp)).ne'
    exact Finset.mem_Icc.mp hk
  · intro hk U hU
    exact (pos_iff_ne_zero.mpr
      ((finiteZipfMeasure_singleton_ne_zero_iff N s k).mpr (Finset.mem_Icc.mpr hk))).trans_le
      (measure_mono (singleton_subset_iff.mpr (mem_of_mem_nhds hU)))

/-- Exponent zero recovers the uniform measure on `1, …, N`, including the empty case. -/
@[simp]
theorem finiteZipfMeasure_zero_right (N : ℕ) :
    finiteZipfMeasure N 0 = uniformOn (Finset.Icc 1 N : Set ℕ) := by
  apply Measure.ext_of_singleton
  intro k
  by_cases hN : N = 0
  · subst N
    simp
  · rw [Finset.uniformOn_coe_finset_apply_singleton]
    simp [ENNReal.ofReal_inv_of_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)), Nat.card_Icc]

/-- All functions are integrable against a finite Zipf law. -/
@[simp]
theorem integrable_finiteZipfMeasure {E : Type*} [SeminormedAddGroup E]
    (f : ℕ → E) (N : ℕ) (s : ℝ) : Integrable f (finiteZipfMeasure N s) := by
  rw [finiteZipfMeasure_eq_sum_dirac]
  exact integrable_finsetSum_measure.mpr fun _ _ ↦
    (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Finite Zipf integration is the normalized finite weighted sum. -/
theorem integral_finiteZipfMeasure {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (f : ℕ → E) (N : ℕ) (s : ℝ) :
    ∫ k, f k ∂finiteZipfMeasure N s =
      ∑ k ∈ Finset.Icc 1 N, ((k : ℝ) ^ (-s) / finiteZipfNormalizer N s) • f k := by
  rw [finiteZipfMeasure_eq_sum_dirac, integral_finsetSum_measure]
  · simp [ENNReal.toReal_ofReal,
      div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (finiteZipfNormalizer_nonneg N s)]
  · exact fun _ _ ↦ (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top

/-- Every function is integrable under the real cast of a finite Zipf law. -/
@[simp]
theorem integrable_map_cast_finiteZipfMeasure {E : Type*} [SeminormedAddGroup E]
    (f : ℝ → E) (N : ℕ) (s : ℝ) :
    Integrable f ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)) := by
  rw [(MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff]
  exact integrable_finiteZipfMeasure _ N s

/-- Integration against the real cast of a finite Zipf law. -/
theorem integral_map_cast_finiteZipfMeasure {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (f : ℝ → E) (N : ℕ) (s : ℝ) :
    ∫ x, f x ∂(finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ) =
      ∑ k ∈ Finset.Icc 1 N, ((k : ℝ) ^ (-s) / finiteZipfNormalizer N s) • f k := by
  rw [integral_map Measurable.of_discrete.aemeasurable
    (integrable_map_cast_finiteZipfMeasure f N s).aestronglyMeasurable,
    integral_finiteZipfMeasure]

/-- Every real-power moment is a ratio of finite Zipf normalizers. -/
theorem integral_rpow_map_cast_finiteZipfMeasure (N : ℕ) (s q : ℝ) :
    ∫ x, x ^ q ∂(finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ) =
      finiteZipfNormalizer N (s - q) / finiteZipfNormalizer N s := by
  rw [integral_map_cast_finiteZipfMeasure, finiteZipfNormalizer_def N (s - q), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : 0 < (k : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hk).1
  rw [smul_eq_mul, div_mul_eq_mul_div, ← Real.rpow_add hk']
  congr 2
  ring

/-- Every natural raw moment of the real cast law. Integrability holds for all functions by
`integrable_map_cast_finiteZipfMeasure`. -/
theorem integral_pow_map_cast_finiteZipfMeasure (N : ℕ) (s : ℝ) (n : ℕ) :
    ∫ x, x ^ n ∂(finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ) =
      finiteZipfNormalizer N (s - n) / finiteZipfNormalizer N s := by
  simpa only [Real.rpow_natCast] using integral_rpow_map_cast_finiteZipfMeasure N s n

/-- The mean is the ratio of the normalizers at exponents `s - 1` and `s`. -/
theorem integral_id_map_cast_finiteZipfMeasure (N : ℕ) (s : ℝ) :
    ∫ x, x ∂(finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ) =
      finiteZipfNormalizer N (s - 1) / finiteZipfNormalizer N s := by
  simpa only [pow_one, Nat.cast_one] using integral_pow_map_cast_finiteZipfMeasure N s 1

/-- The variance is obtained from the first two shifted normalizing sums. -/
theorem variance_id_map_cast_finiteZipfMeasure (N : ℕ) (s : ℝ) :
    variance id ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)) =
      finiteZipfNormalizer N (s - 2) / finiteZipfNormalizer N s -
        (finiteZipfNormalizer N (s - 1) / finiteZipfNormalizer N s) ^ 2 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  let _ := isProbabilityMeasure_finiteZipfMeasure hN s
  rw [variance_eq_sub ((memLp_two_iff_integrable_sq (by fun_prop)).mpr
    (integrable_map_cast_finiteZipfMeasure _ N s))]
  simp only [Pi.pow_apply, id_eq, integral_pow_map_cast_finiteZipfMeasure,
    integral_id_map_cast_finiteZipfMeasure, Nat.cast_ofNat]

/-- The real cast law has every exponential moment. -/
@[simp]
theorem integrableExpSet_id_map_cast_finiteZipfMeasure (N : ℕ) (s : ℝ) :
    integrableExpSet id ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)) = univ := by
  ext t
  simp [integrableExpSet]

/-- The finite Zipf probability generating function is a polynomial, at every real argument. -/
theorem pgf_id_finiteZipfMeasure (N : ℕ) (s z : ℝ) :
    pgf id (finiteZipfMeasure N s) z =
      ∑ k ∈ Finset.Icc 1 N, ((k : ℝ) ^ (-s) / finiteZipfNormalizer N s) * z ^ k := by
  rw [pgf_def, integral_finiteZipfMeasure]
  simp only [id_eq, smul_eq_mul]

/-- The moment generating function of the real cast law, valid on all of `ℝ`. -/
theorem mgf_id_map_cast_finiteZipfMeasure (N : ℕ) (s t : ℝ) :
    mgf id ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)) t =
      ∑ k ∈ Finset.Icc 1 N,
        ((k : ℝ) ^ (-s) / finiteZipfNormalizer N s) * Real.exp (t * k) := by
  rw [mgf, integral_map_cast_finiteZipfMeasure]
  simp only [id_eq, smul_eq_mul]

/-- The cumulant generating function is the logarithm of the finite exponential sum. -/
theorem cgf_id_map_cast_finiteZipfMeasure (N : ℕ) (s t : ℝ) :
    cgf id ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)) t =
      Real.log (∑ k ∈ Finset.Icc 1 N,
        ((k : ℝ) ^ (-s) / finiteZipfNormalizer N s) * Real.exp (t * k)) := by
  rw [cgf, mgf_id_map_cast_finiteZipfMeasure]

/-- The characteristic function is the finite Fourier sum of the masses. -/
theorem charFun_map_cast_finiteZipfMeasure (N : ℕ) (s t : ℝ) :
    charFun ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)) t =
      ∑ k ∈ Finset.Icc 1 N,
        (((k : ℝ) ^ (-s) / finiteZipfNormalizer N s : ℝ) : ℂ) *
          Complex.exp (((k : ℝ) * t) * Complex.I) := by
  rw [charFun_apply, integral_map_cast_finiteZipfMeasure]
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.real_smul]
  simp only [Real.inner_apply]
  congr 2
  push_cast
  ring

/-- The totalized finite Zipf family is jointly measurable in its size and real exponent. -/
@[fun_prop]
theorem measurable_finiteZipfMeasure :
    Measurable fun p : ℕ × ℝ ↦ finiteZipfMeasure p.1 p.2 := by
  apply measurable_from_prod_countable_right
  intro N
  apply Measure.measurable_measure.mpr
  intro A hA
  simp only [finiteZipfMeasure_eq_sum_dirac, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul]
  unfold finiteZipfNormalizer
  fun_prop

/-- The native cumulative mass is the ratio of the truncated and full normalizing sums. -/
theorem finiteZipfMeasure_real_Iic (N : ℕ) (s : ℝ) (k : ℕ) :
    (finiteZipfMeasure N s).real (Iic k) =
      finiteZipfNormalizer (min N k) s / finiteZipfNormalizer N s := by
  classical
  rw [measureReal_def, finiteZipfMeasure_eq_sum_dirac, Measure.finsetSum_apply,
    ENNReal.toReal_sum (fun i _ ↦ by
      rw [Measure.smul_apply, smul_eq_mul]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top (Measure.dirac i) _))]
  simp only [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    Measure.dirac_apply' _ measurableSet_Iic, Set.indicator_apply, Set.mem_Iic,
    Pi.one_apply, ENNReal.toReal_ofReal
      (div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        (finiteZipfNormalizer_nonneg N s))]
  rw [finiteZipfNormalizer_def (min N k), Finset.sum_div]
  simp only [apply_ite ENNReal.toReal, ENNReal.toReal_one, ENNReal.toReal_zero,
    mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext j
  simp [and_assoc]

/-- The cdf of the real cast law, with the negative branch before the natural floor. -/
theorem cdf_map_cast_finiteZipfMeasure {N : ℕ} (hN : 0 < N) (s x : ℝ) :
    cdf ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)) x =
      if x < 0 then 0 else
        finiteZipfNormalizer (min N ⌊x⌋₊) s / finiteZipfNormalizer N s := by
  let _ := isProbabilityMeasure_finiteZipfMeasure hN s
  split_ifs with hx
  · exact Measure.cdf_map_natCast_of_neg _ hx
  · rw [Measure.cdf_map_natCast _ (not_lt.mp hx), finiteZipfMeasure_real_Iic]

/-- An interior quantile is the least natural index whose explicit cumulative sum reaches
the requested probability level. -/
theorem quantile_map_cast_finiteZipfMeasure_eq_iff {N : ℕ} (hN : 0 < N) (s : ℝ)
    {u : ℝ} (hu : u ∈ Ioo 0 1) (k : ℕ) :
    ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)).quantile u = k ↔
      IsLeast {j : ℕ | u ≤ finiteZipfNormalizer (min N j) s / finiteZipfNormalizer N s} k := by
  let _ := isProbabilityMeasure_finiteZipfMeasure hN s
  simp only [Measure.quantile_map_natCast_eq_iff _ hu, finiteZipfMeasure_real_Iic]

/-- As the probability level decreases to zero, finite Zipf quantiles tend to one. -/
theorem tendsto_quantile_map_cast_finiteZipfMeasure_nhdsGT_zero {N : ℕ} (hN : 0 < N)
    (s : ℝ) :
    Tendsto (fun u ↦ ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)).quantile u)
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
  let _ := isProbabilityMeasure_finiteZipfMeasure hN s
  have hmass : 0 < (finiteZipfMeasure N s).real (Iic 1) := by
    rw [finiteZipfMeasure_real_Iic, min_eq_right hN]
    simpa [finiteZipfNormalizer] using inv_pos.mpr (finiteZipfNormalizer_pos hN s)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min_iff.mpr ⟨hmass, zero_lt_one⟩)] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 := ⟨hu.1, hu.2.trans_le (min_le_right _ _)⟩
  have hq : ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)).quantile u = (0 + 1 : ℕ) := by
    rw [Measure.quantile_map_natCast_eq_succ_iff _ hu']
    exact ⟨by simpa [finiteZipfMeasure_real_Iic] using hu.1,
      hu.2.le.trans (min_le_left _ _)⟩
  simpa using hq.symm

/-- As the probability level increases to one, finite Zipf quantiles tend to `N`. -/
theorem tendsto_quantile_map_cast_finiteZipfMeasure_nhdsLT_one {N : ℕ} (hN : 0 < N)
    (s : ℝ) :
    Tendsto (fun u ↦ ((finiteZipfMeasure N s).map (Nat.cast : ℕ → ℝ)).quantile u)
      (nhdsWithin 1 (Iio 1)) (nhds (N : ℝ)) := by
  let _ := isProbabilityMeasure_finiteZipfMeasure hN s
  have hmass : 0 < (finiteZipfMeasure N s).real {N} := by
    rw [finiteZipfMeasure_real_singleton, ite_eq_left (Finset.mem_Icc.mpr ⟨hN, le_rfl⟩)]
    exact div_pos (Real.rpow_pos_of_pos (Nat.cast_pos.mpr hN) _)
      (finiteZipfNormalizer_pos hN s)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT (sub_lt_self 1 hmass)] with u hu
  have hu' : u ∈ Ioo (0 : ℝ) 1 :=
    ⟨(sub_nonneg.mpr measureReal_le_one).trans_lt hu.1, hu.2⟩
  symm
  rw [Measure.quantile_map_natCast_eq_iff _ hu']
  refine ⟨?_, fun j hj ↦ ?_⟩
  · simp only [Set.mem_ofPred_eq, finiteZipfMeasure_real_Iic, min_self,
      div_self (finiteZipfNormalizer_pos hN s).ne']
    exact hu'.2.le
  · by_contra hjN
    have hsub : (Iic j : Set ℕ) ⊆ ({N} : Set ℕ)ᶜ := by
      intro k hk
      exact ne_of_lt (hk.trans_lt (not_le.mp hjN))
    have hle : (finiteZipfMeasure N s).real (Iic j) ≤
        1 - (finiteZipfMeasure N s).real {N} := by
      rw [← probReal_compl_eq_one_sub (measurableSet_singleton N)]
      exact measureReal_mono hsub
    exact hu.1.not_ge (hj.trans hle)

/-- The infinite Zipf cumulative mass is a finite normalizing sum divided by the zeta value. -/
theorem zipfMeasure_real_Iic {s : ℝ} (hs : 1 < s) (N : ℕ) :
    (zipfMeasure s).real (Iic N) = finiteZipfNormalizer N s / (riemannZeta s).re := by
  let _ := isProbabilityMeasure_zipfMeasure hs
  calc
    _ = ∑ k ∈ Finset.Iic N, (zipfMeasure s).real {k} := by
      rw [sum_measureReal_singleton, Finset.coe_Iic]
    _ = ∑ k ∈ Finset.Icc 1 N, (zipfMeasure s).real {k} := by
      symm
      apply Finset.sum_subset Finset.Icc_subset_Iic_self
      intro k hk hk'
      have : k = 0 := by simp_all
      simp [this, measureReal_def]
    _ = _ := by
      simp only [zipfMeasure_real_singleton hs, zipfWeightReal_def,
        ← Finset.sum_div, finiteZipfNormalizer_def]

/-- For `s > 1`, the finite Zipf law is the infinite law conditioned to be at most `N`. -/
theorem finiteZipfMeasure_eq_cond (N : ℕ) {s : ℝ} (hs : 1 < s) :
    finiteZipfMeasure N s = cond (zipfMeasure s) (Iic N) := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · have hzero : (Iic (0 : ℕ) : Set ℕ) = {0} := by ext k; simp
    rw [finiteZipfMeasure_zero_left, hzero,
      cond_eq_zero_of_meas_eq_zero (zipfMeasure_singleton_zero s)]
  let _ := isProbabilityMeasure_zipfMeasure hs
  have hZ := riemannZeta_re_pos_of_one_lt hs
  have hH := finiteZipfNormalizer_pos hN s
  have hmass : (zipfMeasure s) (Iic N) ≠ 0 := by
    intro hz
    have hpos : 0 < (zipfMeasure s).real (Iic N) := by
      rw [zipfMeasure_real_Iic hs]
      exact div_pos hH hZ
    simp [measureReal_def, hz] at hpos
  let _ := cond_isProbabilityMeasure hmass
  apply Measure.ext_of_measureReal_singleton
  intro k
  rw [finiteZipfMeasure_real_singleton, measureReal_def,
    cond_apply' (measurableSet_singleton k), ENNReal.toReal_mul, ENNReal.toReal_inv,
    ← measureReal_def, zipfMeasure_real_Iic hs]
  by_cases hk : k ≤ N
  · rw [inter_singleton_of_mem hk, ← measureReal_def, zipfMeasure_real_singleton hs,
      zipfWeightReal_def]
    by_cases hk0 : k = 0
    · simp [hk0, Real.zero_rpow (neg_ne_zero.mpr (zero_lt_one.trans hs).ne')]
    · rw [ite_eq_left (Finset.mem_Icc.mpr ⟨Nat.pos_of_ne_zero hk0, hk⟩)]
      field_simp
  · rw [inter_singleton_of_notMem hk]
    simp [hk]

/-- Mathlib's total variation distance to the infinite law is twice its discarded tail mass. -/
theorem tvDist_finiteZipfMeasure_zipfMeasure {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 1 < s) :
    tvDist (finiteZipfMeasure N s) (zipfMeasure s) =
      2 * (1 - (zipfMeasure s).real (Iic N)) := by
  let _ := isProbabilityMeasure_zipfMeasure hs
  let _ := isProbabilityMeasure_finiteZipfMeasure hN s
  have hH : IsHahnDecomposition (zipfMeasure s) (finiteZipfMeasure N s) (Iic N) := by
    refine ⟨measurableSet_Iic, ?_, ?_⟩
    · rw [finiteZipfMeasure_eq_cond N hs, ProbabilityTheory.cond, Measure.restrict_smul,
        Measure.restrict_restrict measurableSet_Iic, inter_self]
      apply Measure.le_iff.mpr
      intro B hB
      rw [Measure.smul_apply, smul_eq_mul]
      have hi : 1 ≤ ((zipfMeasure s) (Iic N))⁻¹ := by
        simpa using ENNReal.inv_le_inv.mpr (prob_le_one (μ := zipfMeasure s) (s := Iic N))
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hi
        (bot_le : (0 : ℝ≥0∞) ≤ (zipfMeasure s).restrict (Iic N) B)
    · rw [finiteZipfMeasure_eq_cond N hs, ProbabilityTheory.cond, Measure.restrict_smul,
        Measure.restrict_restrict measurableSet_Iic.compl]
      simp only [compl_Iic, Ioi_inter_Iic, Ioc_self, Measure.restrict_empty, smul_zero]
      exact bot_le
  rw [tvDist_comm, hH.tvDist_eq, probReal_compl_eq_one_sub measurableSet_Iic,
    finiteZipfMeasure_real_Iic, min_self, div_self (finiteZipfNormalizer_pos hN s).ne']
  have hzero : (finiteZipfMeasure N s).real (Iic N)ᶜ = 0 := by
    rw [probReal_compl_eq_one_sub measurableSet_Iic, finiteZipfMeasure_real_Iic,
      min_self, div_self (finiteZipfNormalizer_pos hN s).ne']
    norm_num
  rw [hzero]
  ring

/-- Finite Zipf laws converge to the infinite Zipf law in total variation for `s > 1`. -/
theorem tendsto_tvDist_finiteZipfMeasure_zipfMeasure {s : ℝ} (hs : 1 < s) :
    Filter.Tendsto (fun N ↦ tvDist (finiteZipfMeasure N s) (zipfMeasure s))
      Filter.atTop (nhds 0) := by
  let _ := isProbabilityMeasure_zipfMeasure hs
  have hmass : Filter.Tendsto (fun N ↦ (zipfMeasure s).real (Iic N))
      Filter.atTop (nhds 1) := by
    simpa only [measure_univ, ENNReal.toReal_one, measureReal_def, Function.comp_def] using
      (ENNReal.tendsto_toReal (measure_ne_top (zipfMeasure s) univ)).comp
        (tendsto_measure_Iic_atTop (zipfMeasure s))
  have h : Tendsto (fun N ↦ 2 * (1 - (zipfMeasure s).real (Iic N)))
      atTop (nhds (2 * (1 - 1 : ℝ))) := (tendsto_const_nhds.sub hmass).const_mul 2
  simp only [sub_self, mul_zero] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop 0] with N hN
  exact (tvDist_finiteZipfMeasure_zipfMeasure hN hs).symm

end TauCeti.Probability
