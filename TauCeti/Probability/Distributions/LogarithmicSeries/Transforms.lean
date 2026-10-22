/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.MGFAnalytic
public import TauCeti.Probability.Distributions.LogarithmicSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import TauCeti.Analysis.SpecialFunctions.Log.MulExpLtOne
import TauCeti.Analysis.SpecialFunctions.Log.NegLogOneSub

/-!
# Transforms and moments of the logarithmic-series distribution

This file develops the analytic API of the real cast of the logarithmic-series law with parameter
`0 < q < 1`. Its exponential moments exist exactly for `t < -log q`, where the moment-generating
function is `log (1 - q eᵗ) / log (1 - q)`, obtained from the probability-generating function at
`eᵗ`. Differentiating at zero gives the mean `-q / ((1 - q) log (1 - q))` and the variance
`-q (q + log (1 - q)) / ((1 - q)² log (1 - q)²)`. The characteristic function
`log (1 - q e^{it}) / log (1 - q)` uses the principal complex logarithm, whose Taylor series at `1`
converges on the circle `|q e^{it}| = q < 1`.

## Main results

* `integrableExpSet_id_map_cast_logarithmicSeriesMeasure` gives the exact exponential-integrability
  domain.
* `mgf_id_map_cast_logarithmicSeriesMeasure`, `cgf_id_map_cast_logarithmicSeriesMeasure`, and
  `charFun_map_cast_logarithmicSeriesMeasure` compute the three standard transforms.
* `integral_id_map_cast_logarithmicSeriesMeasure` and
  `variance_id_map_cast_logarithmicSeriesMeasure` compute the first two moments.

See N. L. Johnson, A. W. Kemp, and S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley,
2005, Chapter 7.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped Topology

namespace TauCeti

namespace Probability

/-- The exponential integrand for the real cast of a logarithmic-series law is integrable exactly
when `t < -log q`. -/
theorem integrable_exp_mul_id_map_cast_logarithmicSeriesMeasure_iff {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (t : ℝ) :
    Integrable (fun x : ℝ ↦ exp (t * x))
        ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) ↔ t < -log q := by
  have hcomp : ((fun x : ℝ ↦ exp (t * x)) ∘ (Nat.cast : ℕ → ℝ)) = fun n : ℕ ↦ exp t ^ n := by
    funext n
    rw [Function.comp_apply, mul_comm, Real.exp_nat_mul]
  rw [(MeasurableEmbedding.natCast (α := ℝ)).integrable_map_iff, hcomp,
    integrable_pow_logarithmicSeriesMeasure_iff hq0 hq1,
    abs_of_pos (mul_pos hq0 (exp_pos t)), mul_exp_lt_one_iff hq0]

/-- The exact moment-generating domain of the real cast of a logarithmic-series law is
`(-∞, -log q)`. -/
theorem integrableExpSet_id_map_cast_logarithmicSeriesMeasure {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) :
    integrableExpSet id ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) =
      Iio (-log q) := by
  ext t
  exact integrable_exp_mul_id_map_cast_logarithmicSeriesMeasure_iff hq0 hq1 t

/-- The moment-generating function of the real cast of a logarithmic-series law on its exact
domain. -/
theorem mgf_id_map_cast_logarithmicSeriesMeasure {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {t : ℝ}
    (ht : t < -log q) :
    mgf id ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) t =
      log (1 - q * exp t) / log (1 - q) := by
  have habs : |q * exp t| < 1 := by
    rwa [abs_of_pos (mul_pos hq0 (exp_pos t)), mul_exp_lt_one_iff hq0]
  rw [mgf_id_map_natCast, pgf_logarithmicSeriesMeasure hq0 hq1 habs]

/-- The cumulant-generating function of the real cast of a logarithmic-series law on its exact
domain. -/
theorem cgf_id_map_cast_logarithmicSeriesMeasure {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {t : ℝ}
    (ht : t < -log q) :
    cgf id ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) t =
      log (log (1 - q * exp t) / log (1 - q)) := by
  rw [cgf, mgf_id_map_cast_logarithmicSeriesMeasure hq0 hq1 ht]

private theorem neg_log_pos {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) : 0 < -log q :=
  neg_pos.mpr (log_neg hq0 hq1)

private theorem zero_mem_interior_integrableExpSet {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 ∈ interior (integrableExpSet id
      ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ))) := by
  rw [integrableExpSet_id_map_cast_logarithmicSeriesMeasure hq0 hq1, interior_Iio]
  exact neg_log_pos hq0 hq1

private theorem mgf_eventuallyEq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    mgf id ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) =ᶠ[𝓝 0]
      fun t ↦ log (1 - q * exp t) / log (1 - q) := by
  filter_upwards [Iio_mem_nhds (neg_log_pos hq0 hq1)] with t ht
  exact mgf_id_map_cast_logarithmicSeriesMeasure hq0 hq1 ht

private theorem hasDerivAt_mgf_formula (q t : ℝ) (hden : 1 - q * exp t ≠ 0) :
    HasDerivAt (fun u ↦ log (1 - q * exp u) / log (1 - q))
      (-(q * exp t) / (1 - q * exp t) / log (1 - q)) t := by
  have hd : HasDerivAt (fun u ↦ 1 - q * exp u) (-(q * exp t)) t := by
    simpa using ((Real.hasDerivAt_exp t).const_mul q).const_sub 1
  exact (hd.log hden).div_const _

private theorem hasDerivAt_mgf_formula_deriv (q t : ℝ) (hden : 1 - q * exp t ≠ 0) :
    HasDerivAt (fun u ↦ -(q * exp u) / (1 - q * exp u) / log (1 - q))
      (-(q * exp t) / (1 - q * exp t) ^ 2 / log (1 - q)) t := by
  have hn : HasDerivAt (fun u ↦ q * exp u) (q * exp t) t :=
    (Real.hasDerivAt_exp t).const_mul q
  have hd : HasDerivAt (fun u ↦ 1 - q * exp u) (-(q * exp t)) t := by
    simpa using hn.const_sub 1
  have hneg : HasDerivAt (fun u ↦ -(q * exp u)) (-(q * exp t)) t := hn.neg
  convert (hneg.div hd hden).div_const (log (1 - q)) using 1
  field_simp
  ring

/-- The mean of the real cast of a logarithmic-series law is `-q / ((1 - q) log (1 - q))`. -/
theorem integral_id_map_cast_logarithmicSeriesMeasure {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∫ x, x ∂((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) =
      -q / ((1 - q) * log (1 - q)) := by
  have hden : 1 - q * exp 0 ≠ 0 := by simpa using sub_ne_zero.mpr hq1.ne'
  calc
    ∫ x, x ∂((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) =
        deriv (mgf id ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ))) 0 := by
      simpa using (deriv_mgf_zero (zero_mem_interior_integrableExpSet hq0 hq1)).symm
    _ = deriv (fun t ↦ log (1 - q * exp t) / log (1 - q)) 0 :=
      (mgf_eventuallyEq hq0 hq1).deriv_eq
    _ = -q / ((1 - q) * log (1 - q)) := by
      rw [(hasDerivAt_mgf_formula q 0 hden).deriv, exp_zero, mul_one, div_div]

/-- The second raw moment of the real cast, read off from the second derivative of the
moment-generating function at zero. -/
private theorem integral_sq_map_cast_logarithmicSeriesMeasure {q : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) :
    ∫ x, x ^ 2 ∂((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) =
      -q / ((1 - q) ^ 2 * log (1 - q)) := by
  have hden : 1 - q * exp 0 ≠ 0 := by simpa using sub_ne_zero.mpr hq1.ne'
  have hfirst : deriv (fun t ↦ log (1 - q * exp t) / log (1 - q)) =ᶠ[𝓝 0]
      fun t ↦ -(q * exp t) / (1 - q * exp t) / log (1 - q) := by
    filter_upwards [Iio_mem_nhds (neg_log_pos hq0 hq1)] with t ht
    have ht' : q * exp t < 1 := (mul_exp_lt_one_iff hq0).mpr ht
    exact (hasDerivAt_mgf_formula q t (sub_pos.mpr ht').ne').deriv
  calc
    ∫ x, x ^ 2 ∂((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) =
        iteratedDeriv 2 (mgf id ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ))) 0 := by
      simpa using (iteratedDeriv_mgf_zero (zero_mem_interior_integrableExpSet hq0 hq1) 2).symm
    _ = iteratedDeriv 2 (fun t ↦ log (1 - q * exp t) / log (1 - q)) 0 :=
      Filter.EventuallyEq.iteratedDeriv_eq 2 (mgf_eventuallyEq hq0 hq1)
    _ = -q / ((1 - q) ^ 2 * log (1 - q)) := by
      rw [iteratedDeriv_succ, iteratedDeriv_one, hfirst.deriv_eq,
        (hasDerivAt_mgf_formula_deriv q 0 hden).deriv, exp_zero, mul_one, div_div]

/-- The variance of the real cast of a logarithmic-series law is
`-q (q + log (1 - q)) / ((1 - q)² log (1 - q)²)`. -/
theorem variance_id_map_cast_logarithmicSeriesMeasure {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    variance id ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) =
      -q * (q + log (1 - q)) / ((1 - q) ^ 2 * log (1 - q) ^ 2) := by
  have _ := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  have hmem := memLp_of_mem_interior_integrableExpSet
    (zero_mem_interior_integrableExpSet hq0 hq1) 2
  have hq : 1 - q ≠ 0 := sub_ne_zero.mpr hq1.ne'
  have hlog : log (1 - q) ≠ 0 := (log_one_sub_neg hq0 hq1).ne
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq]
  rw [integral_id_map_cast_logarithmicSeriesMeasure hq0 hq1,
    integral_sq_map_cast_logarithmicSeriesMeasure hq0 hq1]
  field_simp
  ring

/-- The characteristic function of the real cast of a logarithmic-series law, with the principal
complex logarithm. -/
theorem charFun_map_cast_logarithmicSeriesMeasure {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (t : ℝ) :
    charFun ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) t =
      Complex.log (1 - q * Complex.exp (Complex.I * t)) / (log (1 - q) : ℂ) := by
  set z : ℂ := q * Complex.exp (Complex.I * t) with hz_def
  have hz : ‖z‖ < 1 := by
    rw [hz_def, norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hq0.le]
    exact hq1
  have hlog : (log (1 - q) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (log_one_sub_neg hq0 hq1).ne
  have hsum := (Complex.hasSum_taylorSeries_neg_log hz).div_const (-(log (1 - q) : ℂ))
  rw [neg_div_neg_eq] at hsum
  have _ := isProbabilityMeasure_logarithmicSeriesMeasure hq0 hq1
  have hweight_ne_top (k : ℕ) : logarithmicSeriesWeight q k ≠ ⊤ := by
    rw [← logarithmicSeriesMeasure_singleton hq0 hq1]
    exact measure_ne_top _ _
  rw [charFun_apply_real, integral_map (by fun_prop) (by fun_prop),
    logarithmicSeriesMeasure_eq_sum_dirac hq0 hq1, integral_sum_dirac hweight_ne_top,
    ← hsum.tsum_eq]
  congr with k
  have hexp : Complex.exp ((t : ℂ) * ((k : ℝ) : ℂ) * Complex.I) =
      Complex.exp (Complex.I * t) ^ k := by
    rw [← Complex.exp_nat_mul]
    push_cast
    ring_nf
  rw [Complex.real_smul, logarithmicSeriesWeight_toReal hq0 hq1,
    logarithmicSeriesWeightReal_eq_div, hexp, hz_def, mul_pow]
  push_cast
  ring

/-- A real random variable with a logarithmic-series law has mean
`-q / ((1 - q) log (1 - q))`. -/
theorem integral_of_hasLaw_map_cast_logarithmicSeriesMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {q : ℝ}
    (hX : HasLaw X ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) P)
    (hq0 : 0 < q) (hq1 : q < 1) :
    P[X] = -q / ((1 - q) * log (1 - q)) := by
  rw [hX.integral_eq, integral_id_map_cast_logarithmicSeriesMeasure hq0 hq1]

/-- A real random variable with a logarithmic-series law has variance
`-q (q + log (1 - q)) / ((1 - q)² log (1 - q)²)`. -/
theorem variance_of_hasLaw_map_cast_logarithmicSeriesMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ} {q : ℝ}
    (hX : HasLaw X ((logarithmicSeriesMeasure q).map (Nat.cast : ℕ → ℝ)) P)
    (hq0 : 0 < q) (hq1 : q < 1) :
    variance X P = -q * (q + log (1 - q)) / ((1 - q) ^ 2 * log (1 - q) ^ 2) := by
  rw [hX.variance_eq, variance_id_map_cast_logarithmicSeriesMeasure hq0 hq1]

end Probability

end TauCeti
