/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.TruncatedNormal.Basic
public import Mathlib.Probability.Moments.Variance
import TauCeti.Probability.Distributions.Tilted

/-!
# Moments and transforms of the truncated normal distribution

This file computes the moment-generating function, the cumulant-generating function, the mean
and the variance of `truncatedNormalMeasure m v s`, the Gaussian law `N(m, v)` conditioned on a
set `s`.

**Moment-generating function.** For every set `s` and every variance, exponential tilting of the
Gaussian law shifts its mean, so

`E[exp (t X)] = exp (m t + v t² / 2) * N(m + v t, v)(s) / N(m, v)(s)`

(`mgf_id_truncatedNormalMeasure`). In particular the exponential moments are finite for every
`t`, so `integrableExpSet id` is the whole line and every polynomial moment is finite. For an
interval with finite bounds `l ≤ r` at positive variance, write `s₀ = √v`, `α = (l - m) / s₀`,
`β = (r - m) / s₀`, `Φ` for the standard Gaussian cdf and `Z = Φ β - Φ α`; then the mgf is
`exp (m t + v t² / 2) * (Φ (β - s₀ t) - Φ (α - s₀ t)) / Z`.

**Mean and variance.** At positive variance and for an interval with extended bounds `l < r`,
the moments involve the Gaussian density at the two bounds. At an infinite bound this density is
replaced by its limit `0`, which is the role of `gaussianPDFRealEReal` from
`TauCeti.Probability.Distributions.Gaussian.Basic`. Writing `g` for it,
`Z = N(m, v)(s)` for the mass of the interval, and `x.toReal` for the real value of a finite
bound,

* `E[X] = m + v (g l - g r) / Z`;
* `Var X = v (1 + ((l - m) g l - (r - m) g r) / Z - v ((g l - g r) / Z)²)`,

where the product `(l - m) g l` is read as `0` at an infinite bound. With the standard Gaussian
density `φ` and finite bounds these become the classical
`E[X] = m + s₀ (φ α - φ β) / Z` and
`Var X = v (1 + (α φ α - β φ β) / Z - ((φ α - φ β) / Z)²)`.

The mean `M'(0)` and the second moment `M''(0)` are the first two derivatives at `0` of the
closed-form mgf `M`, and the variance is `M''(0) - M'(0)²`. As a function of the mean `μ`, the
Gaussian mass of the interval is a difference of cdf values at the bounds, whose derivative is a
difference of Gaussian densities (`hasDerivAt_measureReal_gaussianReal`).

## Main results

* `TauCeti.Probability.mgf_id_truncatedNormalMeasure` and
  `TauCeti.Probability.mgf_id_truncatedNormalMeasure_eq_cdf_zero_one` — the mgf;
* `TauCeti.Probability.integrableExpSet_id_truncatedNormalMeasure` — exponential moments of
  every order;
* `TauCeti.Probability.cgf_id_truncatedNormalMeasure` — the cgf;
* `TauCeti.Probability.integral_id_truncatedNormalMeasure` and
  `TauCeti.Probability.integral_id_truncatedNormalMeasure_eq_cdf_zero_one` — the mean;
* `TauCeti.Probability.variance_id_truncatedNormalMeasure` and
  `TauCeti.Probability.variance_id_truncatedNormalMeasure_eq_cdf_zero_one` — the variance.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 1,
  2nd ed., Wiley (1994), Chapter 13, Section 10.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Real
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {m : ℝ} {v : ℝ≥0} {s : Set ℝ} {l r : EReal}

/-! ### Moment- and cumulant-generating functions -/

/-- The moment-generating function of the Gaussian law `N(m, v)` conditioned on any set `s`:
`exp (m t + v t² / 2)` times the ratio of the masses of `s` under `N(m + v t, v)` and `N(m, v)`.
Both sides vanish when `s` is Gaussian-null. -/
theorem mgf_id_truncatedNormalMeasure (m : ℝ) (v : ℝ≥0) (s : Set ℝ) (t : ℝ) :
    mgf id (truncatedNormalMeasure m v s) t =
      exp (m * t + v * t ^ 2 / 2) * (gaussianReal (m + v * t) v).real s /
        (gaussianReal m v).real s := by
  rw [mgf, truncatedNormalMeasure_def, ProbabilityTheory.cond, integral_smul_measure]
  simp only [id_eq]
  rw [setIntegral_exp_mul_gaussianReal, ENNReal.toReal_inv, ← measureReal_def, smul_eq_mul]
  ring

/-- Every exponential moment of a truncated normal law is finite. -/
theorem integrable_exp_mul_truncatedNormalMeasure (m : ℝ) (v : ℝ≥0) (s : Set ℝ) (t : ℝ) :
    Integrable (fun x => exp (t * x)) (truncatedNormalMeasure m v s) := by
  by_cases h0 : gaussianReal m v s = 0
  · rw [truncatedNormalMeasure_eq_zero_iff.2 h0]
    exact integrable_zero_measure
  · rw [truncatedNormalMeasure_def, ProbabilityTheory.cond]
    exact (integrable_exp_mul_gaussianReal t).restrict.smul_measure (ENNReal.inv_ne_top.2 h0)

/-- The exponential-integrability set of a truncated normal law is the whole line. -/
@[simp]
theorem integrableExpSet_id_truncatedNormalMeasure (m : ℝ) (v : ℝ≥0) (s : Set ℝ) :
    integrableExpSet id (truncatedNormalMeasure m v s) = univ := by
  ext t
  simpa [integrableExpSet] using integrable_exp_mul_truncatedNormalMeasure m v s t

/-- A truncated normal law has finite moments of every order. -/
theorem memLp_id_truncatedNormalMeasure (m : ℝ) (v : ℝ≥0) (s : Set ℝ) (p : ℝ≥0) :
    MemLp id p (truncatedNormalMeasure m v s) :=
  memLp_of_mem_interior_integrableExpSet (by simp) p

/-- The cumulant-generating function of the Gaussian law `N(m, v)` conditioned on a set `s` of
nonzero Gaussian mass. -/
theorem cgf_id_truncatedNormalMeasure (hs : gaussianReal m v s ≠ 0) (t : ℝ) :
    cgf id (truncatedNormalMeasure m v s) t =
      m * t + v * t ^ 2 / 2 + log ((gaussianReal (m + v * t) v).real s) -
        log ((gaussianReal m v).real s) := by
  -- Gaussian laws with the same variance have the same null sets, so `s` keeps nonzero mass
  -- under the shifted law.
  have hs' : gaussianReal (m + v * t) v s ≠ 0 := by
    rcases eq_or_ne v 0 with rfl | hv
    · simpa using hs
    · exact fun h => hs ((gaussianReal_absolutelyContinuous m hv).trans
        (gaussianReal_absolutelyContinuous' _ hv) h)
  have hZ : (gaussianReal m v).real s ≠ 0 := (measureReal_ne_zero_iff ..).2 hs
  have hZ' : (gaussianReal (m + v * t) v).real s ≠ 0 := (measureReal_ne_zero_iff ..).2 hs'
  rw [cgf, mgf_id_truncatedNormalMeasure, log_div (mul_ne_zero (exp_pos _).ne' hZ') hZ,
    log_mul (exp_pos _).ne' hZ', log_exp]

/-! ### Mean and variance of an interval truncation -/

/-- The derivative of the moment-generating function of an interval truncation. -/
private theorem hasDerivAt_mgf_id_truncatedNormalMeasure (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) (t : ℝ) :
    HasDerivAt (mgf id (truncatedNormalMeasure m v s))
      (exp (m * t + v * t ^ 2 / 2) * ((m + v * t) * (gaussianReal (m + v * t) v).real s +
        v * (gaussianPDFRealEReal (m + v * t) v l - gaussianPDFRealEReal (m + v * t) v r)) /
        (gaussianReal m v).real s) t := by
  have hmean : HasDerivAt (fun t : ℝ => m + v * t) v t := by
    simpa using ((hasDerivAt_id' t).const_mul (v : ℝ)).const_add m
  have hexp : HasDerivAt (fun t : ℝ => exp (m * t + v * t ^ 2 / 2))
      (exp (m * t + v * t ^ 2 / 2) * (m + v * t)) t := by
    convert ((((hasDerivAt_id' t).const_mul m).fun_add
      ((((hasDerivAt_id' t).fun_pow 2).const_mul (v : ℝ)).div_const 2))).exp using 1
    ring
  have hmass₀ := (hasDerivAt_measureReal_gaussianReal hv hlr.le hs₁ hs₂ (m + v * t)).comp t hmean
  have hmass : HasDerivAt (fun t : ℝ => (gaussianReal (m + v * t) v).real s) _ t := hmass₀
  rw [funext (mgf_id_truncatedNormalMeasure m v s)]
  convert (hexp.fun_mul hmass).div_const ((gaussianReal m v).real s) using 1
  ring

/-- The mean of a normal law of positive variance truncated to an interval with extended bounds
`l < r`: `m + v (g l - g r) / Z`, where `g` is the Gaussian density at the bounds (zero at an
infinite bound) and `Z` is the Gaussian mass of the interval. -/
theorem integral_id_truncatedNormalMeasure (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    ∫ x, x ∂truncatedNormalMeasure m v s =
      m + v * (gaussianPDFRealEReal m v l - gaussianPDFRealEReal m v r) /
        (gaussianReal m v).real s := by
  have hZ := (measureReal_gaussianReal_pos m hv hlr hs₁).ne'
  have h := deriv_mgf_zero (X := id) (μ := truncatedNormalMeasure m v s) (by simp)
  rw [(hasDerivAt_mgf_id_truncatedNormalMeasure hv hlr hs₁ hs₂ 0).deriv] at h
  simp only [id_eq, mul_zero, add_zero, zero_pow two_ne_zero, zero_div, exp_zero,
    one_mul] at h
  rw [← h]
  field_simp

/-- The variance of a normal law of positive variance truncated to an interval with extended
bounds `l < r`: `v (1 + ((l - m) g l - (r - m) g r) / Z - v ((g l - g r) / Z)²)`, where `g` is
the Gaussian density at the bounds (zero at an infinite bound, so that the corresponding product
vanishes) and `Z` is the Gaussian mass of the interval. -/
theorem variance_id_truncatedNormalMeasure (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Real.toEReal ⁻¹' Ioo l r ⊆ s) (hs₂ : s ⊆ Real.toEReal ⁻¹' Icc l r) :
    variance id (truncatedNormalMeasure m v s) =
      v * (1 + ((l.toReal - m) * gaussianPDFRealEReal m v l -
          (r.toReal - m) * gaussianPDFRealEReal m v r) / (gaussianReal m v).real s -
        v * ((gaussianPDFRealEReal m v l - gaussianPDFRealEReal m v r) /
          (gaussianReal m v).real s) ^ 2) := by
  have hv' : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.2 hv
  have hZ := (measureReal_gaussianReal_pos m hv hlr hs₁).ne'
  have := isProbabilityMeasure_truncatedNormalMeasure_of_lt (m := m) hv hlr hs₁
  -- The second moment is the second derivative of the mgf at `0`.
  have hmean : HasDerivAt (fun t : ℝ => m + v * t) v 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_mul (v : ℝ)).const_add m
  have hexp : HasDerivAt (fun t : ℝ => exp (m * t + v * t ^ 2 / 2)) m 0 := by
    convert ((((hasDerivAt_id' (0 : ℝ)).const_mul m).fun_add
      ((((hasDerivAt_id' (0 : ℝ)).fun_pow 2).const_mul (v : ℝ)).div_const 2))).exp using 1
    simp
  have hmass₀ := (hasDerivAt_measureReal_gaussianReal hv hlr.le hs₁ hs₂ (m + v * 0)).comp 0 hmean
  have hmass : HasDerivAt (fun t : ℝ => (gaussianReal (m + v * t) v).real s) _ 0 := hmass₀
  have hdens₀ := ((hasDerivAt_gaussianPDFRealEReal v l (m + v * 0)).sub
    (hasDerivAt_gaussianPDFRealEReal v r (m + v * 0))).comp 0 hmean
  have hdens : HasDerivAt (fun t : ℝ => gaussianPDFRealEReal (m + v * t) v l -
      gaussianPDFRealEReal (m + v * t) v r) _ 0 := hdens₀
  have hsecond : HasDerivAt (fun t : ℝ =>
      exp (m * t + v * t ^ 2 / 2) * ((m + v * t) * (gaussianReal (m + v * t) v).real s +
        v * (gaussianPDFRealEReal (m + v * t) v l - gaussianPDFRealEReal (m + v * t) v r)) /
        (gaussianReal m v).real s) _ 0 :=
    (hexp.fun_mul ((hmean.fun_mul hmass).fun_add (hdens.const_mul (v : ℝ)))).div_const
      ((gaussianReal m v).real s)
  have hderiv : deriv (mgf id (truncatedNormalMeasure m v s)) = fun t =>
      exp (m * t + v * t ^ 2 / 2) * ((m + v * t) * (gaussianReal (m + v * t) v).real s +
        v * (gaussianPDFRealEReal (m + v * t) v l - gaussianPDFRealEReal (m + v * t) v r)) /
        (gaussianReal m v).real s :=
    funext fun t => (hasDerivAt_mgf_id_truncatedNormalMeasure hv hlr hs₁ hs₂ t).deriv
  have h2 := iteratedDeriv_mgf_zero (X := id) (μ := truncatedNormalMeasure m v s) (by simp) 2
  rw [iteratedDeriv_succ, iteratedDeriv_one, hderiv] at h2
  rw [hsecond.deriv] at h2
  rw [variance_eq_sub (memLp_id_truncatedNormalMeasure m v s 2), ← h2]
  simp only [id_eq]
  rw [integral_id_truncatedNormalMeasure hv hlr hs₁ hs₂]
  simp only [mul_zero, add_zero, zero_pow two_ne_zero, zero_div, exp_zero, one_mul]
  field_simp
  ring

/-! ### Finite bounds in standardized form -/

/-- The moment-generating function of a normal law of positive variance truncated to an
interval with finite bounds `l ≤ r`: with `s₀ = √v`, `α = (l - m) / s₀`, `β = (r - m) / s₀` and
`Φ` the standard Gaussian cdf, it is
`exp (m t + v t² / 2) * (Φ (β - s₀ t) - Φ (α - s₀ t)) / (Φ β - Φ α)`. -/
theorem mgf_id_truncatedNormalMeasure_eq_cdf_zero_one {l r : ℝ} (hv : v ≠ 0) (hlr : l ≤ r)
    (hs₁ : Ioo l r ⊆ s) (hs₂ : s ⊆ Icc l r) (t : ℝ) :
    mgf id (truncatedNormalMeasure m v s) t =
      exp (m * t + v * t ^ 2 / 2) *
        (cdf (gaussianReal 0 1) ((r - m) / √(v : ℝ) - √(v : ℝ) * t) -
          cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ) - √(v : ℝ) * t)) /
        (cdf (gaussianReal 0 1) ((r - m) / √(v : ℝ)) -
          cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ))) := by
  have hv' : (0 : ℝ) < √(v : ℝ) := Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  have hvσ : (v : ℝ) = √(v : ℝ) ^ 2 := (Real.sq_sqrt (NNReal.coe_nonneg v)).symm
  have hshift (x : ℝ) : (x - (m + v * t)) / √(v : ℝ) = (x - m) / √(v : ℝ) - √(v : ℝ) * t := by
    generalize √(v : ℝ) = σ at hv' hvσ ⊢
    rw [hvσ]
    field_simp
    ring
  rw [mgf_id_truncatedNormalMeasure, measureReal_gaussianReal_eq_cdf_zero_one _ hv hlr hs₁ hs₂,
    measureReal_gaussianReal_eq_cdf_zero_one _ hv hlr hs₁ hs₂, hshift, hshift]

/-- The mean of a normal law of positive variance truncated to an interval with finite bounds
`l < r`: with `s₀ = √v`, `α = (l - m) / s₀`, `β = (r - m) / s₀`, `φ` and `Φ` the standard Gaussian
density and cdf, it is `m + s₀ (φ α - φ β) / (Φ β - Φ α)`. -/
theorem integral_id_truncatedNormalMeasure_eq_cdf_zero_one {l r : ℝ} (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Ioo l r ⊆ s) (hs₂ : s ⊆ Icc l r) :
    ∫ x, x ∂truncatedNormalMeasure m v s =
      m + √(v : ℝ) * (gaussianPDFReal 0 1 ((l - m) / √(v : ℝ)) -
          gaussianPDFReal 0 1 ((r - m) / √(v : ℝ))) /
        (cdf (gaussianReal 0 1) ((r - m) / √(v : ℝ)) -
          cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ))) := by
  have hv' : (0 : ℝ) < √(v : ℝ) := Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  rw [integral_id_truncatedNormalMeasure (l := l) (r := r) hv (EReal.coe_lt_coe_iff.2 hlr)
      (by rwa [EReal.preimage_coe_Ioo]) (by rwa [EReal.preimage_coe_Icc]),
    measureReal_gaussianReal_eq_cdf_zero_one _ hv hlr.le hs₁ hs₂]
  simp only [gaussianPDFRealEReal_coe, gaussianPDFReal_eq_gaussianPDFReal_zero_one m v]
  have hvσ : (v : ℝ) = √(v : ℝ) ^ 2 := (Real.sq_sqrt (NNReal.coe_nonneg v)).symm
  generalize √(v : ℝ) = σ at hv' hvσ ⊢
  rw [hvσ]
  field_simp

/-- The variance of a normal law of positive variance truncated to an interval with finite
bounds `l < r`: with `s₀ = √v`, `α = (l - m) / s₀`, `β = (r - m) / s₀`, `φ` and `Φ` the standard
Gaussian density and cdf, and `Z = Φ β - Φ α`, it is
`v (1 + (α φ α - β φ β) / Z - ((φ α - φ β) / Z)²)`. -/
theorem variance_id_truncatedNormalMeasure_eq_cdf_zero_one {l r : ℝ} (hv : v ≠ 0) (hlr : l < r)
    (hs₁ : Ioo l r ⊆ s) (hs₂ : s ⊆ Icc l r) :
    variance id (truncatedNormalMeasure m v s) =
      v * (1 + ((l - m) / √(v : ℝ) * gaussianPDFReal 0 1 ((l - m) / √(v : ℝ)) -
            (r - m) / √(v : ℝ) * gaussianPDFReal 0 1 ((r - m) / √(v : ℝ))) /
          (cdf (gaussianReal 0 1) ((r - m) / √(v : ℝ)) -
            cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ))) -
        ((gaussianPDFReal 0 1 ((l - m) / √(v : ℝ)) - gaussianPDFReal 0 1 ((r - m) / √(v : ℝ))) /
          (cdf (gaussianReal 0 1) ((r - m) / √(v : ℝ)) -
            cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ)))) ^ 2) := by
  have hv' : (0 : ℝ) < √(v : ℝ) := Real.sqrt_pos.2 (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv))
  have hZ : cdf (gaussianReal 0 1) ((r - m) / √(v : ℝ)) -
      cdf (gaussianReal 0 1) ((l - m) / √(v : ℝ)) ≠ 0 := by
    rw [← measureReal_gaussianReal_eq_cdf_zero_one _ hv hlr.le hs₁ hs₂]
    exact (measureReal_gaussianReal_pos m hv (EReal.coe_lt_coe_iff.2 hlr)
      (by rwa [EReal.preimage_coe_Ioo])).ne'
  rw [variance_id_truncatedNormalMeasure (l := l) (r := r) hv (EReal.coe_lt_coe_iff.2 hlr)
      (by rwa [EReal.preimage_coe_Ioo]) (by rwa [EReal.preimage_coe_Icc]),
    measureReal_gaussianReal_eq_cdf_zero_one _ hv hlr.le hs₁ hs₂]
  simp only [gaussianPDFRealEReal_coe, EReal.toReal_coe,
    gaussianPDFReal_eq_gaussianPDFReal_zero_one m v]
  have hvσ : (v : ℝ) = √(v : ℝ) ^ 2 := (Real.sq_sqrt (NNReal.coe_nonneg v)).symm
  generalize √(v : ℝ) = σ at hv' hvσ hZ ⊢
  rw [hvσ]
  field_simp

end TauCeti.Probability
