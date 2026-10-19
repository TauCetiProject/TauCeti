/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.MeasureTheory.Measure.WithDensity
import TauCeti.Probability.Density

/-!
# Elementary theory of the beta distribution

This file develops the elementary moment theory of Mathlib's beta distribution. For positive
shape parameters it computes mixed real-power moments, including their sharp integrability
criterion, and obtains the natural moments, mean, and variance as special cases. It also records
that the beta law is carried by `[0, 1]`, so every exponential moment exists.

## Main results

* `TauCeti.Probability.betaPDFReal_nonneg` — nonnegativity of the density;
* `TauCeti.Probability.integrable_betaMeasure_iff` and `TauCeti.Probability.integral_betaMeasure_eq`
  — integrability and
  integration against the beta law, transferred to the real density;
* `TauCeti.Probability.betaMeasure_eq_withDensity_restrict_Ioo` — the law is its density against
  Lebesgue
  measure on the open unit interval;
* `TauCeti.Probability.support_betaMeasure` — the exact topological support at positive shapes;
* `TauCeti.Probability.integrable_pow_betaMeasure` and
  `TauCeti.Probability.integrable_pow_abs_betaMeasure` — integrability of natural powers;
* `TauCeti.Probability.integrable_rpow_mul_one_sub_rpow_betaMeasure_iff` — the exact integrability
  criterion for mixed real powers;
* `TauCeti.Probability.integral_rpow_mul_one_sub_rpow_betaMeasure` — the mixed real-power moments
  as a quotient of beta values;
* `TauCeti.Probability.integral_pow_betaMeasure` — the natural raw moments as a quotient of Gamma
  values;
* `TauCeti.Probability.integral_id_betaMeasure` — the mean is `α / (α + β)`;
* `TauCeti.Probability.variance_id_betaMeasure` — the variance is
  `α * β / ((α + β) ^ 2 * (α + β + 1))`;
* `TauCeti.Probability.integrableExpSet_id_betaMeasure` — every exponential moment exists.

The moment calculation rewrites the density integral as Euler's beta integral — the real-valued
`TauCeti.integral_rpow_mul_one_sub_rpow`, proved in
`TauCeti/Analysis/SpecialFunctions/Beta.lean` — and then uses the Gamma quotient.

## References

* Tau Ceti roadmap, `StandardDistributions`, Layer 1, "Beta".
* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  2nd ed., Wiley, 1995.
-/

public section

namespace TauCeti.Probability

open _root_.MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory

/-- For positive shape parameters the beta density is nonnegative: it vanishes off the open unit
interval, and on it the normalizing constant `ProbabilityTheory.beta α β` is positive. -/
theorem betaPDFReal_nonneg {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (x : ℝ) :
    0 ≤ betaPDFReal α β x := by
  rw [betaPDFReal]
  split_ifs with hx
  · exact mul_nonneg (mul_nonneg (one_div_nonneg.mpr (beta_pos hα hβ).le)
      (Real.rpow_nonneg hx.1.le _))
      (Real.rpow_nonneg (sub_nonneg.mpr hx.2.le) _)
  · exact le_rfl

/-- The beta law presented by its real-valued density. -/
theorem betaMeasure_eq_withDensity_ofReal (α β : ℝ) :
    betaMeasure α β = volume.withDensity fun x ↦ ENNReal.ofReal (betaPDFReal α β x) :=
  (rfl)

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Integrability transfer.** A function is integrable against a beta law with positive shape
parameters exactly when its density-weighted version is Lebesgue integrable. -/
theorem integrable_betaMeasure_iff {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) {g : ℝ → E} :
    Integrable g (betaMeasure α β) ↔ Integrable fun x ↦ betaPDFReal α β x • g x := by
  rw [betaMeasure_eq_withDensity_ofReal]
  exact Probability.integrable_withDensity_ofReal_iff (measurable_betaPDFReal α β).aemeasurable
    (ae_of_all _ (betaPDFReal_nonneg hα hβ))

/-- **Integral transfer.** An integral against a beta law with positive shape parameters is the
density-weighted Lebesgue integral. -/
theorem integral_betaMeasure_eq {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (g : ℝ → E) :
    ∫ x, g x ∂betaMeasure α β = ∫ x, betaPDFReal α β x • g x := by
  rw [betaMeasure_eq_withDensity_ofReal]
  exact Probability.integral_withDensity_ofReal (measurable_betaPDFReal α β).aemeasurable
    (ae_of_all _ (betaPDFReal_nonneg hα hβ)) g

end Transfer

/-- A beta measure lies almost everywhere in the open unit interval, for all parameter values. -/
theorem ae_mem_Ioo_betaMeasure (α β : ℝ) :
    ∀ᵐ x ∂betaMeasure α β, x ∈ Set.Ioo (0 : ℝ) 1 := by
  have hpdf : betaPDF α β = ENNReal.ofReal ∘ betaPDFReal α β := rfl
  rw [betaMeasure, hpdf, ae_withDensity_iff
    (ENNReal.measurable_ofReal.comp (measurable_betaPDFReal α β))]
  filter_upwards [(volume : Measure ℝ).ae_ne 0, (volume : Measure ℝ).ae_ne 1]
    with x _ _ hpdf
  constructor
  · by_contra hx
    exact hpdf (betaPDF_eq_zero_of_nonpos (le_of_not_gt hx))
  · by_contra hx
    exact hpdf (betaPDF_eq_zero_of_one_le (le_of_not_gt hx))

/-- The beta law is its density against Lebesgue measure on the open unit interval: the density
vanishes off the closed interval, and the two endpoints are null. -/
theorem betaMeasure_eq_withDensity_restrict_Ioo (α β : ℝ) :
    betaMeasure α β = (volume.restrict (Ioo (0 : ℝ) 1)).withDensity (betaPDF α β) := by
  rw [← restrict_withDensity measurableSet_Ioo, ← betaMeasure,
    Measure.restrict_eq_self_of_ae_mem (ae_mem_Ioo_betaMeasure α β)]

/-- The beta distribution is carried by the unit interval. -/
theorem ae_mem_Icc_betaMeasure (α β : ℝ) :
    ∀ᵐ x ∂betaMeasure α β, x ∈ Set.Icc (0 : ℝ) 1 := by
  filter_upwards [ae_mem_Ioo_betaMeasure α β] with x hx
  exact ⟨hx.1.le, hx.2.le⟩

/-- At positive shape parameters, the topological support of a beta law is the closed unit
interval. -/
@[simp]
theorem support_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    (betaMeasure α β).support = Icc 0 1 := by
  have hsupp : Function.support (betaPDF α β) = Ioo 0 1 := by
    ext x
    rw [Function.mem_support]
    constructor
    · intro hx
      constructor
      · by_contra h
        exact hx (betaPDF_eq_zero_of_nonpos (le_of_not_gt h))
      · by_contra h
        exact hx (betaPDF_eq_zero_of_one_le (le_of_not_gt h))
    · intro hx
      rw [betaPDF, ENNReal.ofReal_ne_zero_iff]
      exact betaPDFReal_pos hx.1 hx.2 hα hβ
  rw [betaMeasure,
    Measure.support_withDensity_eq_closure (f := betaPDF α β)
      (measurable_betaPDFReal α β).ennreal_ofReal isOpen_Ioo hsupp,
    closure_Ioo zero_ne_one]

private lemma betaPDFReal_mul_rpow_mul_one_sub_rpow {α β q s x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    betaPDFReal α β x * (x ^ q * (1 - x) ^ s) =
      (1 / beta α β) * (x ^ (α + q - 1) * (1 - x) ^ (β + s - 1)) := by
  rw [betaPDFReal, ite_eq_left ⟨hx.1, hx.2⟩]
  calc
    (1 / beta α β) * x ^ (α - 1) * (1 - x) ^ (β - 1) *
          (x ^ q * (1 - x) ^ s) =
        (1 / beta α β) *
          ((x ^ (α - 1) * x ^ q) * ((1 - x) ^ (β - 1) * (1 - x) ^ s)) := by ring
    _ = (1 / beta α β) * (x ^ (α + q - 1) * (1 - x) ^ (β + s - 1)) := by
      rw [← Real.rpow_add hx.1, ← Real.rpow_add (sub_pos.mpr hx.2)]
      congr 3 <;> ring

private lemma betaPDFReal_mul_rpow_mul_one_sub_rpow_eq_indicator (α β q s : ℝ) :
    (fun x : ℝ => betaPDFReal α β x * (x ^ q * (1 - x) ^ s)) =
      (Ioo (0 : ℝ) 1).indicator fun x =>
        (1 / beta α β) * (x ^ (α + q - 1) * (1 - x) ^ (β + s - 1)) := by
  funext x
  by_cases hx : x ∈ Ioo (0 : ℝ) 1
  · rw [indicator_of_mem hx, betaPDFReal_mul_rpow_mul_one_sub_rpow hx]
  · rw [indicator_of_notMem hx, betaPDFReal]
    split_ifs with hx'
    · exact (hx hx').elim
    · simp

/-- Mixed real powers of a beta variable are integrable exactly when their exponents remain above
the two endpoint singularity thresholds. -/
@[simp]
theorem integrable_rpow_mul_one_sub_rpow_betaMeasure_iff {α β q s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) :
    Integrable (fun x : ℝ => x ^ q * (1 - x) ^ s) (betaMeasure α β) ↔
      0 < α + q ∧ 0 < β + s := by
  rw [integrable_betaMeasure_iff hα hβ]
  simp_rw [smul_eq_mul, betaPDFReal_mul_rpow_mul_one_sub_rpow_eq_indicator,
    integrable_indicator_iff measurableSet_Ioo, IntegrableOn]
  rw [integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (one_div_ne_zero (beta_pos hα hβ).ne'))]
  exact TauCeti.integrableOn_rpow_mul_one_sub_rpow_iff

/-- The mixed real-power moment of a beta variable is a quotient of beta values. -/
@[simp]
theorem integral_rpow_mul_one_sub_rpow_betaMeasure {α β q s : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hq : 0 < α + q) (hs : 0 < β + s) :
    ∫ x, x ^ q * (1 - x) ^ s ∂betaMeasure α β =
      beta (α + q) (β + s) / beta α β := by
  rw [integral_betaMeasure_eq hα hβ]
  simp_rw [smul_eq_mul]
  rw [betaPDFReal_mul_rpow_mul_one_sub_rpow_eq_indicator, integral_indicator measurableSet_Ioo]
  calc
    ∫ x in Ioo (0 : ℝ) 1,
        (1 / beta α β) * (x ^ (α + q - 1) * (1 - x) ^ (β + s - 1)) =
        (1 / beta α β) * beta (α + q) (β + s) := by
      rw [integral_const_mul, ← integral_Ioc_eq_integral_Ioo,
        ← intervalIntegral.integral_of_le zero_le_one,
        TauCeti.integral_rpow_mul_one_sub_rpow hq hs]
    _ = beta (α + q) (β + s) / beta α β := by ring

/-- The `n`th raw moment of a beta distribution with positive shape parameters. -/
@[simp]
theorem integral_pow_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    ∫ x, x ^ n ∂betaMeasure α β =
      Real.Gamma (α + n) * Real.Gamma (α + β) /
        (Real.Gamma α * Real.Gamma (α + β + n)) := by
  have hαn : 0 < α + (n : ℝ) := add_pos_of_pos_of_nonneg hα (Nat.cast_nonneg n)
  calc
    ∫ x, x ^ n ∂betaMeasure α β =
        ∫ x, x ^ (n : ℝ) * (1 - x) ^ (0 : ℝ) ∂betaMeasure α β := by
      congr with x
      rw [Real.rpow_natCast, Real.rpow_zero, mul_one]
    _ = beta (α + n) β / beta α β := by
      have hβ0 : 0 < β + (0 : ℝ) := by simpa using hβ
      simpa using integral_rpow_mul_one_sub_rpow_betaMeasure (q := (n : ℝ)) (s := 0)
        hα hβ hαn hβ0
    _ = Real.Gamma (α + n) * Real.Gamma (α + β) /
          (Real.Gamma α * Real.Gamma (α + β + n)) := by
      rw [beta, beta]
      field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα),
        ne_of_gt (Real.Gamma_pos_of_pos hβ),
        ne_of_gt (Real.Gamma_pos_of_pos hαn),
        ne_of_gt (Real.Gamma_pos_of_pos (add_pos hα hβ)),
        ne_of_gt (Real.Gamma_pos_of_pos (add_pos hαn hβ))]
      ring_nf

/-- `Real.Gamma` two steps up: `Γ (x + 2) = (x + 1) * x * Γ x`. The second raw moment of a beta
law evaluates `Real.Gamma` at `α + 2` and at `α + β + 2`, and this is the shape in which those two
values are compared with `Real.Gamma α` and `Real.Gamma (α + β)`. -/
private lemma Gamma_add_two {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 2) = (x + 1) * x * Real.Gamma x := by
  have hx2 : x + 2 = x + 1 + 1 := by ring
  rw [hx2, Real.Gamma_add_one (by linarith : (0 : ℝ) < x + 1).ne',
    Real.Gamma_add_one hx.ne']
  ring

/-- The mean of a beta distribution with positive shape parameters. -/
@[simp]
theorem integral_id_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ∫ x, x ∂betaMeasure α β = α / (α + β) := by
  have hmoment := integral_pow_betaMeasure hα hβ 1
  simp only [pow_one, Nat.cast_one] at hmoment
  rw [hmoment, Real.Gamma_add_one hα.ne', Real.Gamma_add_one (add_pos hα hβ).ne']
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα),
    ne_of_gt (Real.Gamma_pos_of_pos (add_pos hα hβ)), ne_of_gt (add_pos hα hβ)]

/-- The variance of a beta distribution with positive shape parameters. -/
@[simp]
theorem variance_id_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    variance id (betaMeasure α β) =
      α * β / ((α + β) ^ 2 * (α + β + 1)) := by
  let _ : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  have hmem : MemLp id 2 (betaMeasure α β) :=
    memLp_of_bounded (ae_mem_Icc_betaMeasure α β) measurable_id.aestronglyMeasurable 2
  rw [variance_eq_sub hmem]
  simp only [Pi.pow_apply, id_eq, integral_pow_betaMeasure hα hβ 2,
    integral_id_betaMeasure hα hβ]
  norm_num only [Nat.cast_ofNat]
  rw [Gamma_add_two hα, Gamma_add_two (add_pos hα hβ)]
  field_simp [ne_of_gt (Real.Gamma_pos_of_pos hα),
    ne_of_gt (Real.Gamma_pos_of_pos (add_pos hα hβ)),
    ne_of_gt (add_pos hα hβ)]
  ring_nf

/-- Every exponential moment of a beta distribution with positive shape parameters exists. -/
@[simp]
theorem integrableExpSet_id_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    integrableExpSet id (betaMeasure α β) = Set.univ := by
  let _ : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  ext t
  simp only [Set.mem_univ, iff_true, integrableExpSet, Set.mem_ofPred_eq, id_eq]
  exact integrable_exp_mul_of_mem_Icc measurable_id.aemeasurable
    (ae_mem_Icc_betaMeasure α β)

/-- Every natural power is integrable against a beta law with positive shape parameters. -/
theorem integrable_pow_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n) (betaMeasure α β) := by
  apply integrable_pow_of_mem_interior_integrableExpSet (X := id) _ n
  simp only [integrableExpSet_id_betaMeasure hα hβ, interior_univ, mem_univ]

/-- Every natural power of the absolute value is integrable against a beta law with positive
shape parameters. -/
theorem integrable_pow_abs_betaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) (n : ℕ) :
    Integrable (fun x : ℝ ↦ |x| ^ n) (betaMeasure α β) := by
  apply integrable_pow_abs_of_mem_interior_integrableExpSet (X := id) _ n
  simp only [integrableExpSet_id_betaMeasure hα hβ, interior_univ, mem_univ]

end TauCeti.Probability
