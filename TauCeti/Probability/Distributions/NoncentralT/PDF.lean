/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.NoncentralT.Basic
import TauCeti.MeasureTheory.Measure.Mixture.Basic
import TauCeti.Probability.Density

/-!
# Densities of noncentral t laws

Given that the chi-squared factor of a noncentral t variable with `ν` degrees of freedom takes
the value `v`, the variable is Gaussian with density `√(v / ν) φ(x √(v / ν) - δ)`, where `φ` is
the standard Gaussian density. Integrating these densities against the chi-squared law gives the
density of the noncentral t law. It is positive everywhere for positive degrees, and it is zero
for nonpositive degrees, where the law is the zero measure.

The density is kept as this mixture integral; no hypergeometric closed form is developed.

## Main definitions

* `TauCeti.Probability.noncentralTPDFReal` — the real density, as a chi-squared mixture integral.
* `TauCeti.Probability.noncentralTPDF` — its extended nonnegative companion.

## Main results

* `TauCeti.Probability.noncentralTPDFReal_pos` — positivity of the density.
* `TauCeti.Probability.noncentralTMeasure_eq_withDensity` — the law is Lebesgue measure with the
  density.
* `TauCeti.Probability.rnDeriv_noncentralTMeasure` — the Radon–Nikodym derivative.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 31.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ν δ : ℝ}

/-- The real density of the noncentral t law with `ν` degrees of freedom and noncentrality `δ`:
the integral of `√(v / ν) φ(x √(v / ν) - δ)` against the chi-squared law with `ν` degrees of
freedom, where `φ` is the standard Gaussian density. It is zero for `ν ≤ 0`. -/
def noncentralTPDFReal (ν δ x : ℝ) : ℝ :=
  ∫ v, √(v / ν) * gaussianPDFReal 0 1 (x * √(v / ν) - δ) ∂chiSquaredMeasure ν

/-- The extended nonnegative density of the noncentral t law. -/
def noncentralTPDF (ν δ x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (noncentralTPDFReal ν δ x)

/-- The real density is the chi-squared mixture integral of the conditional Gaussian densities. -/
theorem noncentralTPDFReal_def (ν δ x : ℝ) :
    noncentralTPDFReal ν δ x =
      ∫ v, √(v / ν) * gaussianPDFReal 0 1 (x * √(v / ν) - δ) ∂chiSquaredMeasure ν := (rfl)

/-- The extended density is obtained from its nonnegative real companion. -/
theorem noncentralTPDF_eq_ofReal (ν δ x : ℝ) :
    noncentralTPDF ν δ x = ENNReal.ofReal (noncentralTPDFReal ν δ x) := (rfl)

/-- The real density vanishes for nonpositive degrees. -/
@[simp]
theorem noncentralTPDFReal_of_nonpos (hν : ν ≤ 0) (δ x : ℝ) : noncentralTPDFReal ν δ x = 0 := by
  rcases hν.lt_or_eq with hν | rfl
  · simp [noncentralTPDFReal_def, chiSquaredMeasure_of_neg hν]
  · simp [noncentralTPDFReal_def]

/-- The extended density vanishes for nonpositive degrees. -/
@[simp]
theorem noncentralTPDF_of_nonpos (hν : ν ≤ 0) (δ x : ℝ) : noncentralTPDF ν δ x = 0 := by
  simp [noncentralTPDF_eq_ofReal, hν]

/-- The conditional Gaussian densities are integrable against the chi-squared law: they are
bounded by a multiple of `√(v / ν)`, which has finite expectation. -/
private theorem integrable_noncentralT_integrand (hν : 0 < ν) (δ x : ℝ) :
    Integrable (fun v ↦ √(v / ν) * gaussianPDFReal 0 1 (x * √(v / ν) - δ))
      (chiSquaredMeasure ν) := by
  have hsqrt : Integrable (fun v ↦ √(v / ν)) (chiSquaredMeasure ν) := by
    rw [chiSquaredMeasure_eq_gammaMeasure hν]
    have h := (integrable_rpow_gammaMeasure_iff (a := ν / 2) (r := 1 / 2) (by positivity)
      (by norm_num) (1 / 2)).2 (by linarith)
    refine (h.div_const √ν).congr (ae_of_all _ fun v ↦ ?_)
    simp [sqrt_div' _ hν.le, sqrt_eq_rpow]
  refine (hsqrt.mul_const (√(2 * π))⁻¹).mono' (by fun_prop) (ae_of_all _ fun v ↦ ?_)
  rw [norm_mul, norm_of_nonneg (sqrt_nonneg _), norm_of_nonneg (gaussianPDFReal_nonneg _ _ _)]
  refine mul_le_mul_of_nonneg_left ?_ (sqrt_nonneg _)
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one]
  refine mul_le_of_le_one_right (by positivity) (exp_le_one_iff.2 ?_)
  rw [neg_div]
  exact neg_nonpos.2 (by positivity)

/-- The real density is nonnegative. -/
theorem noncentralTPDFReal_nonneg (ν δ x : ℝ) : 0 ≤ noncentralTPDFReal ν δ x :=
  integral_nonneg fun _ ↦ mul_nonneg (sqrt_nonneg _) (gaussianPDFReal_nonneg _ _ _)

/-- For positive degrees, the real density is positive everywhere. -/
theorem noncentralTPDFReal_pos (hν : 0 < ν) (δ x : ℝ) : 0 < noncentralTPDFReal ν δ x := by
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  rw [noncentralTPDFReal_def, integral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun _ ↦ mul_nonneg (sqrt_nonneg _) (gaussianPDFReal_nonneg _ _ _))
    (integrable_noncentralT_integrand hν δ x)]
  refine pos_iff_ne_zero.2 fun h ↦ ?_
  obtain ⟨v, hv, hsupp⟩ := ((measure_eq_zero_iff_ae_notMem.1 h).and
    (ae_pos_sqrt_div_chiSquaredMeasure hν)).exists
  exact hv (mul_pos hsupp (gaussianPDFReal_pos _ _ _ one_ne_zero)).ne'

/-- The real density is measurable. -/
@[fun_prop]
theorem measurable_noncentralTPDFReal (ν δ : ℝ) : Measurable (noncentralTPDFReal ν δ) := by
  rcases le_or_gt ν 0 with hν | hν
  · rw [funext (noncentralTPDFReal_of_nonpos hν δ)]
    exact measurable_const
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  have h : StronglyMeasurable (Function.uncurry fun (x v : ℝ) ↦
      √(v / ν) * gaussianPDFReal 0 1 (x * √(v / ν) - δ)) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ ↦
      √(p.2 / ν) * gaussianPDFReal 0 1 (p.1 * √(p.2 / ν) - δ)).stronglyMeasurable
  exact h.integral_prod_right.measurable

/-- The extended density is measurable. -/
@[fun_prop]
theorem measurable_noncentralTPDF (ν δ : ℝ) : Measurable (noncentralTPDF ν δ) :=
  (measurable_noncentralTPDFReal ν δ).ennreal_ofReal

/-- The noncentral t law is Lebesgue measure with density `noncentralTPDF ν δ`, for every
choice of parameters. -/
theorem noncentralTMeasure_eq_withDensity (ν δ : ℝ) :
    noncentralTMeasure ν δ = volume.withDensity (noncentralTPDF ν δ) := by
  rcases le_or_gt ν 0 with hν | hν
  · have hzero : noncentralTPDF ν δ = 0 := funext (noncentralTPDF_of_nonpos hν δ)
    rw [noncentralTMeasure_of_nonpos hν, hzero, withDensity_zero]
  let _ := isProbabilityMeasure_chiSquaredMeasure hν.le
  rw [noncentralTMeasure_eq_bind hν, Measure.bind_eq_withDensity_of_ae_eq _ volume
    (f := fun v x ↦ ENNReal.ofReal (√(v / ν) * gaussianPDFReal 0 1 (x * √(v / ν) - δ)))
    (by fun_prop) ?_]
  · congr 1
    funext x
    rw [noncentralTPDF_eq_ofReal, noncentralTPDFReal_def,
      ofReal_integral_eq_lintegral_ofReal (integrable_noncentralT_integrand hν δ x)
        (ae_of_all _ fun _ ↦ mul_nonneg (sqrt_nonneg _) (gaussianPDFReal_nonneg _ _ _))]
  · -- Dividing the Gaussian factor by `c = √(v / ν) > 0` gives density `c φ(x c - δ)`.
    filter_upwards [ae_pos_sqrt_div_chiSquaredMeasure hν] with v hv
    generalize √(v / ν) = c at hv ⊢
    rw [gaussianReal_map_div_const, gaussianReal_of_var_ne_zero, gaussianPDF_def]
    swap
    · rw [ne_eq, ← NNReal.coe_eq_zero]
      simp [hv.ne']
    congr 1
    funext x
    rw [gaussianPDFReal_sub, zero_add, mul_comm x c, gaussianPDFReal_mul hv.ne',
      abs_of_pos (inv_pos.2 hv), ← mul_assoc, mul_inv_cancel₀ hv.ne', one_mul]
    congr 2
    · rw [div_eq_inv_mul]
    · ext
      simp

/-- For positive degrees, the extended density integrates to one. -/
theorem lintegral_noncentralTPDF_eq_one (hν : 0 < ν) (δ : ℝ) :
    ∫⁻ x, noncentralTPDF ν δ x = 1 := by
  let _ := isProbabilityMeasure_noncentralTMeasure hν δ
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    ← noncentralTMeasure_eq_withDensity, measure_univ]

/-- For positive degrees, the real density integrates to one. -/
theorem integral_noncentralTPDFReal_eq_one (hν : 0 < ν) (δ : ℝ) :
    ∫ x, noncentralTPDFReal ν δ x = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (noncentralTPDFReal_nonneg ν δ))
    (measurable_noncentralTPDFReal ν δ).aestronglyMeasurable]
  simp_rw [← noncentralTPDF_eq_ofReal]
  rw [lintegral_noncentralTPDF_eq_one hν, ENNReal.toReal_one]

/-- The Radon–Nikodym derivative of the noncentral t law with respect to Lebesgue measure is its
density. -/
theorem rnDeriv_noncentralTMeasure (ν δ : ℝ) :
    (noncentralTMeasure ν δ).rnDeriv volume =ᵐ[volume] noncentralTPDF ν δ := by
  rw [noncentralTMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ (measurable_noncentralTPDF ν δ)

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- The density of a variable with a noncentral t law agrees almost everywhere with
`noncentralTPDF ν δ`. -/
theorem pdf_eq_noncentralTPDF_of_hasLaw_noncentralTMeasure
    (hX : HasLaw X (noncentralTMeasure ν δ) P) :
    pdf X P volume =ᵐ[volume] noncentralTPDF ν δ := by
  apply pdf_eq_of_hasLaw_withDensity (measurable_noncentralTPDF ν δ).aemeasurable
  rwa [← noncentralTMeasure_eq_withDensity]

end TauCeti.Probability
