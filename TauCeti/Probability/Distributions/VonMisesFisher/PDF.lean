/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.VonMisesFisher.Basic
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity

/-!
# Densities of sphere-valued von Mises–Fisher laws

The natural-parameter and direction/concentration densities are taken relative to
`uniformSphereMeasure E`, not ambient Lebesgue measure. Their normalized exponential form works
in every positive dimension, including the two-point sphere in dimension one. Negative
concentration gives density zero; at zero concentration the density is one. In dimension at
least two, the positive-concentration normalizer can also be expressed using the modified
Bessel function.

This module supplies positivity, normalization, and joint measurability of the densities
introduced in `VonMisesFisher.Basic`. That module also supplies their Radon–Nikodym derivatives
and the density interfaces for sphere-valued random variables.

## References

* K. V. Mardia, P. E. Jupp, *Directional Statistics*, Wiley (2000), §9.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Metric Real Set
open scoped ENNReal RealInnerProductSpace

namespace TauCeti.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The natural-parameter real density is positive at every sphere point. -/
theorem vonMisesFisherNaturalPDFReal_pos (η : E) (x : sphere (0 : E) 1) :
    0 < vonMisesFisherNaturalPDFReal η x := by
  have : Nontrivial E := ⟨⟨x, 0, ne_zero_of_mem_sphere one_ne_zero x⟩⟩
  rw [vonMisesFisherNaturalPDFReal_def]
  exact div_pos (exp_pos _) (integral_exp_inner_uniformSphereMeasure_pos _)

/-- Zero natural parameter gives real density one at every sphere point. -/
@[simp]
theorem vonMisesFisherNaturalPDFReal_zero (x : sphere (0 : E) 1) :
    vonMisesFisherNaturalPDFReal 0 x = 1 := by
  have : Nontrivial E := ⟨⟨x, 0, ne_zero_of_mem_sphere one_ne_zero x⟩⟩
  simp [vonMisesFisherNaturalPDFReal_def]

/-- Zero natural parameter gives extended-real density one. -/
@[simp]
theorem vonMisesFisherNaturalPDF_zero (x : sphere (0 : E) 1) :
    vonMisesFisherNaturalPDF 0 x = 1 := by
  simp [vonMisesFisherNaturalPDF_def]

/-- The natural-parameter real density is jointly measurable in its parameter and sphere point. -/
@[fun_prop]
theorem measurable_uncurry_vonMisesFisherNaturalPDFReal :
    Measurable fun p : E × sphere (0 : E) 1 ↦ vonMisesFisherNaturalPDFReal p.1 p.2 := by
  have hZ : Measurable fun η : E ↦
      ∫ y : sphere (0 : E) 1, exp ⟪η, (y : E)⟫ ∂uniformSphereMeasure E :=
    (by fun_prop : Measurable fun p : E × sphere (0 : E) 1 ↦
      exp ⟪p.1, (p.2 : E)⟫).stronglyMeasurable.integral_prod_right'.measurable
  simp_rw [vonMisesFisherNaturalPDFReal_def]
  exact Measurable.div (by fun_prop) (hZ.comp measurable_fst)

/-- The natural-parameter extended-real density is jointly measurable. -/
@[fun_prop]
theorem measurable_uncurry_vonMisesFisherNaturalPDF :
    Measurable fun p : E × sphere (0 : E) 1 ↦ vonMisesFisherNaturalPDF p.1 p.2 := by
  simp_rw [vonMisesFisherNaturalPDF_def]
  exact measurable_uncurry_vonMisesFisherNaturalPDFReal.ennreal_ofReal

/-- The natural-parameter real density is measurable in the sphere point. -/
@[fun_prop]
theorem measurable_vonMisesFisherNaturalPDFReal (η : E) :
    Measurable (vonMisesFisherNaturalPDFReal η) :=
  measurable_uncurry_vonMisesFisherNaturalPDFReal.comp (measurable_const.prodMk measurable_id)

/-- The natural-parameter density has total mass one in positive dimension. -/
theorem lintegral_vonMisesFisherNaturalPDF [Nontrivial E] (η : E) :
    ∫⁻ x, vonMisesFisherNaturalPDF η x ∂uniformSphereMeasure E = 1 := by
  simpa only [vonMisesFisherNaturalMeasure_eq_withDensity,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using
    measure_univ (μ := vonMisesFisherNaturalMeasure η)

/-- The natural-parameter real density is integrable, including on the empty sphere. -/
theorem integrable_vonMisesFisherNaturalPDFReal (η : E) :
    Integrable (vonMisesFisherNaturalPDFReal η) (uniformSphereMeasure E) :=
  MeasureTheory.integrable_of_eq_withDensity
    (by simpa only [vonMisesFisherNaturalPDF_def] using
      vonMisesFisherNaturalMeasure_eq_withDensity η)
    (measurable_vonMisesFisherNaturalPDFReal η).aemeasurable
    (ae_of_all _ (vonMisesFisherNaturalPDFReal_nonneg η))

/-- The natural-parameter real density integrates to one in positive dimension. -/
theorem integral_vonMisesFisherNaturalPDFReal [Nontrivial E] (η : E) :
    ∫ x, vonMisesFisherNaturalPDFReal η x ∂uniformSphereMeasure E = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (vonMisesFisherNaturalPDFReal_nonneg η))
    (measurable_vonMisesFisherNaturalPDFReal η).aestronglyMeasurable]
  simpa only [vonMisesFisherNaturalPDF_def, ENNReal.toReal_one] using
    congrArg ENNReal.toReal (lintegral_vonMisesFisherNaturalPDF η)

/-- At nonnegative concentration, the real density is the normalized exponential weight. -/
@[simp]
theorem vonMisesFisherPDFReal_eq_exp_div (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (x : sphere (0 : E) 1) :
    vonMisesFisherPDFReal m κ x = exp (κ * ⟪(m : E), (x : E)⟫) /
      ∫ y : sphere (0 : E) 1, exp (κ * ⟪(m : E), (y : E)⟫) ∂uniformSphereMeasure E := by
  rw [vonMisesFisherPDFReal_of_nonneg m hκ, vonMisesFisherNaturalPDFReal_def]
  simp only [real_inner_smul_left]

/-- At nonnegative concentration, the extended-real density is the normalized exponential. -/
@[simp]
theorem vonMisesFisherPDF_eq_ofReal_exp_div (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (x : sphere (0 : E) 1) :
    vonMisesFisherPDF m κ x = ENNReal.ofReal (exp (κ * ⟪(m : E), (x : E)⟫) /
      ∫ y : sphere (0 : E) 1, exp (κ * ⟪(m : E), (y : E)⟫) ∂uniformSphereMeasure E) := by
  simp only [vonMisesFisherPDF_def, vonMisesFisherPDFReal_eq_exp_div m hκ]

/-- The real density is strictly positive at every sphere point for valid concentration. -/
theorem vonMisesFisherPDFReal_pos (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (x : sphere (0 : E) 1) : 0 < vonMisesFisherPDFReal m κ x := by
  rw [vonMisesFisherPDFReal_of_nonneg m hκ]
  exact vonMisesFisherNaturalPDFReal_pos (κ • (m : E)) x

/-- At zero concentration the density relative to uniform sphere probability is one. -/
@[simp high]
theorem vonMisesFisherPDFReal_zero (m x : sphere (0 : E) 1) :
    vonMisesFisherPDFReal m 0 x = 1 := by
  rw [vonMisesFisherPDFReal_of_nonneg m le_rfl, zero_smul, vonMisesFisherNaturalPDFReal_zero]

/-- At zero concentration the extended-real density is one. -/
@[simp high]
theorem vonMisesFisherPDF_zero (m x : sphere (0 : E) 1) : vonMisesFisherPDF m 0 x = 1 := by
  simp only [vonMisesFisherPDF_def, vonMisesFisherPDFReal_zero, ENNReal.ofReal_one]

/-- The real density is jointly measurable in the direction, concentration, and sphere point. -/
@[fun_prop]
theorem measurable_uncurry_vonMisesFisherPDFReal :
    Measurable fun p : (sphere (0 : E) 1 × ℝ) × sphere (0 : E) 1 ↦
      vonMisesFisherPDFReal p.1.1 p.1.2 p.2 := by
  simp_rw [vonMisesFisherPDFReal_def]
  apply Measurable.ite (measurableSet_le measurable_const measurable_fst.snd)
  · exact measurable_uncurry_vonMisesFisherNaturalPDFReal.comp
      ((measurable_fst.snd.smul (measurable_subtypeVal.comp measurable_fst.fst)).prodMk
        measurable_snd)
  · exact measurable_const

/-- The extended-real density is jointly measurable in all its arguments. -/
@[fun_prop]
theorem measurable_uncurry_vonMisesFisherPDF :
    Measurable fun p : (sphere (0 : E) 1 × ℝ) × sphere (0 : E) 1 ↦
      vonMisesFisherPDF p.1.1 p.1.2 p.2 := by
  simpa only [vonMisesFisherPDF_def] using
    measurable_uncurry_vonMisesFisherPDFReal.ennreal_ofReal

/-- The real density is measurable as a function of the sphere point. -/
@[fun_prop]
theorem measurable_vonMisesFisherPDFReal (m : sphere (0 : E) 1) (κ : ℝ) :
    Measurable (vonMisesFisherPDFReal m κ) :=
  measurable_uncurry_vonMisesFisherPDFReal.comp
    ((measurable_const : Measurable fun _ : sphere (0 : E) 1 ↦ (m, κ)).prodMk measurable_id)

/-- The density has total mass one at every valid concentration. -/
theorem lintegral_vonMisesFisherPDF (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∫⁻ x, vonMisesFisherPDF m κ x ∂uniformSphereMeasure E = 1 := by
  have : Nontrivial E := ⟨⟨m, 0, ne_zero_of_mem_sphere one_ne_zero m⟩⟩
  rw [vonMisesFisherPDF_of_nonneg m hκ]
  exact lintegral_vonMisesFisherNaturalPDF (κ • (m : E))

/-- The real density is integrable for every concentration, including negative concentrations
where it vanishes. -/
theorem integrable_vonMisesFisherPDFReal (m : sphere (0 : E) 1) (κ : ℝ) :
    Integrable (vonMisesFisherPDFReal m κ) (uniformSphereMeasure E) := by
  by_cases hκ : 0 ≤ κ
  · rw [vonMisesFisherPDFReal_of_nonneg m hκ]
    exact integrable_vonMisesFisherNaturalPDFReal (κ • (m : E))
  · rw [vonMisesFisherPDFReal_of_neg m (lt_of_not_ge hκ)]
    exact integrable_zero _ _ _

/-- The real density integrates to one at valid concentrations. -/
theorem integral_vonMisesFisherPDFReal (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∫ x, vonMisesFisherPDFReal m κ x ∂uniformSphereMeasure E = 1 := by
  have : Nontrivial E := ⟨⟨m, 0, ne_zero_of_mem_sphere one_ne_zero m⟩⟩
  rw [vonMisesFisherPDFReal_of_nonneg m hκ]
  exact integral_vonMisesFisherNaturalPDFReal (κ • (m : E))

end TauCeti.Probability
