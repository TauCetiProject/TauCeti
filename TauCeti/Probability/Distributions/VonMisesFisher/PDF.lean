/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.VonMisesFisher.Basic
public import TauCeti.Probability.Density
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Densities of sphere-valued von Mises–Fisher laws

The direction/concentration density is taken relative to `uniformSphereMeasure E`, not
ambient Lebesgue measure. Its normalized exponential form works in every positive dimension,
including the two-point sphere in dimension one. Negative concentration gives density zero;
at zero concentration the density is one. In dimension at least two, the positive-concentration
normalizer can also be expressed using the modified Bessel function.

This module supplies named real and extended-real densities, their normalization and
Radon–Nikodym derivative, and the density interfaces for sphere-valued random variables.
The density is jointly measurable in the direction, concentration, and sphere point.

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

/-- The real von Mises–Fisher density relative to uniform sphere probability, zero at negative
concentration. The direction is a unit vector, so the empty sphere has no parameters. -/
def vonMisesFisherPDFReal (m : sphere (0 : E) 1) (κ : ℝ) (x : sphere (0 : E) 1) : ℝ :=
  if 0 ≤ κ then
    exp ⟪κ • (m : E), (x : E)⟫ /
      ∫ y : sphere (0 : E) 1, exp ⟪κ • (m : E), (y : E)⟫ ∂uniformSphereMeasure E
  else 0

/-- The extended-real von Mises–Fisher density relative to uniform sphere probability. -/
def vonMisesFisherPDF (m : sphere (0 : E) 1) (κ : ℝ) (x : sphere (0 : E) 1) : ℝ≥0∞ :=
  ENNReal.ofReal (vonMisesFisherPDFReal m κ x)

/-- The extended-real density is the nonnegative lift of the real density. -/
theorem vonMisesFisherPDF_eq_ofReal (m : sphere (0 : E) 1) (κ : ℝ)
    (x : sphere (0 : E) 1) :
    vonMisesFisherPDF m κ x = ENNReal.ofReal (vonMisesFisherPDFReal m κ x) := (rfl)

/-- At nonnegative concentration, the density is the normalized exponential weight. -/
theorem vonMisesFisherPDFReal_of_nonneg (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (x : sphere (0 : E) 1) :
    vonMisesFisherPDFReal m κ x = exp (κ * ⟪(m : E), (x : E)⟫) /
      ∫ y : sphere (0 : E) 1, exp (κ * ⟪(m : E), (y : E)⟫) ∂uniformSphereMeasure E := by
  simp only [vonMisesFisherPDFReal, ite_eq_left hκ, real_inner_smul_left]

/-- Negative concentration gives zero real density. -/
@[simp]
theorem vonMisesFisherPDFReal_of_neg (m : sphere (0 : E) 1) {κ : ℝ} (hκ : κ < 0)
    (x : sphere (0 : E) 1) : vonMisesFisherPDFReal m κ x = 0 := by
  simp [vonMisesFisherPDFReal, hκ.not_ge]

/-- Negative concentration gives zero extended-real density. -/
@[simp]
theorem vonMisesFisherPDF_of_neg (m : sphere (0 : E) 1) {κ : ℝ} (hκ : κ < 0)
    (x : sphere (0 : E) 1) : vonMisesFisherPDF m κ x = 0 := by
  simp [vonMisesFisherPDF, hκ]

/-- The real density is strictly positive at every sphere point for valid concentration. -/
theorem vonMisesFisherPDFReal_pos (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ)
    (x : sphere (0 : E) 1) : 0 < vonMisesFisherPDFReal m κ x := by
  have : Nontrivial E := ⟨⟨m, 0, ne_zero_of_mem_sphere one_ne_zero m⟩⟩
  simp only [vonMisesFisherPDFReal, ite_eq_left hκ]
  exact div_pos (exp_pos _) (integral_exp_inner_uniformSphereMeasure_pos _)

/-- The totalized real density is nonnegative. -/
theorem vonMisesFisherPDFReal_nonneg (m : sphere (0 : E) 1) (κ : ℝ)
    (x : sphere (0 : E) 1) : 0 ≤ vonMisesFisherPDFReal m κ x := by
  by_cases hκ : 0 ≤ κ
  · exact (vonMisesFisherPDFReal_pos m hκ x).le
  · simp [vonMisesFisherPDFReal, hκ]

/-- Converting the extended-real density back to the reals recovers the real density. -/
@[simp]
theorem toReal_vonMisesFisherPDF (m : sphere (0 : E) 1) (κ : ℝ) (x : sphere (0 : E) 1) :
    (vonMisesFisherPDF m κ x).toReal = vonMisesFisherPDFReal m κ x :=
  ENNReal.toReal_ofReal (vonMisesFisherPDFReal_nonneg m κ x)

/-- At zero concentration the density relative to uniform sphere probability is one. -/
@[simp]
theorem vonMisesFisherPDFReal_zero (m x : sphere (0 : E) 1) :
    vonMisesFisherPDFReal m 0 x = 1 := by
  have : Nontrivial E := ⟨⟨m, 0, ne_zero_of_mem_sphere one_ne_zero m⟩⟩
  simp [vonMisesFisherPDFReal]

/-- At zero concentration the extended-real density is one. -/
@[simp]
theorem vonMisesFisherPDF_zero (m x : sphere (0 : E) 1) : vonMisesFisherPDF m 0 x = 1 := by
  simp [vonMisesFisherPDF]

/-- The real density is jointly measurable in the direction, concentration, and sphere point. -/
@[fun_prop]
theorem measurable_uncurry_vonMisesFisherPDFReal :
    Measurable fun p : (sphere (0 : E) 1 × ℝ) × sphere (0 : E) 1 ↦
      vonMisesFisherPDFReal p.1.1 p.1.2 p.2 := by
  have hZ : Measurable fun η : E ↦
      ∫ y : sphere (0 : E) 1, exp ⟪η, (y : E)⟫ ∂uniformSphereMeasure E :=
    (by fun_prop : Measurable fun p : E × sphere (0 : E) 1 ↦
      exp ⟪p.1, (p.2 : E)⟫).stronglyMeasurable.integral_prod_right'.measurable
  unfold vonMisesFisherPDFReal
  apply Measurable.ite (measurableSet_le measurable_const measurable_fst.snd)
  · exact Measurable.div (by fun_prop) (hZ.comp (by fun_prop))
  · exact measurable_const

/-- The extended-real density is jointly measurable in all its arguments. -/
@[fun_prop]
theorem measurable_uncurry_vonMisesFisherPDF :
    Measurable fun p : (sphere (0 : E) 1 × ℝ) × sphere (0 : E) 1 ↦
      vonMisesFisherPDF p.1.1 p.1.2 p.2 :=
  measurable_uncurry_vonMisesFisherPDFReal.ennreal_ofReal

/-- The real density is measurable as a function of the sphere point. -/
@[fun_prop]
theorem measurable_vonMisesFisherPDFReal (m : sphere (0 : E) 1) (κ : ℝ) :
    Measurable (vonMisesFisherPDFReal m κ) :=
  measurable_uncurry_vonMisesFisherPDFReal.comp
    ((measurable_const : Measurable fun _ : sphere (0 : E) 1 ↦ (m, κ)).prodMk measurable_id)

/-- The extended-real density is measurable as a function of the sphere point. -/
@[fun_prop]
theorem measurable_vonMisesFisherPDF (m : sphere (0 : E) 1) (κ : ℝ) :
    Measurable (vonMisesFisherPDF m κ) :=
  measurable_uncurry_vonMisesFisherPDF.comp
    ((measurable_const : Measurable fun _ : sphere (0 : E) 1 ↦ (m, κ)).prodMk measurable_id)

/-- The totalized law is uniform sphere probability weighted by its named density. -/
theorem vonMisesFisherMeasure_eq_withDensity (m : sphere (0 : E) 1) (κ : ℝ) :
    vonMisesFisherMeasure m κ = (uniformSphereMeasure E).withDensity
      (vonMisesFisherPDF m κ) := by
  by_cases hκ : 0 ≤ κ
  · rw [vonMisesFisherMeasure_of_nonneg m hκ, vonMisesFisherNaturalMeasure_eq_withDensity]
    congr 1
    funext x
    simp only [vonMisesFisherPDF_eq_ofReal, vonMisesFisherPDFReal, ite_eq_left hκ]
  · have hzero : vonMisesFisherPDF m κ = 0 :=
      funext fun x ↦ vonMisesFisherPDF_of_neg m (lt_of_not_ge hκ) x
    simp [vonMisesFisherMeasure_of_neg m (lt_of_not_ge hκ), hzero]

/-- The named density is the Radon–Nikodym derivative against uniform sphere probability. -/
theorem rnDeriv_vonMisesFisherMeasure (m : sphere (0 : E) 1) (κ : ℝ) :
    (vonMisesFisherMeasure m κ).rnDeriv (uniformSphereMeasure E) =ᵐ[uniformSphereMeasure E]
      vonMisesFisherPDF m κ := by
  rw [vonMisesFisherMeasure_eq_withDensity]
  exact Measure.rnDeriv_withDensity _ (measurable_vonMisesFisherPDF m κ)

/-- The density has total mass one at every valid concentration. -/
theorem lintegral_vonMisesFisherPDF (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∫⁻ x, vonMisesFisherPDF m κ x ∂uniformSphereMeasure E = 1 := by
  have := isProbabilityMeasure_vonMisesFisherMeasure m hκ
  simpa only [vonMisesFisherMeasure_eq_withDensity, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ] using measure_univ (μ := vonMisesFisherMeasure m κ)

/-- The real density is integrable for every concentration, including negative concentrations
where it vanishes. -/
theorem integrable_vonMisesFisherPDFReal (m : sphere (0 : E) 1) (κ : ℝ) :
    Integrable (vonMisesFisherPDFReal m κ) (uniformSphereMeasure E) :=
  integrable_of_eq_withDensity (vonMisesFisherMeasure_eq_withDensity m κ)
    (measurable_vonMisesFisherPDFReal m κ).aemeasurable
    (ae_of_all _ (vonMisesFisherPDFReal_nonneg m κ))

/-- The real density integrates to one at valid concentrations. -/
theorem integral_vonMisesFisherPDFReal (m : sphere (0 : E) 1) {κ : ℝ} (hκ : 0 ≤ κ) :
    ∫ x, vonMisesFisherPDFReal m κ x ∂uniformSphereMeasure E = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (vonMisesFisherPDFReal_nonneg m κ))
    (measurable_vonMisesFisherPDFReal m κ).aestronglyMeasurable]
  simpa only [vonMisesFisherPDF_eq_ofReal, ENNReal.toReal_one] using
    congrArg ENNReal.toReal (lintegral_vonMisesFisherPDF m hκ)

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {E Ω : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace Ω] {P : Measure Ω}
  {X : Ω → sphere (0 : E) 1} {m : sphere (0 : E) 1} {κ : ℝ}

/-- A sphere-valued von Mises–Fisher variable has a density relative to uniform sphere
probability, not ambient volume. -/
theorem hasPDF_vonMisesFisherMeasure (hX : HasLaw X (vonMisesFisherMeasure m κ) P) :
    HasPDF X P (uniformSphereMeasure E) :=
  hasPDF_of_hasLaw_withDensity (measurable_vonMisesFisherPDF m κ).aemeasurable
    (by rwa [vonMisesFisherMeasure_eq_withDensity] at hX)

/-- The canonical density of a sphere-valued von Mises–Fisher variable agrees almost everywhere
with the named density against uniform sphere probability. -/
theorem pdf_eq_vonMisesFisherPDF (hX : HasLaw X (vonMisesFisherMeasure m κ) P) :
    pdf X P (uniformSphereMeasure E) =ᵐ[uniformSphereMeasure E] vonMisesFisherPDF m κ :=
  pdf_eq_of_hasLaw_withDensity (measurable_vonMisesFisherPDF m κ).aemeasurable
    (by rwa [vonMisesFisherMeasure_eq_withDensity] at hX)

end ProbabilityTheory.HasLaw
