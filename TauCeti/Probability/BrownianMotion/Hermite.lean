/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.NormalizedIncrements
public import TauCeti.Probability.Distributions.Gaussian.Hermite.Pi.Pullback

/-!
# Hermite expansions of finite Brownian observations

On a strictly increasing grid starting at zero, the standardized Brownian increments carry
exactly the same information, modulo null sets, as the observations on that grid. Thus the
Gaussian `L²` pullback has as its range precisely the classes measurable from those observations.
Every such claim has an `L²` expansion in products of normalized Hermite polynomials of the
standardized increments, with coefficients computed on the original probability space.

This is a finite-grid completeness statement, not a representation by a stochastic integral.
It needs only pre-Brownian laws and a measurable increment vector, not continuous paths or a
filtration. The one-point grid {0} (`n = 0`, empty increment vector) is allowed: its observation
is zero almost surely and only constant classes remain. Measurability is explicitly up to null
sets, so the result also applies to claims measured in the completed observation sigma algebra.

The range and expansion are stated using `HasLaw.gaussianVectorL2Isometry` and
`HasLaw.gaussianVectorHermite` applied to `IsPreBrownianReal.hasLaw_normalizedBrownianIncrements`.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.4.
-/

public section
noncomputable section

open MeasureTheory ProbabilityTheory TauCeti
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {n : ℕ} {t : Fin (n + 1) → ℝ≥0}

/-- The Gaussian pullback along standardized increments has range exactly the `L²` classes
measurable, up to null sets, from observations on a strictly increasing grid starting at zero. -/
theorem mem_range_gaussianVectorL2Isometry_iff
    (hB : IsPreBrownianReal B P) (ht : StrictMono t) (ht₀ : t 0 = 0)
    (hmeas : Measurable (normalizedBrownianIncrements B t)) (u : Lp ℝ 2 P) :
    u ∈ LinearMap.range
      ((hB.hasLaw_normalizedBrownianIncrements ht).gaussianVectorL2Isometry hmeas).toLinearMap ↔
      AEStronglyMeasurable[MeasurableSpace.comap (fun ω i ↦ B (t i) ω) inferInstance] u P := by
  rw [(hB.hasLaw_normalizedBrownianIncrements ht).mem_range_gaussianVectorL2Isometry_iff]
  exact hB.aestronglyMeasurable_comap_normalizedBrownianIncrements_iff ht ht₀

/-- Every square-integrable claim measurable, up to null sets, from Brownian observations
on a strictly increasing finite grid starting at zero has a Hermite expansion in the standardized
increments converging in `L²`. The coefficients are expectations on the original sample space. -/
theorem hasSum_gaussianVectorHermite_of_aestronglyMeasurable_comap
    (hB : IsPreBrownianReal B P) (ht : StrictMono t) (ht₀ : t 0 = 0)
    (hmeas : Measurable (normalizedBrownianIncrements B t)) (u : Lp ℝ 2 P)
    (hu : AEStronglyMeasurable[MeasurableSpace.comap
      (fun ω i ↦ B (t i) ω) inferInstance] u P) :
    HasSum (fun a : Fin n → ℕ ↦
      (∫ ω, (hB.hasLaw_normalizedBrownianIncrements ht).gaussianVectorHermite
        hmeas a ω * u ω ∂P) •
      (hB.hasLaw_normalizedBrownianIncrements ht).gaussianVectorHermite hmeas a) u := by
  apply HasLaw.hasSum_gaussianVectorHermite_of_aestronglyMeasurable
  exact (hB.aestronglyMeasurable_comap_normalizedBrownianIncrements_iff ht ht₀).2 hu

end ProbabilityTheory.IsPreBrownianReal
