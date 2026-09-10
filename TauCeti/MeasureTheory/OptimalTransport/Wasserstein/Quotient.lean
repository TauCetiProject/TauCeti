/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Dirac
public import TauCeti.MeasureTheory.Measure.SeparationQuotient
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Pushforward

/-!
# Wasserstein separation on pseudometric spaces

On a pseudometric ground space, zero Wasserstein distance identifies probability laws only after
the ground space itself is separated. This file expresses that statement using Mathlib's
`SeparationQuotient`: for a complete second-countable pseudometric space carrying its Borel
sigma-algebra, `W_p μ ν = 0` if and only if the pushforwards of `μ` and `ν` to the separation
quotient agree.

The reverse implication uses a feature of the Borel measurable structure of a pseudometric space:
every open set is saturated under zero distance. Since open sets generate the Borel sigma-algebra,
pushforward along `SeparationQuotient.mk` is injective on finite Borel measures. The forward
implication contracts Wasserstein distance along the quotient map and applies metric separation on
the complete separable metric quotient.

## Main statements

* `MeasureTheory.Measure.separationQuotient` is pushforward along Mathlib's separation-quotient map,
  carrying the quotient's Borel measurable structure.
* `MeasureTheory.Measure.separationQuotient_inj` says that two finite Borel measures on a
  pseudometric space have the same quotient pushforward exactly when they agree.
* `TauCeti.wassersteinEDist_eq_zero_iff_separationQuotient_eq` characterizes zero Wasserstein
  distance by equality after pushforward to the metric separation quotient, for every nonzero
  exponent, including `p = ∞`.
* `TauCeti.wassersteinEDist_dirac_eq_zero_of_dist_eq_zero` records the pseudometric
  regression case of two zero-distance points.

## References

* C. Villani, *Optimal Transport: Old and New*, Grundlehren 338, Springer 2009, Chapter 6.
-/

public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal

universe u

namespace TauCeti

variable {X : Type u} [PseudoMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [SecondCountableTopology X] {p : ℝ≥0∞}

/-- **Separation on a pseudometric base.** For every nonzero exponent, Wasserstein distance
vanishes exactly when the two laws have equal pushforwards to the metric separation quotient.
The statement includes the essential-supremum endpoint `p = ∞`. -/
theorem wassersteinEDist_eq_zero_iff_separationQuotient_eq (hp : p ≠ 0)
    (μ ν : Measure X) [CompleteSpace X] [IsFiniteMeasure μ] :
    wassersteinEDist p μ ν = 0 ↔
      Measure.separationQuotient μ = Measure.separationQuotient ν := by
  let _ : TopologicalSpace.SeparableSpace (SeparationQuotient X) :=
    SeparationQuotient.surjective_mk.denseRange.separableSpace
      SeparationQuotient.continuous_mk
  let _ : SecondCountableTopology (SeparationQuotient X) :=
    UniformSpace.secondCountable_of_separable (SeparationQuotient X)
  let _ : MeasurableSpace (SeparationQuotient X) := borel (SeparationQuotient X)
  let _ : BorelSpace (SeparationQuotient X) := ⟨rfl⟩
  have hmk : Measurable (SeparationQuotient.mk : X → SeparationQuotient X) :=
    SeparationQuotient.continuous_mk.measurable
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Measure.separationQuotient_def, Measure.separationQuotient_def]
    have hLip : LipschitzWith 1 (SeparationQuotient.mk : X → SeparationQuotient X) := by
      intro x y
      simp only [SeparationQuotient.edist_mk, ENNReal.coe_one, one_mul, le_refl]
    have hmap := wassersteinEDist_map_le_mul_of_ne_zero (p := p)
      measurable_edist hmk hLip one_ne_zero μ ν
    rw [h, mul_zero] at hmap
    exact eq_of_wassersteinEDist_eq_zero hp _ _ (nonpos_iff_eq_zero.mp hmap)
  · have hμν : μ = ν := (Measure.separationQuotient_inj μ ν).1 h
    subst ν
    exact wassersteinEDist_self_of_measurable_edist measurable_edist p μ

/-- **Pseudometric regression.** Dirac laws at two zero-distance points have zero Wasserstein
distance for every exponent, even when the points are not equal. -/
theorem wassersteinEDist_dirac_eq_zero_of_dist_eq_zero {x y : X} (hxy : dist x y = 0) :
    wassersteinEDist p (Measure.dirac x) (Measure.dirac y) = 0 := by
  rw [Measure.dirac_eq_dirac_of_inseparable (Metric.inseparable_iff.2 hxy)]
  exact wassersteinEDist_self_of_measurable_edist measurable_edist p (Measure.dirac y)

end TauCeti
