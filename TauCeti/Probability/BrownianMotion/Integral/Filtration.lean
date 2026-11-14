/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Integral.L2

/-!
# Filtration invariance of the predictable L² Brownian integral

Enlarging a filtration does not change the integral of an originally predictable L²
integrand, provided the integrator is still Brownian relative to the larger filtration.
The integrand is transported by the native measure-preserving pullback along the identity
between the two predictable measure spaces. This compares the actual completed maps,
not just the elementary gains, and includes the zero horizon.

The comparison is useful when constructing stochastic integrals on an augmented filtration
and identifying them with raw-filtration integrals. It does not assert that an arbitrary
filtration enlargement preserves Brownian increment independence, or that all integrands
of the enlarged filtration were predictable in the original one.

The proof uses `l2Integral_unique`: both continuous linear maps have the same values on
the smaller filtration's predictable rectangles.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.2, elementary integrals and their L² completion.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {ℱ 𝒢 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- Enlarging the filtration while preserving the Brownian property leaves the integral
unchanged on the smaller predictable L² space. The pullback along the identity on time/sample
pairs represents the same coefficient function almost everywhere. -/
theorem l2Integral_compMeasurePreserving_id
    (hW : IsFilteredPreBrownianReal 𝒢 W P) (hB : IsFilteredPreBrownianReal ℱ W P)
    (h : ℱ ≤ 𝒢) (T : ℝ≥0) (f : Lp ℝ 2 (ℱ.predictableMeasure P T)) :
    letI : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
    hW.l2Integral T (Lp.compMeasurePreserving id
      (Filtration.measurePreserving_id_predictableMeasure h P T) f) = hB.l2Integral T f := by
  let : MeasurableSpace (ℝ≥0 × Ω) := ℱ.predictable
  let := hB.toIsPreBrownianReal.hasLaw_eval 0 |>.isProbabilityMeasure
  let J := (hW.l2Integral T).toContinuousLinearMap.comp
    (Lp.compMeasurePreservingₗᵢ ℝ id
      (Filtration.measurePreserving_id_predictableMeasure h P T)).toContinuousLinearMap
  have hJ : J = (hB.l2Integral T).toContinuousLinearMap := by
    apply hB.l2Integral_unique T
    intro s t hst ht A hA
    have hp := Lp.indicatorConstLp_compMeasurePreserving (p := 2)
      (measurableSet_predictable_Ioc_prod s t hA) (measure_ne_top _ _) (1 : ℝ)
      (Filtration.measurePreserving_id_predictableMeasure h P T)
    have hrect : J (indicatorConstLp 2 (measurableSet_predictable_Ioc_prod s t hA)
        (measure_ne_top _ _) 1) =
        hW.l2Integral T (indicatorConstLp 2
          (measurableSet_predictable_Ioc_prod s t (h _ _ hA)) (measure_ne_top _ _) 1) :=
      congrArg (hW.l2Integral T) hp
    rw [hrect]
    exact hW.coeFn_l2Integral_indicatorConstLp_Ioc_prod_of_le hst.le ht (h _ _ hA) 1
  exact congrArg (fun A : Lp ℝ 2 (ℱ.predictableMeasure P T) →L[ℝ] Lp ℝ 2 P ↦ A f) hJ

end TauCeti.Probability.IsFilteredPreBrownianReal
