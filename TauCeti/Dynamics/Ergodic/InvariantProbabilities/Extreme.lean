/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.InvariantProbabilities
public import Mathlib.Dynamics.Ergodic.Extreme
import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Ergodic invariant probabilities are the extreme points

The invariant probability measures `TauCeti.invariantProbabilities T` of a map `T`, viewed in
`Measure X`, are Mathlib's set `{ν | MeasurePreserving T ν ν ∧ IsProbabilityMeasure ν}`
(`TauCeti.toMeasure_image_invariantProbabilities`), a convex set over `ℝ≥0∞`. Mathlib's
`Ergodic.iff_mem_extremePoints` then says that an invariant probability is ergodic exactly when
it is an extreme point of this set
(`TauCeti.ergodic_iff_mem_extremePoints_invariantProbabilities`). In particular the unique
invariant probability of a uniquely ergodic map is ergodic (`TauCeti.UniquelyErgodic.ergodic`),
and the Dirac mass at a fixed point of a measurable map is an ergodic invariant probability
(`TauCeti.ergodic_dirac_of_isFixedPt`).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {T : X → X}

/-- The invariant probabilities of `T`, as measures, are the probability measures preserved by
`T`. -/
theorem toMeasure_image_invariantProbabilities :
    ((↑) : ProbabilityMeasure X → Measure X) '' invariantProbabilities T =
      {ν | MeasurePreserving T ν ν ∧ IsProbabilityMeasure ν} := by
  ext ν
  refine ⟨?_, fun ⟨hν, hν₁⟩ ↦ ⟨⟨ν, hν₁⟩, mem_invariantProbabilities.2 hν, rfl⟩⟩
  rintro ⟨ν, hν, rfl⟩
  exact ⟨mem_invariantProbabilities.1 hν, inferInstance⟩

/-- **Ergodic measures are the extreme points.** A probability measure is ergodic for `T` exactly
when it is an extreme point of the invariant probabilities of `T`, as a subset of `Measure X`. -/
theorem ergodic_iff_mem_extremePoints_invariantProbabilities {ν : ProbabilityMeasure X} :
    Ergodic T ν ↔ (ν : Measure X) ∈ extremePoints ℝ≥0∞
      (((↑) : ProbabilityMeasure X → Measure X) '' invariantProbabilities T) := by
  rw [toMeasure_image_invariantProbabilities]
  exact Ergodic.iff_mem_extremePoints

/-- The invariant probability of a uniquely ergodic map is ergodic. -/
theorem UniquelyErgodic.ergodic (h : UniquelyErgodic T) {ν : ProbabilityMeasure X}
    (hν : ν ∈ invariantProbabilities T) : Ergodic T ν := by
  obtain ⟨μ, hμ⟩ := uniquelyErgodic_def.1 h
  rw [hμ, mem_singleton_iff] at hν
  rw [ergodic_iff_mem_extremePoints_invariantProbabilities, hμ, image_singleton, hν,
    extremePoints_singleton]
  exact mem_singleton _

/-- The Dirac mass at a fixed point of a measurable map is ergodic. -/
theorem ergodic_dirac_of_isFixedPt (hT : Measurable T) {x : X} (hx : Function.IsFixedPt T x) :
    Ergodic T (Measure.dirac x) where
  toMeasurePreserving := ⟨hT, by rw [Measure.map_dirac' hT, hx.eq]⟩
  aeconst_set _ hs _ := eventuallyEmptyOrUniv_ae_dirac hs

end TauCeti
