/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Ergodic.InvariantProbabilities
public import Mathlib.Dynamics.Ergodic.Extreme

/-!
# Ergodic invariant probabilities are the extreme points

The invariant probability measures `TauCeti.invariantProbabilities T` of a map `T`, viewed in
`Measure X`, are Mathlib's set `{ν | MeasurePreserving T ν ν ∧ IsProbabilityMeasure ν}`
(`TauCeti.image_invariantProbabilities`), a convex set over `ℝ≥0∞`. Mathlib's
`Ergodic.of_mem_extremePoints` and `Ergodic.mem_extremePoints` then say that an invariant
probability is ergodic exactly when it is an extreme point of this set
(`TauCeti.ergodic_iff_mem_extremePoints_invariantProbabilities`). In particular the unique
invariant probability of a uniquely ergodic map is ergodic (`TauCeti.UniquelyErgodic.ergodic`).
-/

public section

namespace TauCeti

open MeasureTheory Set
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {T : X → X}

/-- The invariant probabilities of `T`, as measures, are the probability measures preserved by
`T`. -/
theorem image_invariantProbabilities :
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
  rw [image_invariantProbabilities]
  exact ⟨Ergodic.mem_extremePoints, Ergodic.of_mem_extremePoints⟩

/-- The invariant probability of a uniquely ergodic map is ergodic. -/
theorem UniquelyErgodic.ergodic (h : UniquelyErgodic T) {ν : ProbabilityMeasure X}
    (hν : ν ∈ invariantProbabilities T) : Ergodic T ν := by
  obtain ⟨μ, hμ⟩ := uniquelyErgodic_def.1 h
  rw [hμ, mem_singleton_iff] at hν
  rw [ergodic_iff_mem_extremePoints_invariantProbabilities, hμ, image_singleton, hν,
    extremePoints_singleton]
  exact mem_singleton _

end TauCeti
