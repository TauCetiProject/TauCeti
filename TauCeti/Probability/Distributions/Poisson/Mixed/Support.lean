/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Poisson.Mixed.Basic
public import TauCeti.MeasureTheory.Measure.Support

import TauCeti.Probability.Distributions.Poisson.Basic
import TauCeti.Probability.Distributions.Poisson.Measurability

/-!
# Support of mixed Poisson laws

A nonzero mixing measure gives positive mass to every count as soon as it gives positive mass
to nonzero rates. If it is concentrated at rate zero, only count zero has positive mass.
Consequently the support of the real-cast law is either the singleton zero or the nonnegative
integers. This distinction determines whether the upper quantile endpoint is finite.

## References

* J. Grandell, *Mixed Poisson Processes*, Chapman & Hall (1997), ch. 2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open TauCeti.Probability
open scoped NNReal

namespace MeasureTheory.Measure

/-- A mixed Poisson singleton has nonzero mass precisely when the mixing measure is nonzero
and either the count is zero or nonzero rates have positive mixing mass. -/
theorem mixedPoissonMeasure_singleton_ne_zero_iff (ρ : Measure ℝ≥0) (n : ℕ) :
    mixedPoissonMeasure ρ {n} ≠ 0 ↔
      ρ ≠ 0 ∧ (n = 0 ∨ ρ {0}ᶜ ≠ 0) := by
  have hm : Measurable (fun r : ℝ≥0 ↦ poissonMeasure r {n}) :=
    (measurable_coe (measurableSet_singleton n)).comp measurable_poissonMeasure
  rw [mixedPoissonMeasure_def,
    bind_apply (measurableSet_singleton n) measurable_poissonMeasure.aemeasurable,
    ← pos_iff_ne_zero, lintegral_pos_iff_support hm]
  by_cases hn : n = 0
  · simp [Function.support, poissonMeasure_singleton_ne_zero_iff, hn]
  · have hs : Function.support (fun r : ℝ≥0 ↦ poissonMeasure r {n}) = {0}ᶜ := by
      ext r
      simp [Function.support, poissonMeasure_singleton_ne_zero_iff, hn]
    rw [hs, pos_iff_ne_zero]
    simp only [hn, false_or]
    exact ⟨fun h ↦ ⟨fun hρ ↦ h (by simp [hρ]), h⟩, And.right⟩

/-- A nonzero mixed Poisson law has full native support unless the mixing measure is
concentrated at rate zero, in which case its support is the singleton zero. -/
@[simp]
theorem support_mixedPoissonMeasure (ρ : Measure ℝ≥0) [NeZero ρ] :
    (mixedPoissonMeasure ρ).support = if ρ {0}ᶜ = 0 then {0} else univ := by
  rw [support_eq_setOf_singleton_ne_zero]
  ext n
  by_cases hρ : ρ {0}ᶜ = 0 <;>
    simp [mixedPoissonMeasure_singleton_ne_zero_iff, hρ, NeZero.ne ρ]

/-- Real-cast mixed Poisson support is the nonnegative integers unless all mixing mass is at
rate zero, when it is the singleton zero. -/
@[simp]
theorem support_map_cast_mixedPoissonMeasure (ρ : Measure ℝ≥0) [NeZero ρ] :
    ((mixedPoissonMeasure ρ).map (Nat.cast : ℕ → ℝ)).support =
      if ρ {0}ᶜ = 0 then {0} else range (Nat.cast : ℕ → ℝ) := by
  rw [support_map_eq_closure_image _ support_mem_ae (by fun_prop),
    support_mixedPoissonMeasure]
  split_ifs <;> simp [Nat.isClosedEmbedding_coe_real.isClosed_range.closure_eq]

end MeasureTheory.Measure
