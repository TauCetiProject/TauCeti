/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Adapted

/-!
# Pre-Brownian motion relative to a filtration

Mathlib's `ProbabilityTheory.IsPreBrownianReal` prescribes only the finite-dimensional laws of
`W`. A martingale statement needs a filtration, and the law of `W` alone does not say how `W`
interacts with it: `TauCeti.Probability.IsFilteredPreBrownianReal ℱ W P` adds that `W` is adapted
to `ℱ` and that every increment `W_t - W_s`, `s ≤ t`, is independent of `ℱ_s`. A pre-Brownian
motion is a pre-Brownian motion relative to its own natural filtration
(`ProbabilityTheory.IsPreBrownianReal.isFilteredPreBrownianReal_natural`).

## Main declarations

* `TauCeti.Probability.IsFilteredPreBrownianReal`: a pre-Brownian motion relative to a
  filtration.
* `ProbabilityTheory.IsPreBrownianReal.isFilteredPreBrownianReal_natural`: the natural
  filtration.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.1.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `W` is a **pre-Brownian motion relative to the filtration `ℱ`** under `P`: its
finite-dimensional laws are those of Brownian motion, it is adapted to `ℱ`, and for `s ≤ t` the
increment `W t - W s` is independent of `ℱ s`. -/
structure IsFilteredPreBrownianReal (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω := by volume_tac) : Prop extends IsPreBrownianReal W P where
  /-- `W t` is `ℱ t`-measurable. -/
  adapted : Adapted ℱ W
  /-- The increment `W t - W s` is independent of `ℱ s`. -/
  indep_sub ⦃s t : ℝ≥0⦄ : s ≤ t → Indep (.comap (W t - W s) inferInstance) (ℱ s) P

end TauCeti.Probability

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A pre-Brownian motion is a pre-Brownian motion relative to its natural filtration: by the weak
Markov property `ProbabilityTheory.IsPreBrownianReal.indepFun_shift`, the increments after time
`s` are independent of `(B u, u ≤ s)`. -/
theorem isFilteredPreBrownianReal_natural (hB : IsPreBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t)) :
    IsFilteredPreBrownianReal (Filtration.natural B hmeas) B P where
  toIsPreBrownianReal := hB
  adapted t := (Filtration.stronglyAdapted_natural hmeas t).measurable
  indep_sub s t hst := by
    rw [Filtration.natural_eq_comap]
    refine indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).mp (hB.indepFun_shift s)) ?_
    have : B t - B s = (fun x : ℝ≥0 → ℝ ↦ x (t - s)) ∘ fun ω u ↦ B (s + u) ω - B s ω := by
      ext ω
      simp [add_tsub_cancel_of_le hst]
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

end ProbabilityTheory.IsPreBrownianReal
