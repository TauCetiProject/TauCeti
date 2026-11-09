/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.PMF
public import Mathlib.Probability.Kernel.Invariance

/-!
# Stationarity and detailed balance on countable state spaces

On a countable space with measurable singletons, Mathlib's set-level notions
`Kernel.Invariant` and `Kernel.IsReversible` reduce to identities between singleton masses.
A measure `π` is invariant under `κ` exactly when every state receives its own mass,
`∑' x, π {x} * κ x {y} = π {y}`, and `κ` satisfies detailed balance with respect to `π`
exactly when the flux between every two states is the same in both directions,
`π {x} * κ x {y} = π {y} * κ y {x}`.

Neither characterization needs the measure to be finite or the kernel to be Markov, and
the state space may be infinite. For a Markov kernel, the singleton form of detailed balance
therefore gives invariance through Mathlib's `Kernel.IsReversible.invariant`.

For kernels given by transition weights, `Kernel.ofPMF p`, and laws given by a probability
mass function, the same criteria are stated in terms of the weights alone. The finite
row-vector and symmetric-matrix forms are in `TauCeti.Probability.Kernel.Matrix.Invariance`.

## Main statements

* `ProbabilityTheory.Kernel.invariant_iff_singleton`: invariance as a balance equation at
  each state.
* `ProbabilityTheory.Kernel.isReversible_iff_singleton`: detailed balance as equality of the
  two directed fluxes between each pair of states.
* `ProbabilityTheory.Kernel.invariant_ofPMF_toMeasure_iff` and
  `ProbabilityTheory.Kernel.isReversible_ofPMF_toMeasure_iff`: the same criteria for
  transition weights and a probability mass function.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.7 and 1.9.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]

/-- On a countable space, a measure is invariant under a kernel exactly when each state
receives, from all states together, precisely its own mass. Neither finiteness of the
measure nor the Markov property of the kernel is needed. -/
theorem invariant_iff_singleton {κ : Kernel α α} {π : Measure α} :
    κ.Invariant π ↔ ∀ y, ∑' x, π {x} * κ x {y} = π {y} := by
  rw [Invariant, Measure.ext_iff_singleton]
  refine forall_congr' fun y => ?_
  rw [Measure.bind_apply (measurableSet_singleton y) κ.aemeasurable, lintegral_countable']
  simp_rw [mul_comm]

/-- On a countable space, a kernel satisfies detailed balance with respect to a measure
exactly when, for every two states, the flux `π {x} * κ x {y}` from `x` to `y` equals the
flux from `y` to `x`. Neither finiteness of the measure nor the Markov property of the
kernel is needed. -/
theorem isReversible_iff_singleton {κ : Kernel α α} {π : Measure α} :
    κ.IsReversible π ↔ ∀ x y, π {x} * κ x {y} = π {y} * κ y {x} := by
  -- The flux from `A` to `B` is the double sum of the singleton fluxes over `A × B`.
  have hflux (A B : Set α) : ∫⁻ x in A, κ x B ∂π =
      ∑' x, ∑' y, A.indicator (fun x => B.indicator (fun y => π {x} * κ x {y}) y) x := by
    rw [← lintegral_indicator A.to_countable.measurableSet, lintegral_countable']
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ A
    · simp_rw [Set.indicator_of_mem hx, ← Measure.tsum_indicator_apply_singleton (κ x) B
        B.to_countable.measurableSet, ← ENNReal.tsum_mul_right, mul_comm (π {x}),
        Set.indicator_mul_left]
    · simp [Set.indicator_of_notMem hx]
  refine ⟨fun h x y => ?_, fun h A B _ _ => ?_⟩
  · simpa [lintegral_singleton, mul_comm] using h (measurableSet_singleton x)
      (measurableSet_singleton y)
  · rw [hflux, hflux, tsum_comm]
    refine tsum_congr fun y => tsum_congr fun x => ?_
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ B <;> simp [hx, hy, h y x]

/-- Transition weights `p` leave a probability mass function `π` invariant exactly when
`∑' x, π x * p x y = π y` for every state `y`. -/
theorem invariant_ofPMF_toMeasure_iff (p : α → PMF α) (π : PMF α) :
    (ofPMF p).Invariant π.toMeasure ↔ ∀ y, ∑' x, π x * p x y = π y := by
  simp [invariant_iff_singleton, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

/-- Transition weights `p` satisfy detailed balance with respect to a probability mass
function `π` exactly when `π x * p x y = π y * p y x` for every two states. -/
theorem isReversible_ofPMF_toMeasure_iff (p : α → PMF α) (π : PMF α) :
    (ofPMF p).IsReversible π.toMeasure ↔ ∀ x y, π x * p x y = π y * p y x := by
  simp [isReversible_iff_singleton,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

end ProbabilityTheory.Kernel
