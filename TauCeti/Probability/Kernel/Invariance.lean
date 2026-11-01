/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Invariance

/-!
# Invariant and reversible measures of kernels on countable spaces

On a countable space whose singletons are measurable, invariance and detailed balance of a kernel
have pointwise content. A measure is invariant under the kernel if and only if every singleton
receives exactly the mass the kernel pushes into it. The kernel is reversible with respect to the
measure if and only if, for every pair of points, the flux from the singleton of one point to the
singleton of the other equals the flux in the opposite direction, the balance of transitions
between singletons. Since reversibility implies invariance for a Markov kernel, the singleton
form of detailed balance also implies invariance.

## Main statements

* `invariant_iff_singletons`: invariance of a measure under a kernel, expressed in terms of the
  mass flowing into each singleton.
* `isReversible_iff_singletons`: detailed balance of a kernel with respect to a measure,
  expressed in terms of the two directed fluxes between each pair of singletons.
* `invariant_of_reversible_singletons`: a Markov kernel whose singleton fluxes are in balance
  leaves the measure invariant.
-/

public section

open MeasureTheory ProbabilityTheory

namespace ProbabilityTheory.Kernel

variable {S : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
  (κ : Kernel S S) (π : Measure S)

/-- A measure on a countable space is invariant under a kernel if and only if every singleton
receives the mass the kernel pushes into it. -/
theorem invariant_iff_singletons : κ.Invariant π ↔ ∀ y, ∑' x, π {x} * κ x {y} = π {y} := by
  constructor
  · intro h y
    calc
      ∑' x, π {x} * κ x {y} = (Measure.sum (fun ω => π {ω} • κ ω)) {y} := by simp
      _ = (κ ∘ₘ π) {y} := by rw [← Measure.comp_eq_sum_of_countable]
      _ = π {y} := congrArg (fun μ : Measure S => μ {y}) h
  · intro h
    have hsum : κ ∘ₘ π = π := (Measure.ext_iff_singleton (μ := κ ∘ₘ π) (ν := π)).2 fun y => by
      calc
        (κ ∘ₘ π) {y} = (Measure.sum (fun ω => π {ω} • κ ω)) {y} := by
          rw [Measure.comp_eq_sum_of_countable]
        _ = ∑' x, π {x} * κ x {y} := by simp
        _ = π {y} := h y
    exact hsum

/-- A kernel on a countable space is reversible with respect to a measure if and only if, for
every pair of points, the flux from the singleton of one point to the singleton of the other
equals the flux in the opposite direction. -/
theorem isReversible_iff_singletons :
    κ.IsReversible π ↔ ∀ x y, π {x} * κ x {y} = π {y} * κ y {x} := by
  constructor
  · intro h x y
    have hxy := h (A := {x}) (B := {y}) (measurableSet_singleton x) (measurableSet_singleton y)
    simpa [lintegral_singleton, mul_comm] using hxy
  · intro h
    -- Restate the goal in the explicit form that binds the two measurable sets
    -- and their measurability proofs, so the proof can run over the sets.
    change ∀ (A B : Set S) (_ : MeasurableSet A) (_ : MeasurableSet B),
      ∫⁻ x in A, κ x B ∂π = ∫⁻ x in B, κ x A ∂π
    intro A B _ _
    have hAc : A.Countable := Set.Countable.mono (Set.subset_univ A) Set.countable_univ
    have hBc : B.Countable := Set.Countable.mono (Set.subset_univ B) Set.countable_univ
    have hsum (x : S) : ∑' y : B, κ x {↑y} = κ x B := by
      simpa only [Set.preimage_id] using
        tsum_measure_preimage_singleton hBc (f := id) (fun _ _ => by
          simpa only [Set.preimage_id] using measurableSet_singleton _)
    have hsumA (y : S) : ∑' x : A, κ y {↑x} = κ y A := by
      simpa only [Set.preimage_id] using
        tsum_measure_preimage_singleton hAc (f := id) (fun _ _ => by
          simpa only [Set.preimage_id] using measurableSet_singleton _)
    calc
      ∫⁻ x in A, κ x B ∂π = ∑' x : A, (κ x B) * π {↑x} := by
        rw [lintegral_countable (f := fun x => κ x B) hAc]
      _ = ∑' x : A, ∑' y : B, π {↑x} * κ x {↑y} :=
        tsum_congr fun x => by
          calc
            (κ x B) * π {↑x} = (∑' y : B, κ x {↑y}) * π {↑x} := by rw [← hsum x]
            _ = π {↑x} * ∑' y : B, κ x {↑y} := by rw [mul_comm]
            _ = ∑' y : B, π {↑x} * κ x {↑y} := by rw [← ENNReal.tsum_mul_left]
      _ = ∑' y : B, ∑' x : A, π {↑x} * κ x {↑y} := by rw [ENNReal.tsum_comm]
      _ = ∑' y : B, ∑' x : A, π {↑y} * κ y {↑x} :=
        tsum_congr (fun y => tsum_congr (fun x => h x y))
      _ = ∑' y : B, (∑' x : A, κ y {↑x}) * π {↑y} :=
        tsum_congr fun y => by
          calc
            ∑' x : A, π {↑y} * κ y {↑x} = π {↑y} * ∑' x : A, κ y {↑x} := by
              rw [ENNReal.tsum_mul_left]
            _ = (∑' x : A, κ y {↑x}) * π {↑y} := by rw [mul_comm]
      _ = ∑' y : B, (κ y A) * π {↑y} := by
        exact tsum_congr (fun y => by rw [← hsumA y])
      _ = ∫⁻ x in B, κ x A ∂π := by rw [← lintegral_countable (f := fun x => κ x A) hBc]

/-- A Markov kernel on a countable space whose singleton fluxes are in balance leaves the
measure invariant. -/
theorem invariant_of_reversible_singletons [IsMarkovKernel κ]
    (h : ∀ x y, π {x} * κ x {y} = π {y} * κ y {x}) : κ.Invariant π :=
  ((isReversible_iff_singletons κ π).2 h).invariant

end ProbabilityTheory.Kernel
