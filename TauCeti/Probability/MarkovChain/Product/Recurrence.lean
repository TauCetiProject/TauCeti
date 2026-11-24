/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Invariant
public import TauCeti.Probability.MarkovChain.Product.Basic

/-!
# Recurrence and positive recurrence of independent product chains

Let `κ : Kernel α α` and `η : Kernel β β` be Markov transition kernels and write `κ ∥ₖ η` for their
independent parallel composition on `α × β`.

* **Coordinate recurrence and return-time lower bounds.** Whenever the target coordinate space has
  measurable singletons, coordinate projection of `markovChainLaw (Measure.dirac z) (κ ∥ₖ η)`
  transfers recurrence (`ProbabilityTheory.Kernel.IsRecurrent.of_parallelComp_left`,
  `ProbabilityTheory.Kernel.IsRecurrent.of_parallelComp_right`), contrapositively lifts transience
  (`ProbabilityTheory.Kernel.IsTransient.parallelComp_left`,
  `ProbabilityTheory.Kernel.IsTransient.parallelComp_right`), and bounds each marginal mean return
  time by the joint mean return time
  (`ProbabilityTheory.Kernel.meanReturnTime_le_parallelComp_left`,
  `ProbabilityTheory.Kernel.meanReturnTime_le_parallelComp_right`), so positive recurrence of `z`
  projects to each coordinate (`ProbabilityTheory.Kernel.IsPositiveRecurrent.of_parallelComp_left`,
  `ProbabilityTheory.Kernel.IsPositiveRecurrent.of_parallelComp_right`).
* **Cycle-occupation upper bound and positive recurrence.** When both `α` and `β` have measurable
  singletons, at every state `z : α × β` the product cycle occupation measure satisfies
  `(κ ∥ₖ η).cycleOccupation z ≤ (κ.cycleOccupation z.1).prod (η.cycleOccupation z.2)`
  (`ProbabilityTheory.Kernel.cycleOccupation_parallelComp_le`), hence
  `(κ ∥ₖ η).meanReturnTime z ≤ κ.meanReturnTime z.1 * η.meanReturnTime z.2`
  (`ProbabilityTheory.Kernel.meanReturnTime_parallelComp_le`), without any irreducibility,
  aperiodicity, or countability assumptions. Combining both bounds shows that `z` is positive
  recurrent for `κ ∥ₖ η` if and only if `z.1` is positive recurrent for `κ` and `z.2` is positive
  recurrent for `η` (`ProbabilityTheory.Kernel.IsPositiveRecurrent.parallelComp`,
  `ProbabilityTheory.Kernel.isPositiveRecurrent_parallelComp_iff`).

## Main statements

* `ProbabilityTheory.Kernel.IsRecurrent.of_parallelComp_left`,
  `ProbabilityTheory.Kernel.IsRecurrent.of_parallelComp_right`,
  `ProbabilityTheory.Kernel.meanReturnTime_le_parallelComp_left`,
  `ProbabilityTheory.Kernel.meanReturnTime_le_parallelComp_right`: coordinate projections of
  recurrence and lower bounds on the product mean return time.
* `ProbabilityTheory.Kernel.cycleOccupation_parallelComp_le`,
  `ProbabilityTheory.Kernel.meanReturnTime_parallelComp_le`: upper bounds on the cycle occupation
  measure and mean return time of `κ ∥ₖ η` when both coordinate spaces have measurable singletons.
* `ProbabilityTheory.Kernel.IsPositiveRecurrent.parallelComp`,
  `ProbabilityTheory.Kernel.isPositiveRecurrent_parallelComp_iff`: positive recurrence of `κ ∥ₖ η`
  at `z` is equivalent to positive recurrence of `z.1` under `κ` and `z.2` under `η`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.7–1.8.
* Olav Kallenberg, *Foundations of Modern Probability*, 2nd edition, Springer (2002), Chapter 8.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Recurrence of `z` under `κ ∥ₖ η` implies recurrence of `z.1` under `κ`. Only measurable
singletons on the first coordinate space are needed. -/
theorem IsRecurrent.of_parallelComp_left [MeasurableSingletonClass α]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {z : α × β} (hz : (κ ∥ₖ η).IsRecurrent z) :
    κ.IsRecurrent z.1 :=
  hz.of_map_eq measurable_fst fun p => by simp [parallelComp_apply]

/-- Recurrence of `z` under `κ ∥ₖ η` implies recurrence of `z.2` under `η`. Only measurable
singletons on the second coordinate space are needed. -/
theorem IsRecurrent.of_parallelComp_right [MeasurableSingletonClass β]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {z : α × β} (hz : (κ ∥ₖ η).IsRecurrent z) :
    η.IsRecurrent z.2 :=
  hz.of_map_eq measurable_snd fun p => by simp [parallelComp_apply]

/-- If `x` is transient under `κ`, then `(x, y)` is transient under `κ ∥ₖ η` for every `y`. Only
measurable singletons on the first coordinate space are needed. -/
theorem IsTransient.parallelComp_left [MeasurableSingletonClass α]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {x : α} (hx : κ.IsTransient x) (y : β) :
    (κ ∥ₖ η).IsTransient (x, y) :=
  isTransient_iff.mpr fun hrec => isTransient_iff.mp hx hrec.of_parallelComp_left

/-- If `y` is transient under `η`, then `(x, y)` is transient under `κ ∥ₖ η` for every `x`. Only
measurable singletons on the second coordinate space are needed. -/
theorem IsTransient.parallelComp_right [MeasurableSingletonClass β]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    (x : α) {y : β} (hy : η.IsTransient y) :
    (κ ∥ₖ η).IsTransient (x, y) :=
  isTransient_iff.mpr fun hrec => isTransient_iff.mp hy hrec.of_parallelComp_right

/-- Returning to `z` requires returning to `z.1`, so the first-coordinate mean return time never
exceeds the joint mean return time when `α` has measurable singletons. -/
theorem meanReturnTime_le_parallelComp_left [MeasurableSingletonClass α]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] (z : α × β) :
    κ.meanReturnTime z.1 ≤ (κ ∥ₖ η).meanReturnTime z :=
  meanReturnTime_le_of_map_eq measurable_fst (fun p => by simp [parallelComp_apply]) z

/-- Returning to `z` requires returning to `z.2`, so the second-coordinate mean return time never
exceeds the joint mean return time when `β` has measurable singletons. -/
theorem meanReturnTime_le_parallelComp_right [MeasurableSingletonClass β]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] (z : α × β) :
    η.meanReturnTime z.2 ≤ (κ ∥ₖ η).meanReturnTime z :=
  meanReturnTime_le_of_map_eq measurable_snd (fun p => by simp [parallelComp_apply]) z

/-- Positive recurrence of `z` under `κ ∥ₖ η` implies positive recurrence of `z.1` under `κ` when
`α` has measurable singletons. -/
theorem IsPositiveRecurrent.of_parallelComp_left [MeasurableSingletonClass α]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {z : α × β} (hz : (κ ∥ₖ η).IsPositiveRecurrent z) :
    κ.IsPositiveRecurrent z.1 :=
  (isPositiveRecurrent_iff _ _).mpr
    ((meanReturnTime_le_parallelComp_left κ η z).trans_lt hz.meanReturnTime_lt_top)

/-- Positive recurrence of `z` under `κ ∥ₖ η` implies positive recurrence of `z.2` under `η` when
`β` has measurable singletons. -/
theorem IsPositiveRecurrent.of_parallelComp_right [MeasurableSingletonClass β]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {z : α × β} (hz : (κ ∥ₖ η).IsPositiveRecurrent z) :
    η.IsPositiveRecurrent z.2 :=
  (isPositiveRecurrent_iff _ _).mpr
    ((meanReturnTime_le_parallelComp_right κ η z).trans_lt hz.meanReturnTime_lt_top)

/-- **Upper bound on the product cycle occupation measure.** For any Markov kernels `κ` and `η` on
spaces with measurable singletons and any state `z`,
`(κ ∥ₖ η).cycleOccupation z ≤ (κ.cycleOccupation z.1).prod (η.cycleOccupation z.2)`, without any
irreducibility, recurrence, or countability assumption. -/
theorem cycleOccupation_parallelComp_le [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] (z : α × β) :
    (κ ∥ₖ η).cycleOccupation z ≤ (κ.cycleOccupation z.1).prod (η.cycleOccupation z.2) := by
  -- The product of the marginal cycle occupation measures is `(κ ∥ₖ η)`-superharmonic and has
  -- unit mass at `{z}`, so minimality of `cycleOccupation` gives the domination.
  have hsub : (κ ∥ₖ η) ∘ₘ ((κ.cycleOccupation z.1).prod (η.cycleOccupation z.2)) ≤
      (κ.cycleOccupation z.1).prod (η.cycleOccupation z.2) := by
    rw [Measure.parallelComp_comp_prod]
    exact Measure.prod_mono (κ.comp_cycleOccupation_le z.1) (η.comp_cycleOccupation_le z.2)
  have hz : ((κ.cycleOccupation z.1).prod (η.cycleOccupation z.2)) {z} = 1 := by
    rw [← Prod.eta z, ← Set.singleton_prod_singleton, Measure.prod_prod,
      cycleOccupation_singleton_self, cycleOccupation_singleton_self, one_mul]
  simpa [hz] using smul_cycleOccupation_le_of_comp_le hsub z

/-- **Upper bound on the product mean return time.** For any Markov kernels `κ` and `η` on spaces
with measurable singletons and any state `z`,
`(κ ∥ₖ η).meanReturnTime z ≤ κ.meanReturnTime z.1 * η.meanReturnTime z.2`. -/
theorem meanReturnTime_parallelComp_le [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] (z : α × β) :
    (κ ∥ₖ η).meanReturnTime z ≤ κ.meanReturnTime z.1 * η.meanReturnTime z.2 := by
  calc (κ ∥ₖ η).meanReturnTime z
    _ = (κ ∥ₖ η).cycleOccupation z Set.univ := (cycleOccupation_univ _ _).symm
    _ ≤ ((κ.cycleOccupation z.1).prod (η.cycleOccupation z.2)) Set.univ :=
      (cycleOccupation_parallelComp_le κ η z) Set.univ
    _ = κ.meanReturnTime z.1 * η.meanReturnTime z.2 := by
      rw [← Set.univ_prod_univ, Measure.prod_prod, cycleOccupation_univ, cycleOccupation_univ]

/-- On spaces with measurable singletons, `(x, y)` is positive recurrent under `κ ∥ₖ η` whenever
`x` is positive recurrent under `κ` and `y` is positive recurrent under `η`, with no
irreducibility, aperiodicity, or countability assumption. -/
theorem IsPositiveRecurrent.parallelComp [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    {κ : Kernel α α} {η : Kernel β β} [IsMarkovKernel κ] [IsMarkovKernel η]
    {x : α} {y : β} (hx : κ.IsPositiveRecurrent x) (hy : η.IsPositiveRecurrent y) :
    (κ ∥ₖ η).IsPositiveRecurrent (x, y) :=
  (isPositiveRecurrent_iff _ _).mpr <|
    (meanReturnTime_parallelComp_le κ η (x, y)).trans_lt
      (ENNReal.mul_lt_top hx.meanReturnTime_lt_top hy.meanReturnTime_lt_top)

/-- **Characterization of positive recurrence in an independent product chain.** On spaces with
measurable singletons, a pair `z` is positive recurrent under `κ ∥ₖ η` if and only if both
coordinates are positive recurrent under their respective kernels, without any irreducibility,
aperiodicity, or countability assumption. -/
@[simp]
theorem isPositiveRecurrent_parallelComp_iff
    [MeasurableSingletonClass α] [MeasurableSingletonClass β]
    (κ : Kernel α α) (η : Kernel β β) [IsMarkovKernel κ] [IsMarkovKernel η] (z : α × β) :
    (κ ∥ₖ η).IsPositiveRecurrent z ↔ κ.IsPositiveRecurrent z.1 ∧ η.IsPositiveRecurrent z.2 :=
  ⟨fun hz => ⟨hz.of_parallelComp_left, hz.of_parallelComp_right⟩,
    fun ⟨hx, hy⟩ => hx.parallelComp hy⟩

end ProbabilityTheory.Kernel
