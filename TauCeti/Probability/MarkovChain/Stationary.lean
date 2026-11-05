/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Kernel.Invariance
public import TauCeti.Probability.MarkovChain.MarkovProperty
public import TauCeti.Probability.Process.PathLaw.ProcessShift

/-!
# Stationary Markov path laws

A homogeneous chain started from a finite invariant measure has a shift-invariant path law.
Conversely, shift invariance of its path law forces invariance of the initial measure, by
comparing the time-zero and time-one marginals. Thus kernel invariance characterizes
stationarity of the entire process, not just equality of its one-time marginals.

The result transfers to any realization of the chain: shifting its random path by any
number of steps preserves its law. Together with invariance of product measures for parallel
kernels, this gives stationary independent product chains. Stationarity here does not assert
convergence to equilibrium. No countability, irreducibility, aperiodicity, or probability
normalization is required.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.7.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.Probability

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] {κ : Kernel α α} [IsMarkovKernel κ]
  {ν : Measure α} [IsFiniteMeasure ν]

/-- Starting a homogeneous chain from an invariant finite measure makes the one-sided
path shift measure preserving. -/
theorem Invariant.measurePreserving_shift_markovChainLaw (hν : κ.Invariant ν) :
    MeasurePreserving (shift α) (markovChainLaw ν κ) (markovChainLaw ν κ) := by
  refine ⟨measurable_shift, ?_⟩
  simpa only [Function.iterate_one, pow_one, hν.def] using
    ν.markovChainLaw_map_shift_iterate κ 1

end ProbabilityTheory.Kernel

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α]

/-- The path law of a homogeneous chain with a finite initial measure is stationary exactly
when that initial measure is invariant for the transition kernel. -/
theorem measurePreserving_shift_markovChainLaw_iff (ν : Measure α) [IsFiniteMeasure ν]
    (κ : Kernel α α) [IsMarkovKernel κ] :
    MeasurePreserving (shift α) (markovChainLaw ν κ) (markovChainLaw ν κ) ↔ κ.Invariant ν := by
  refine ⟨fun h => ?_, Kernel.Invariant.measurePreserving_shift_markovChainLaw⟩
  have hzero := congrArg (fun ρ : Measure (ℕ → α) => ρ.map (fun x => x 0)) h.map_eq
  rw [Measure.map_map (measurable_pi_apply 0) measurable_shift] at hzero
  rw [Kernel.Invariant]
  simpa only [Function.comp_def, shift_apply, zero_add,
    markovChainLaw_map_eval_succ, pow_one, markovChainLaw_map_eval_zero] using hzero

end MeasureTheory.Measure

namespace ProbabilityTheory.HasLaw

variable {α Ω : Type*} [MeasurableSpace α] [MeasurableSpace Ω]
  {κ : Kernel α α} [IsMarkovKernel κ] {ν : Measure α} [IsFiniteMeasure ν]
  {P : Measure Ω} {X : ℕ → Ω → α}

/-- Every time shift of an arbitrary realization of a chain started from an invariant finite
measure has the original full path law. -/
theorem processShift_markovChainLaw
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    (hν : κ.Invariant ν) (n : ℕ) :
    HasLaw (processShift X n) (markovChainLaw ν κ) P := by
  rw [processShift_eq_shift_iterate]
  exact ((hν.measurePreserving_shift_markovChainLaw.iterate n).hasLaw).fun_comp hX

end ProbabilityTheory.HasLaw
