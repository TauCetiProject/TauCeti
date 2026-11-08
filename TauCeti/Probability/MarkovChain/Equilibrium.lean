/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Coupling.Convergence
public import TauCeti.Probability.MarkovChain.Product.Basic
public import TauCeti.Probability.MarkovChain.Transient.Occupation

/-!
# Convergence to an invariant probability

An irreducible aperiodic kernel on a countable state space converges in total variation
to any invariant probability, from every initial probability law. This also holds for
the coordinate laws of any realization of the chain on an arbitrary measurable sample
space. The theorem assumes an invariant probability, not a finite return-time mean;
constructing that probability is separate from the convergence argument.

The independent square chain has the invariant probability `π.prod π`. A positive-mass
atom of that probability is recurrent, while irreducibility and aperiodicity of the
original kernel ensure irreducibility of the square. The square-chain coupling theorem
then compares the evolving initial law with the unchanged stationary law. Aperiodicity
is essential: an invariant probability alone does not prevent periodic oscillation.

The distance is Mathlib's `MeasureTheory.tvDist`, with values in `[0, 2]` for probability
measures, rather than the normalization with values in `[0, 1]`.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §1.8,
  the independent-square meeting argument for convergence to equilibrium.
-/

public section

open MeasureTheory ProbabilityTheory Filter TauCeti.Probability
open scoped Topology

namespace ProbabilityTheory.Kernel

variable {α : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  {κ : Kernel α α} [IsMarkovKernel κ] [IsIrreducible Measure.count κ]
  {π : Measure α} [IsProbabilityMeasure π]

/-- **Convergence to equilibrium.** For an irreducible aperiodic countable-state kernel,
an invariant probability attracts every initial probability in total variation. -/
theorem Invariant.tendsto_tvDist_pow_comp (hπ : κ.Invariant π) (hκ : κ.IsAperiodic)
    (ν : Measure α) [IsProbabilityMeasure ν] :
    Tendsto (fun n : ℕ => tvDist ((κ ^ n : Kernel α α) ∘ₘ ν) π) atTop (𝓝 0) := by
  obtain ⟨x, hx⟩ : ∃ x : α, π {x} ≠ 0 := by
    by_contra h
    have hzero : π = 0 := Measure.ext_iff_singleton.mpr (fun x => by simpa using not_exists.mp h x)
    have hone : π Set.univ = 1 := measure_univ
    simp [hzero] at hone
  let := hκ.isIrreducible_parallelComp hκ
  have hrec : (κ ∥ₖ κ).IsRecurrent (x, x) :=
    (hπ.parallelComp hπ).isRecurrent_of_apply_singleton_ne_zero (by
      simpa only [← Set.singleton_prod_singleton, Measure.prod_prod] using mul_ne_zero hx hx)
  have hlim := κ.tendsto_tvDist_pow_comp_of_parallelComp_isRecurrent hrec ν π
  simpa only [hπ.pow_comp] using hlim

end ProbabilityTheory.Kernel

namespace ProbabilityTheory.HasLaw

variable {α Ω : Type*} [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
  [MeasurableSpace Ω] {P : Measure Ω} {X : ℕ → Ω → α}
  {κ : Kernel α α} [IsMarkovKernel κ] [Kernel.IsIrreducible Measure.count κ]
  {π ν : Measure α} [IsProbabilityMeasure π] [IsProbabilityMeasure ν]

/-- The coordinate laws of any realization of an irreducible aperiodic countable-state
chain converge to its invariant probability. No topology on the sample space is needed. -/
theorem tendsto_tvDist_map_of_invariant
    (hX : HasLaw (fun ω n => X n ω) (markovChainLaw ν κ) P)
    (hπ : κ.Invariant π) (hκ : κ.IsAperiodic) :
    Tendsto (fun n : ℕ => tvDist (P.map (X n)) π) atTop (𝓝 0) := by
  simpa only [(hX.eval_markovChainLaw ν κ _).map_eq] using hπ.tendsto_tvDist_pow_comp hκ ν

end ProbabilityTheory.HasLaw
