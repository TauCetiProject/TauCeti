/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.MarkovExchangeable
public import TauCeti.Probability.Exchangeability.MixedIID.Basic
public import TauCeti.Probability.Process.MixedMarkovChain

/-!
# Mixtures of Markov chains are Markov exchangeable

A mixture of Markov chains (`MixedMarkovChainWith` / `MixedMarkovChain`, from
`TauCeti.Probability.Process.MixedMarkovChain`) is the class in the conclusion of the
Diaconis–Freedman representation theorem: a recurrent Markov exchangeable process is a mixture of
Markov chains. This file places that class in the symmetry lattice. It supplies the **easy
direction** of the theorem, `MixedMarkovChainWith.markovExchangeable`: every mixture of Markov
chains is Markov exchangeable. The mechanism is the one that makes the initial state together with
the transition counts sufficient for a Markov-chain path mass — the transition-product factor
depends on the path only through its transition counts (`TauCeti.prod_eq_of_transitionCount_eq`) —
applied inside the mixing integral, where it holds pointwise in the mixing variable.

The naming and the witness/existential split of the mixture class follow `MixedIIDWith` /
`MixedIID`, and the class contains mixed i.i.d. processes: an i.i.d. mixture is the mixture of
Markov chains whose rows do not depend on the current state (`MixedIIDWith.mixedMarkovChainWith`).
The class is strictly larger than the mixed i.i.d. one: the deterministic 3-cycle of
`TauCeti/Probability/Exchangeability/ThreeCycle.lean` is a Markov chain, hence a mixture of Markov
chains (`threeCycle_mixedMarkovChain`), but is not exchangeable and so not mixed i.i.d.

## Main results

* `TauCeti.Probability.MixedMarkovChainWith.markovExchangeable`: a mixture of Markov chains is
  Markov exchangeable — the easy direction of Diaconis–Freedman.
* `TauCeti.Probability.MixedIIDWith.mixedMarkovChainWith`: a mixed i.i.d. process is a mixture of
  Markov chains with state-independent rows.
* `TauCeti.Probability.markovChainLaw_markovExchangeable`: a homogeneous Markov chain is Markov
  exchangeable, which makes `MarkovExchangeable` non-vacuous at an arbitrary transition kernel.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable rather than
Markov exchangeable sequences.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **A mixture of Markov chains is Markov exchangeable.** This is the easy direction of the
Diaconis–Freedman representation theorem. Two paths with a common start and common transition
counts have equal Markov-chain probabilities for *every* value of the mixing variable, because a
product of transition weights depends on the path only through its transition counts; integration
against `μ` preserves the equality. -/
theorem MixedMarkovChainWith.markovExchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure α} {κ : Ω → α → ProbabilityMeasure α}
    (h : MixedMarkovChainWith μ X ν κ) : MarkovExchangeable μ X := by
  have := h.countable
  have := h.measurableSingletonClass
  refine MarkovExchangeable.intro h.aemeasurable ?_
  intro n u v h0 hcount
  rw [h.prefixLaw_singleton_eq_lintegral n u, h.prefixLaw_singleton_eq_lintegral n v]
  refine lintegral_congr fun ω => ?_
  rw [h0, prod_eq_of_transitionCount_eq hcount fun a b => (κ ω a : Measure α) {b}]

/-- **A mixture of Markov chains is Markov exchangeable**, existential form. -/
theorem MixedMarkovChain.markovExchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : MixedMarkovChain μ X) : MarkovExchangeable μ X := by
  obtain ⟨_, _, h⟩ := h.exists_witnesses
  exact h.markovExchangeable

/-- **A mixed i.i.d. process is a mixture of Markov chains** whose rows do not depend on the
current state: drawing the next coordinate from the mixing representative, whatever the present
one, reproduces the mixed i.i.d. finite-dimensional laws. Thus this places `MixedIID` below
`MixedMarkovChain` in the symmetry lattice, refining `Exchangeable.markovExchangeable` at the
level of the representations. -/
theorem MixedIIDWith.mixedMarkovChainWith [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}
    (h : MixedIIDWith μ X ν) : MixedMarkovChainWith μ X ν fun ω _ => ν ω := by
  refine MixedMarkovChainWith.intro h.aemeasurable h.measurable_mixingRepresentative
    (fun _ => h.measurable_mixingRepresentative) fun n w => ?_
  rw [prefixLaw_def, ← Set.univ_pi_singleton w,
    h.blockLaw_univ_pi (fun i : Fin (n + 1) => i.val) Fin.val_injective (fun i => {w i})
      fun i => measurableSet_singleton (w i)]
  exact lintegral_congr fun ω => Fin.prod_univ_succ fun i => (ν ω : Measure α) {w i}

/-- **A mixed i.i.d. process is a mixture of Markov chains**, existential form. -/
theorem MixedIID.mixedMarkovChain [Countable α] [MeasurableSingletonClass α]
    {μ : Measure Ω} {X : ℕ → Ω → α} (h : MixedIID μ X) : MixedMarkovChain μ X := by
  obtain ⟨ν, hν⟩ := h.exists_mixingRepresentative
  exact MixedMarkovChain.of_witnesses hν.mixedMarkovChainWith

section MarkovChain

open ProbabilityTheory

variable (ν : Measure α) [IsProbabilityMeasure ν] (κ : Kernel α α) [IsMarkovKernel κ]

/-- **A homogeneous Markov chain is Markov exchangeable.** Its finite path masses factor as an
initial weight times a product of transition weights, and such a product depends on the path only
through its first state and its transition counts. -/
theorem markovChainLaw_markovExchangeable [Countable α] [MeasurableSingletonClass α] :
    MarkovExchangeable (markovChainLaw ν κ) fun i x => x i :=
  markovExchangeable_of_prefixLaw_singleton_eq
    (fun i => (measurable_pi_apply i).aemeasurable) (fun a => ν {a}) (fun a b => κ a {b})
    (MeasureTheory.Measure.markovChainLaw_prefixLaw_singleton ν κ)

end MarkovChain

end Probability

end TauCeti

end

end
