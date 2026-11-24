/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Excursion.Basic
public import TauCeti.Probability.Process.Excursion.MarkovChain
public import TauCeti.Probability.Exchangeability.ConditionallyIID.Const
public import TauCeti.Probability.Exchangeability.Excursion
public import TauCeti.Probability.Recurrent.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic
-- Non-public: recurrence of exchangeable processes is used only inside a proof.
import TauCeti.Probability.Exchangeability.Recurrence.Basic

/-!
# Exchangeability of excursions

For a Markov exchangeable process started at `a₀` that returns to `a₀` infinitely often, the
excursion process is exchangeable. Prescribing its first excursions is a finite-path event;
reordering the excursions preserves the initial state and transition counts of that path, hence
its mass. The measurable excursion process and the event identity live in
`TauCeti.Probability.Process.Excursion.Basic`.

The returns to `a₀` make the event comparison two-way. The deterministic absorbed walk in
`TauCeti.Probability.Exchangeability.Recurrence.AbsorbedWalk` shows that Markov
exchangeability alone does not ensure them. De Finetti's theorem can then be applied
to the exchangeable excursion process, as in
`TauCeti.Probability.Exchangeability.Recurrence.Representation`.

Returning to the initial state infinitely often is the recurrence hypothesis of the
Diaconis–Freedman theorem. For a Markov exchangeable process under a finite measure, started at a
fixed state, it implies recurrence in the sense of `TauCeti.Probability.Recurrent`, that every
state the process visits is visited infinitely often
(`TauCeti.Probability.MarkovExchangeable.recurrent_of_ae_initial_eq`).

For a recurrent Markov chain itself the excursions are not merely exchangeable but i.i.d.
(`TauCeti.Probability.Process.Excursion.MarkovChain`); in the language of de Finetti's theorem,
their directing measure is the constant excursion law.

## Main results

* `TauCeti.Probability.MarkovExchangeable.measure_setOf_excursionPrefix_eq_of_perm`: reordering a
  list of excursions does not change its probability.
* `TauCeti.Probability.MarkovExchangeable.exchangeable_excursionProcess`: the excursions of a
  Markov exchangeable process that returns to its initial state infinitely often are exchangeable.
* `TauCeti.Probability.MarkovExchangeable.recurrent_of_ae_initial_eq`: under a finite measure, a
  Markov exchangeable process started at a fixed state and returning to it infinitely often visits
  each of its states infinitely often.
* `TauCeti.Probability.conditionallyIIDWith_excursionProcess`: the excursions of a recurrent
  Markov chain are conditionally i.i.d. with the constant excursion law as directing measure.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* N. Halberstam and T. Hutchcroft, "Proof of the Diaconis–Freedman conjecture on
  partially-exchangeable processes", arXiv:2405.20276 (2024), §1, which restates the
  Diaconis–Freedman theorem with recurrence meaning return to the starting state infinitely often.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {a₀ : α}

/-- **Reordering a list of excursions does not change the probability that a Markov exchangeable
process traverses it**, when the process starts at `a₀` and returns to `a₀` infinitely often. No
hypothesis on the list is needed: excursions never visit the base state, so if some entry of `bs`
does, both events are empty. -/
theorem MarkovExchangeable.measure_setOf_excursionPrefix_eq_of_perm (h : MarkovExchangeable μ X)
    (hret : ∀ᵐ ω ∂μ, {n | X n ω = a₀}.Infinite) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀)
    {bs bs' : List (List α)} (hperm : bs.Perm bs') :
    μ {ω | excursionPrefix (fun n => X n ω) a₀ bs.length = bs} =
      μ {ω | excursionPrefix (fun n => X n ω) a₀ bs'.length = bs'} := by
  by_cases havoid : ∀ e ∈ bs, a₀ ∉ e
  · have hvisit : ∀ cs : List (List α),
        ∀ᵐ ω ∂μ, ∃ n, X n ω = a₀ ∧ visitCount (fun n => X n ω) a₀ n = cs.length := fun cs =>
      hret.mono fun _ hω => exists_visitCount_of_infinite hω cs.length
    have havoid' : ∀ e ∈ bs', a₀ ∉ e := fun e he => havoid e (hperm.mem_iff.2 he)
    rw [measure_setOf_excursionPrefix_eq (hvisit bs) h0 havoid,
      measure_setOf_excursionPrefix_eq (hvisit bs') h0 havoid',
      ← loopSteps_eq_of_perm hperm]
    exact h.measure_setOf_loopPathAt_eq_of_perm a₀ hperm rfl
  · -- A list with an entry through the base state is nobody's list of excursions.
    have hempty : ∀ cs : List (List α), ¬(∀ e ∈ cs, a₀ ∉ e) →
        μ {ω | excursionPrefix (fun n => X n ω) a₀ cs.length = cs} = 0 := by
      intro cs hcs
      have hset : {ω | excursionPrefix (fun n => X n ω) a₀ cs.length = cs} = ∅ :=
        Set.eq_empty_of_forall_notMem fun ω hω => hcs (by
          rw [← Set.mem_ofPred.mp hω]
          exact forall_not_mem_excursionPrefix _ a₀ cs.length)
      rw [hset, measure_empty]
    rw [hempty bs havoid,
      hempty bs' fun hbs' => havoid fun e he => hbs' e (hperm.mem_iff.mp he)]

/-! ## Exchangeability of the excursion process -/

section Exchangeable

omit [MeasurableSpace Ω] [MeasurableSpace α] in
/-- A finite-dimensional event of the excursion process, read as an event of the excursion
prefix. -/
private theorem setOf_forall_excursion_eq {m : ℕ} (v : Fin m → List α) :
    {ω | ∀ i : Fin m, excursionProcess X a₀ i.val ω = v i} =
      {ω | excursionPrefix (fun n => X n ω) a₀ (List.ofFn v).length = List.ofFn v} := by
  ext ω
  simp only [Set.mem_ofPred_eq, excursionProcess_apply, List.length_ofFn]
  constructor
  · intro hv
    refine List.ext_getElem (by simp) fun j hj hj' => ?_
    have hjm : j < m := by simpa using hj
    rw [List.getElem_ofFn, getElem_excursionPrefix hjm]
    exact hv ⟨j, hjm⟩
  · intro hv i
    have hi : i.val < (excursionPrefix (fun n => X n ω) a₀ m).length := by simp
    simpa using List.getElem_of_eq hv hi

/-- **The excursion process of a Markov exchangeable process is exchangeable**, when the process
starts at `a₀` and returns to `a₀` infinitely often.

Its finite-dimensional laws are permutation invariant because each of them is the mass of a finite
path, and reordering the excursions of a path preserves both its initial state and its transition
counts — the sufficient statistic Markov exchangeability sees. -/
theorem MarkovExchangeable.exchangeable_excursionProcess (h : MarkovExchangeable μ X)
    (hret : ∀ᵐ ω ∂μ, {n | X n ω = a₀}.Infinite) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
    Exchangeable μ (excursionProcess X a₀) := by
  let _ : Countable α := h.countable
  have : MeasurableSingletonClass α := h.measurableSingletonClass
  have hmeas : ∀ k, AEMeasurable (excursionProcess X a₀ k) μ :=
    aemeasurable_excursionProcess h.aemeasurable a₀ (measurableSet_singleton a₀)
  intro m σ
  refine Measure.ext_of_singleton fun v => ?_
  rw [prefixLaw_def,
    blockLaw_apply_of_measurable _ _ _ (fun i => hmeas _) (measurableSet_singleton v),
    blockLaw_apply_of_measurable _ _ _ (fun i => hmeas _) (measurableSet_singleton v)]
  -- Both singleton masses are excursion-prefix events, at lists differing by the permutation.
  have hleft : (fun ω i => excursionProcess X a₀ (σ i).val ω) ⁻¹' {v} =
      {ω | ∀ i : Fin m, excursionProcess X a₀ i.val ω = v (σ.symm i)} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff]
    exact ⟨fun hv i => by simpa using hv (σ.symm i), fun hv i => by simpa using hv (σ i)⟩
  have hright : (fun ω i => excursionProcess X a₀ i.val ω) ⁻¹' {v} =
      {ω | ∀ i : Fin m, excursionProcess X a₀ i.val ω = v i} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff]
  rw [hleft, hright, setOf_forall_excursion_eq, setOf_forall_excursion_eq]
  exact h.measure_setOf_excursionPrefix_eq_of_perm hret h0
    (Equiv.Perm.ofFn_comp_perm σ.symm v)

end Exchangeable

/-! ## Recurrence from returns to the initial state -/

/-- **A Markov exchangeable process that returns to its initial state infinitely often is
recurrent.** Under a finite measure, if the process starts at `a₀` and returns to `a₀` infinitely
often almost surely, then almost surely it visits each of its states infinitely often. The
hypothesis is the recurrence hypothesis of the Diaconis–Freedman theorem; the conclusion is
`TauCeti.Probability.Recurrent`, which asks this of every visited state. -/
theorem MarkovExchangeable.recurrent_of_ae_initial_eq [IsFiniteMeasure μ]
    (h : MarkovExchangeable μ X) (hret : ∀ᵐ ω ∂μ, {n | X n ω = a₀}.Infinite)
    (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) : Recurrent μ X := by
  let _ : Countable α := h.countable
  have : MeasurableSingletonClass α := h.measurableSingletonClass
  -- The excursions are exchangeable finite words, so by Poincaré recurrence each of them almost
  -- surely recurs infinitely often, and with it every state it visits.
  have hexc := ((h.exchangeable_excursionProcess hret h0).recurrent
    (aemeasurable_excursionProcess h.aemeasurable a₀
      (measurableSet_singleton a₀))).ae_infinite_setOf_eq
  rw [recurrent_def]
  filter_upwards [hret, h0, hexc] with ω hω hω0 hωexc k
  exact Nat.frequently_atTop_iff_infinite.2
    (infinite_setOf_eq_of_forall_infinite_setOf_excursion_eq hω hω0
      (fun j => by simpa only [excursionProcess_apply] using hωexc j) k)

/-! ## The excursions of a recurrent Markov chain -/

/-- **The excursions of a recurrent Markov chain are i.i.d.**: independent, and each distributed as
the first excursion. The constant directing measure is the excursion law, so this is genuine
independence and not only a mixture identity. -/
theorem conditionallyIIDWith_excursionProcess [Countable α] [MeasurableSingletonClass α]
    {κ : ProbabilityTheory.Kernel α α} [ProbabilityTheory.IsMarkovKernel κ]
    (hret : ∀ᵐ x ∂(markovChainLaw (Measure.dirac a₀) κ), {n | x n = a₀}.Infinite) :
    ConditionallyIIDWith (markovChainLaw (Measure.dirac a₀) κ)
      (excursionProcess (fun n (x : ℕ → α) => x n) a₀)
      (fun _ => ⟨excursionLaw κ a₀, isProbabilityMeasure_excursionLaw⟩) :=
  conditionallyIIDWith_const_iff_iIndepFun_and_map_eq.2
    ⟨aemeasurable_excursionProcess (fun i => (measurable_pi_apply i).aemeasurable) a₀
        (measurableSet_singleton a₀),
      iIndepFun_excursionProcess hret,
      fun k => map_excursionProcess_eq_excursionLaw k
        (hret.mono fun _ hx => exists_visitCount_of_infinite hx (k + 1))⟩

end Probability

end TauCeti

end

end
