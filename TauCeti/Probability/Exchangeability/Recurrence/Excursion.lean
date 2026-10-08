/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Excursion.Basic
public import TauCeti.Probability.Exchangeability.Excursion
public import TauCeti.Probability.Recurrent.Basic
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Exchangeability of excursions

For a recurrent Markov exchangeable process started at `a₀`, the excursion process is
exchangeable. Prescribing its first excursions is a finite-path event; reordering the
excursions preserves the initial state and transition counts of that path, hence its mass.
The measurable excursion process and the event identity live in
`TauCeti.Probability.Process.Excursion.Basic`.

Recurrence makes the event comparison two-way. The deterministic absorbed walk in
`TauCeti.Probability.Exchangeability.Recurrence.AbsorbedWalk` shows that Markov
exchangeability alone does not ensure recurrence. De Finetti's theorem can then be applied
to the exchangeable excursion process, as in
`TauCeti.Probability.Exchangeability.Recurrence.Representation`.

## Main results

* `TauCeti.Probability.MarkovExchangeable.measure_setOf_excursionPrefix_eq_of_perm`: reordering a
  list of excursions does not change its probability.
* `TauCeti.Probability.MarkovExchangeable.exchangeable_excursionProcess`: the excursions of a
  recurrent Markov exchangeable process are exchangeable.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {a₀ : α}

/-- **Reordering a list of excursions does not change the probability that a recurrent Markov
exchangeable process traverses it.** No hypothesis on the list is needed: excursions never visit
the base state, so if some entry of `bs` does, both events are empty. -/
theorem MarkovExchangeable.measure_setOf_excursionPrefix_eq_of_perm (h : MarkovExchangeable μ X)
    (hrec : Recurrent μ X) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) {bs bs' : List (List α)}
    (hperm : bs.Perm bs') :
    μ {ω | excursionPrefix (fun n => X n ω) a₀ bs.length = bs} =
      μ {ω | excursionPrefix (fun n => X n ω) a₀ bs'.length = bs'} := by
  by_cases havoid : ∀ e ∈ bs, a₀ ∉ e
  · have hvisit : ∀ cs : List (List α),
        ∀ᵐ ω ∂μ, ∃ n, X n ω = a₀ ∧ visitCount (fun n => X n ω) a₀ n = cs.length := by
      intro cs
      filter_upwards [h0, hrec.ae_infinite_setOf_eq] with ω hω0 hωinf
      have hinf := hωinf 0
      rw [hω0] at hinf
      exact exists_visitCount_of_infinite hinf cs.length
    have havoid' : ∀ e ∈ bs', a₀ ∉ e := fun e he => havoid e (hperm.mem_iff.2 he)
    rw [measure_setOf_excursionPrefix_eq (hvisit bs) h0 havoid,
      measure_setOf_excursionPrefix_eq (hvisit bs') h0 havoid',
      ← loopSteps_eq_of_perm hperm]
    exact h.measure_setOf_loopPathAt_eq_of_perm a₀ hperm rfl
  · -- A list with an entry through the base state is nobody's list of excursions.
    have hempty : ∀ cs : List (List α), ¬(∀ e ∈ cs, a₀ ∉ e) →
        μ {ω | excursionPrefix (fun n => X n ω) a₀ cs.length = cs} = 0 := by
      intro cs hcs
      convert measure_empty (μ := μ)
      refine Set.eq_empty_of_forall_notMem fun ω hω => hcs ?_
      rw [← hω]
      exact forall_not_mem_excursionPrefix _ a₀ cs.length
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

/-- **The excursion process of a recurrent Markov exchangeable process is exchangeable.**

This is the half of the Diaconis–Freedman representation theorem that consumes the recurrence
hypothesis. Its finite-dimensional laws are permutation invariant because each of them is the mass
of a finite path, and reordering the excursions of a path preserves both its initial state and its
transition counts — the sufficient statistic Markov exchangeability sees. -/
theorem MarkovExchangeable.exchangeable_excursionProcess (h : MarkovExchangeable μ X)
    (hrec : Recurrent μ X) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀) :
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
  exact h.measure_setOf_excursionPrefix_eq_of_perm hrec h0
    (Equiv.Perm.ofFn_comp_perm σ.symm v)

end Exchangeable

end Probability

end TauCeti

end

end
