/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.DiracProba
public import TauCeti.MeasureTheory.Measure.Measurability
public import TauCeti.Probability.Exchangeability.MixedMarkovChain
public import TauCeti.Probability.Exchangeability.RowExchangeable
public import TauCeti.Probability.Exchangeability.SuccessorArray

/-!
# From a row exchangeable successor array back to a mixture of Markov chains

Diaconis and Freedman represent a recurrent Markov exchangeable process as a mixture of Markov
chains by passing to its **successor array**: the array whose `(a, k)`-entry is the state the
process moves to right after its `k`-th visit to `a`. Their argument has two halves. One half
shows that the successor array of such a process is *row exchangeable* — its law is unchanged when
the entries of each row are permuted, with a permutation chosen separately for each row. The other
half is the change of variables that turns a description of the successor array's law back into a
description of the path law. This file is the second half.

The input is `TauCeti.Probability.RowExchangeable` for an array that almost surely records the
successors of the process at the cells it consumes — the successor array itself
(`TauCeti.Probability.successorProcess`), or the visited successor array
(`TauCeti.Probability.visitedSuccessorProcess`) whose unvisited rows are constant — and the output
is `TauCeti.Probability.MixedMarkovChainWith`, with the row marginals of the array's directing
measure as the random transition matrix. The mechanism is that the finite path event
`{X i = w i, i ≤ n}` *is* an event of the array: by
`TauCeti.eqOn_iff_visitCell_of_apply_visitCell_eq_succ` it says exactly that the array takes the
prescribed values at the `n` cells the reference path `w` designates, which are cells the process
consumes, and by `TauCeti.visitCell_injective` those cells are pairwise distinct. Distinct cells of
a row exchangeable array are conditionally independent given the directing measure of its columns
(`TauCeti.Probability.RowExchangeable.measure_setOf_forall_mem_eq_lintegral_prod`), each governed by
its row's marginal, so the mass of that event is the mixture of a product of transition
probabilities — which is the defining identity of a mixture of Markov chains.

The process is assumed to start almost surely at a fixed state `a₀`, so the initial-law witness is
the Dirac measure at `a₀`. That is the form in which Diaconis and Freedman state their theorem, and
it is what the change of variables gives on its own: the array's mixture identity constrains the
array law alone, so carrying a genuinely random initial state through it would need the joint law
of the initial state and the array, not just the array's law.

This is the last step of the Diaconis–Freedman representation theorem that does not mention
recurrence. Its other half, the row exchangeability of the visited successor array of a recurrent
Markov exchangeable process, is
`TauCeti.Probability.MarkovExchangeable.rowExchangeable_visitedSuccessorProcess`.

## Main results

* `TauCeti.Probability.mixedMarkovChainWith_of_rowExchangeable`: at a named mixing representative
  for the columns of a row exchangeable array recording the successors at consumed cells, a process
  starting almost surely at `a₀` is a mixture of Markov chains with the Dirac initial law at `a₀`
  and the array's row marginals as transition matrix.
* `TauCeti.Probability.mixedMarkovChain_of_rowExchangeable`: the existential form, with de Finetti
  supplying the witness.

## References

* P. Diaconis and D. Freedman, "de Finetti's theorem for Markov chains", *Annals of Probability*
  8 (1980), 115–130.
* Roadmap: `TauCetiRoadmap/Exchangeability/README.md`, Layer 8, "Markov exchangeability".

No material is adapted from `cameronfreer/exchangeability`, which treats exchangeable rather than
Markov exchangeable sequences.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

section Representation

variable {μ : Measure Ω} {X : ℕ → Ω → α} {Y : α × ℕ → Ω → α} {a₀ : α}
  {lam : Ω → ProbabilityMeasure (α → α)}

/-- **The change of variables from a row exchangeable successor array back to the path law.** Let
`Y` be an array that almost surely records, at each cell the process consumes, the state the
process moves to next — as `TauCeti.Probability.successorProcess X` and
`TauCeti.Probability.visitedSuccessorProcess X` both do, whatever their entries elsewhere. A
process that starts almost surely at `a₀` and for which such an array is row exchangeable is a
mixture of Markov chains: the Dirac measure at `a₀` is its initial-law witness, and the row
marginals of the mixing representative of the array's columns form its transition-matrix
witness. -/
theorem mixedMarkovChainWith_of_rowExchangeable [Countable α]
    [MeasurableSingletonClass α] [IsProbabilityMeasure μ]
    (hX : ∀ i, AEMeasurable (X i) μ) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀)
    (hY : ∀ᵐ ω ∂μ, ∀ n, Y (visitCell (fun j => X j ω) n) ω = X (n + 1) ω)
    (hrow : RowExchangeable μ Y) (hlam : MixedIIDWith μ (arrayColumn Y) lam) :
    MixedMarkovChainWith μ X (fun _ => diracProba a₀) fun ω a =>
      (lam ω).map (fun x => x a) := by
  classical
  -- Taking the `a`-th row marginal is measurable in the Giry structure.
  have hmarg : ∀ a : α, Measurable fun P : ProbabilityMeasure (α → α) =>
      P.map (fun x => x a) := fun a =>
    TauCeti.MeasureTheory.measurable_probabilityMeasure_map (measurable_pi_apply a)
  refine MixedMarkovChainWith.intro hX measurable_const
    (fun a => (hmarg a).comp hlam.measurable_mixingRepresentative) ?_
  intro n w
  -- Extend the finite path to a reference sequence, so the combinatorial lemmas apply.
  obtain ⟨w', hfin⟩ : ∃ w' : ℕ → α, ∀ (j : ℕ) (hj : j < n + 1), w' j = w ⟨j, hj⟩ := by
    refine ⟨fun j => w ⟨min j n, Nat.lt_succ_of_le (Nat.min_le_right j n)⟩, fun j hj => ?_⟩
    exact congrArg w (Fin.ext (Nat.min_eq_left (Nat.lt_succ_iff.1 hj)))
  have hw0 : w' 0 = w 0 := by simpa using hfin 0 (Nat.succ_pos n)
  have hwc : ∀ t : Fin n, w' t.val = w t.castSucc := fun t => by
    rw [hfin t.val (Nat.lt_succ_of_lt t.isLt)]
    exact congrArg w (Fin.ext rfl)
  have hws : ∀ t : Fin n, w' (t.val + 1) = w t.succ := fun t => by
    rw [hfin (t.val + 1) (Nat.succ_lt_succ t.isLt)]
    exact congrArg w (Fin.ext rfl)
  -- The finite path event, read on the reference sequence.
  have hpref : prefixLaw μ X (n + 1) {w} = μ {ω | ∀ j ≤ n, X j ω = w' j} := by
    rw [prefixLaw_def, blockLaw_apply_of_measurable μ X (fun i : Fin (n + 1) => i.val)
      (fun i => hX i.val) (measurableSet_singleton w)]
    congr 1
    ext ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq, funext_iff]
    constructor
    · intro h j hj
      rw [hfin j (Nat.lt_succ_of_le hj)]
      exact h ⟨j, Nat.lt_succ_of_le hj⟩
    · intro h i
      rw [← hfin i.val i.isLt]
      exact h i.val (Nat.lt_succ_iff.1 i.isLt)
  rw [hpref]
  by_cases hstart : w 0 = a₀
  · -- The initial condition is almost surely automatic, and what is left is an array event.
    have hdirac : ((diracProba a₀ : ProbabilityMeasure α) : Measure α) {w 0} = 1 :=
      diracProba_toMeasure_apply_of_mem (by simp [hstart])
    have hae : {ω | ∀ j ≤ n, X j ω = w' j} =ᵐ[μ]
        {ω | ∀ t : Fin n, Y (visitCell w' t.val) ω ∈ ({w' (t.val + 1)} : Set α)} := by
      rw [Filter.eventuallyEqSet_iff]
      filter_upwards [h0, hY] with ω hω hYω
      simp only [Set.mem_singleton_iff]
      rw [eqOn_iff_visitCell_of_apply_visitCell_eq_succ (s := fun a k => Y (a, k) ω) hYω w' n]
      exact ⟨fun h t => h.2 t.val t.isLt,
        fun h => ⟨by rw [hω, hw0, hstart], fun j hj => h ⟨j, hj⟩⟩⟩
    rw [measure_congr hae,
      hrow.measure_setOf_forall_mem_eq_lintegral_prod hlam
        (c := fun t : Fin n => visitCell w' t.val)
        (fun s t hst => Fin.val_injective ((visitCell_injective w') hst))
        (B := fun t : Fin n => ({w' (t.val + 1)} : Set α))
        fun t => measurableSet_singleton _]
    refine lintegral_congr fun ω => ?_
    rw [hdirac, one_mul]
    refine Finset.prod_congr rfl fun t _ => ?_
    rw [ProbabilityMeasure.map_apply' (lam ω) (measurable_pi_apply (w t.castSucc)).aemeasurable
      (measurableSet_singleton (w t.succ)), ← hwc t, ← hws t, visitCell_def]
    rfl
  · -- A path with the wrong initial state is null, and so is its Dirac weight.
    have hnull : μ {ω | ∀ j ≤ n, X j ω = w' j} = 0 := by
      refine measure_mono_null ?_ (ae_iff.1 h0)
      intro ω hω hcon
      exact hstart (by rw [← hw0, ← hω 0 (Nat.zero_le n)]; exact hcon)
    have hdirac : ((diracProba a₀ : ProbabilityMeasure α) : Measure α) {w 0} = 0 := by
      rw [diracProba_toMeasure_apply]
      simp [Ne.symm hstart]
    rw [hnull]
    simp [hdirac]

/-- **The change of variables, with de Finetti supplying the mixing representative.** A process
that starts almost surely at a fixed state, and for which some almost everywhere measurable array
recording its successors at the cells it consumes is row exchangeable, is a mixture of Markov
chains. -/
theorem mixedMarkovChain_of_rowExchangeable [Countable α]
    [MeasurableSingletonClass α] [IsProbabilityMeasure μ]
    (hX : ∀ i, AEMeasurable (X i) μ) (h0 : ∀ᵐ ω ∂μ, X 0 ω = a₀)
    (hYm : ∀ p, AEMeasurable (Y p) μ)
    (hY : ∀ᵐ ω ∂μ, ∀ n, Y (visitCell (fun j => X j ω) n) ω = X (n + 1) ω)
    (hrow : RowExchangeable μ Y) :
    MixedMarkovChain μ X := by
  have : Nonempty α := ⟨a₀⟩
  obtain ⟨lam, hlam, -⟩ := hrow.exists_directing_pi_eq_prod hYm
  exact MixedMarkovChain.of_witnesses
    (mixedMarkovChainWith_of_rowExchangeable hX h0 hY hrow
      (mixedIIDWith_of_conditionallyIIDWith hlam))

end Representation

end Probability

end TauCeti

end

end
