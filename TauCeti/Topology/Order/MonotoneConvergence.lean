/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Monotone convergence on a closed half-line

A function that is monotone and bounded above on a closed half-line `[a, ∞)` tends at infinity to
its supremum over that half-line, and dually for antitone functions bounded below. These are the
half-line forms of Mathlib's `tendsto_atTop_ciSup` and `tendsto_atTop_ciInf`, which ask for
monotonicity on the whole domain. They apply, for instance, to a quantity monotone along a
trajectory that is only defined, or only monotone, in forward time.

## Main results

* `TauCeti.tendsto_atTop_ciSup_of_monotoneOn_Ici` — a function monotone and bounded above on
  `[a, ∞)` tends to its supremum there.
* `TauCeti.tendsto_atTop_ciInf_of_antitoneOn_Ici` — a function antitone and bounded below on
  `[a, ∞)` tends to its infimum there.
* `TauCeti.exists_tendsto_of_monotoneOn_Ici_of_sum_le` — each member of a finite family of
  functions monotone on `[a, ∞)` whose sum is bounded above there converges.
-/

public section

open Filter Set Topology

namespace TauCeti

variable {ι α : Type*} [Preorder ι] [TopologicalSpace α] {f : ι → α} {a : ι}

/-- **Monotone convergence on a half-line.** A function monotone and bounded above on `[a, ∞)`
tends at infinity to its supremum over `[a, ∞)`. -/
theorem tendsto_atTop_ciSup_of_monotoneOn_Ici [ConditionallyCompletePartialOrderSup α]
    [SupConvergenceClass α] (hf : MonotoneOn f (Ici a)) (hbdd : BddAbove (f '' Ici a)) :
    Tendsto f atTop (𝓝 (⨆ t : Ici a, f t)) := by
  by_cases h : (atTop : Filter ι).NeBot
  · have := (atTop_neBot_iff.1 h).2
    exact tendsto_comp_val_Ici_atTop.mp <|
      tendsto_atTop_ciSup (fun s t hst ↦ hf s.2 t.2 hst) (by rwa [← image_eq_range])
  · rw [not_neBot.1 h]
    exact tendsto_bot

/-- **Antitone convergence on a half-line.** A function antitone and bounded below on `[a, ∞)`
tends at infinity to its infimum over `[a, ∞)`. -/
theorem tendsto_atTop_ciInf_of_antitoneOn_Ici [ConditionallyCompletePartialOrderInf α]
    [InfConvergenceClass α] (hf : AntitoneOn f (Ici a)) (hbdd : BddBelow (f '' Ici a)) :
    Tendsto f atTop (𝓝 (⨅ t : Ici a, f t)) := by
  by_cases h : (atTop : Filter ι).NeBot
  · have := (atTop_neBot_iff.1 h).2
    exact tendsto_comp_val_Ici_atTop.mp <|
      tendsto_atTop_ciInf (fun s t hst ↦ hf s.2 t.2 hst) (by rwa [← image_eq_range])
  · rw [not_neBot.1 h]
    exact tendsto_bot

/-- **A monotone summand of a bounded sum converges.** If finitely many functions are monotone on
`[a, ∞)` and their sum is bounded above there, then each of them converges at infinity: it is
bounded above by the bound minus the values of the others at `a`. -/
theorem exists_tendsto_of_monotoneOn_Ici_of_sum_le {κ : Type*} [AddCommGroup α]
    [ConditionallyCompletePartialOrderSup α] [IsOrderedAddMonoid α] [SupConvergenceClass α]
    {s : Finset κ} {f : κ → ι → α} {M : α} (hf : ∀ i ∈ s, MonotoneOn (f i) (Ici a))
    (hM : ∀ t ∈ Ici a, ∑ i ∈ s, f i t ≤ M) {i : κ} (hi : i ∈ s) :
    ∃ l, Tendsto (f i) atTop (𝓝 l) := by
  classical
  refine ⟨_, tendsto_atTop_ciSup_of_monotoneOn_Ici (hf i hi)
    ⟨M - ∑ j ∈ s.erase i, f j a, ?_⟩⟩
  rintro _ ⟨t, ht, rfl⟩
  have hrest : ∑ j ∈ s.erase i, f j a ≤ ∑ j ∈ s.erase i, f j t :=
    Finset.sum_le_sum fun j hj ↦ hf j (Finset.mem_of_mem_erase hj) (mem_Ici.2 le_rfl) ht ht
  have h := hM t ht
  rw [← Finset.add_sum_erase _ _ hi] at h
  rw [le_sub_iff_add_le]
  exact (add_le_add_right hrest _).trans h

end TauCeti
