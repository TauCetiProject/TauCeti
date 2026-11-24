/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Basic cardinality and stabilizer properties of alternating groups

This file records two general facts about `alternatingGroup α` for a finite type `α`:

* `TauCeti.card_alternatingGroup_of_card_eq_three`: when `Nat.card α = 3`, `alternatingGroup α`
  has cardinality `3`, parallel to Mathlib's `alternatingGroup.card_of_card_eq_four`.
* `TauCeti.eq_of_forall_mem_stabilizer_alternatingGroup_smul_eq`: for `4 ≤ Nat.card α`, `a` is
  the unique fixed point of `MulAction.stabilizer (alternatingGroup α) a`, deduced from
  `(Nat.card α - 2)`-pretransitivity of `alternatingGroup α`
  (`alternatingGroup.isMultiplyPretransitive`).
-/

public section

namespace TauCeti

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- When `Nat.card α = 3`, the alternating group `alternatingGroup α` has order `3`. -/
theorem card_alternatingGroup_of_card_eq_three (hα3 : Nat.card α = 3) :
    Nat.card (alternatingGroup α) = 3 := by
  have : Nontrivial α := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  rw [nat_card_alternatingGroup, hα3]
  decide

/-- For `4 ≤ Nat.card α`, `a` is the unique fixed point of
`MulAction.stabilizer (alternatingGroup α) a`: since `alternatingGroup α` acts `2`-transitively
on `α`, for any `b ≠ a` some element fixing `a` moves `b`. -/
theorem eq_of_forall_mem_stabilizer_alternatingGroup_smul_eq (hα : 4 ≤ Nat.card α) {a b : α}
    (hb : ∀ g ∈ MulAction.stabilizer (alternatingGroup α) a, g • b = b) : b = a := by
  by_contra hba
  have hc_lt : ({a, b} : Finset α).card < (Finset.univ : Finset α).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact (Finset.card_le_two (a := a) (b := b)).trans_lt (by omega)
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card hc_lt
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  have : MulAction.IsMultiplyPretransitive (alternatingGroup α) α (Nat.card α - 2) :=
    alternatingGroup.isMultiplyPretransitive α
  have h2 : MulAction.IsMultiplyPretransitive (alternatingGroup α) α 2 :=
    MulAction.isMultiplyPretransitive_of_le (n := Nat.card α - 2) (by omega) (Nat.sub_le _ _)
  obtain ⟨g, hga, hgb⟩ := MulAction.is_two_pretransitive_iff.mp h2 (Ne.symm hba) (Ne.symm hc.1)
  exact hc.2 ((hb g (MulAction.mem_stabilizer_iff.mpr hga)).symm.trans hgb).symm

end TauCeti
