/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.CompactlyGenerated.Basic
import Mathlib.Order.Bounds.OrderIso

/-!
# Compact elements and independent families

This file records preservation of compact elements by order isomorphisms, lattice consequences
of independence that involve compact elements and compact generation, and irredundant finite
families realizing a compact element.

## Main declarations

* `iSupIndep.finite_ne_bot_of_isCompactElement`: an independent family whose supremum
  is a compact element has only finitely many nonzero members. Compactness confines the whole
  family to a finite subfamily, and independence then forces every index outside it to be `⊥`.
  This is the compactness variant of Mathlib's
  `WellFoundedGT.finite_ne_bot_of_iSupIndep`, which instead assumes the ascending
  chain condition.
* `iSupIndep.iSup₂_inf_iSup_eq_iSup₂`: a partial supremum of an independent family
  meets the total supremum of a pointwise dominated family in its corresponding partial supremum.
* `iSupIndep.iSup₂_inf_iSup₂_eq_iSup₂_and`: two partial suprema of an independent
  family meet in the supremum over the intersection of their index predicates.
* `OrderIso.isCompactElement` and `OrderIso.isCompactElement_iff`: an order isomorphism of
  preorders preserves and reflects compactness of elements.
* `IsCompactElement.exists_fin_iSup_eq_of_sSup_eq`: a compact element that is the supremum of a set
  is the supremum of an irredundant finite family of its members.
-/

public section

/-- An order isomorphism of preorders sends compact elements to compact elements. -/
theorem OrderIso.isCompactElement {α β : Type*} [Preorder α] [Preorder β]
    (f : α ≃o β) {a : α} (ha : IsCompactElement a) : IsCompactElement (f a) := by
  intro s u hs hdir hlub hle
  obtain ⟨x, ⟨y, hy, rfl⟩, hay⟩ := ha (f.symm '' s) (f.symm u) (hs.image _)
    (hdir.mono_comp fun _ _ h ↦ f.symm.monotone h)
    (f.symm.isLUB_image'.mpr hlub) (f.le_symm_apply.mpr hle)
  exact ⟨y, hy, f.le_symm_apply.mp hay⟩

/-- An order isomorphism of preorders preserves and reflects compactness of elements. -/
@[simp]
theorem OrderIso.isCompactElement_iff {α β : Type*} [Preorder α] [Preorder β]
    (f : α ≃o β) {a : α} : IsCompactElement (f a) ↔ IsCompactElement a :=
  ⟨fun h ↦ by simpa using f.symm.isCompactElement h, f.isCompactElement⟩

/-- An independent family whose supremum is a compact element has only finitely many nonzero
members. -/
theorem iSupIndep.finite_ne_bot_of_isCompactElement {α ι : Type*} [CompleteLattice α]
    {a : ι → α} (ha : iSupIndep a)
    (hc : IsCompactElement (⨆ i, a i)) : {i | a i ≠ ⊥}.Finite := by
  obtain ⟨s, hs⟩ := hc.exists_finset_of_le_iSup a le_rfl
  refine s.finite_toSet.subset fun i hi ↦ ?_
  by_contra his
  exact hi ((ha.disjoint_biSup his).eq_bot_of_le ((le_iSup a i).trans hs))

/-- **A subfamily of an independent family truncates a dominated supremum.** If `B i ≤ A i` for
every `i` and the `A i` are independent, then the total supremum of the `B` meets the partial
supremum of the `A` over the indices satisfying `P` in exactly the partial supremum of the `B` over
those indices. -/
theorem iSupIndep.iSup₂_inf_iSup_eq_iSup₂ {α ι : Type*} [CompleteLattice α]
    [IsModularLattice α] [IsCompactlyGenerated α] {A B : ι → α}
    (hA : iSupIndep A) (hB : ∀ i, B i ≤ A i) (P : ι → Prop) :
    (⨆ (i) (_ : P i), A i) ⊓ ⨆ i, B i = ⨆ (i) (_ : P i), B i := by
  have hle : (⨆ (i) (_ : P i), B i) ≤ ⨆ (i) (_ : P i), A i := iSup₂_mono fun i _ ↦ hB i
  have hdisj : Disjoint (⨆ (i) (_ : P i), A i) (⨆ (i) (_ : ¬ P i), B i) := by
    have h₀ : Disjoint (⨆ (i) (_ : P i), A i) (⨆ (i) (_ : ¬ P i), A i) := by
      simpa only [Set.mem_ofPred_eq] using
        hA.disjoint_biSup_biSup (s := {i | P i}) (t := {i | ¬ P i})
          (Set.disjoint_left.2 fun i hi hi' ↦ hi' hi)
    exact h₀.mono_right (iSup₂_mono fun i _ ↦ hB i)
  rw [iSup_split B P, inf_comm, sup_inf_assoc_of_le _ hle, inf_comm, hdisj.eq_bot, sup_bot_eq]

/-- Two partial suprema of an independent family meet in the partial supremum selected by both
index predicates. -/
theorem iSupIndep.iSup₂_inf_iSup₂_eq_iSup₂_and {α ι : Type*} [CompleteLattice α]
    [IsModularLattice α] [IsCompactlyGenerated α] {A : ι → α}
    (hA : iSupIndep A) (P Q : ι → Prop) :
    (⨆ (i) (_ : P i), A i) ⊓ (⨆ (i) (_ : Q i), A i) =
      ⨆ (i) (_ : P i ∧ Q i), A i := by
  simpa only [iSup_and] using
    hA.iSup₂_inf_iSup_eq_iSup₂ (B := fun i ↦ ⨆ _ : Q i, A i) (fun _ ↦ iSup_le fun _ ↦ le_rfl) P

/-- **An irredundant finite family realizing a compact element.** If a compact element `a` is the
supremum of a set `s`, then `a` is the supremum of finitely many members of `s` none of which can
be omitted: a family of minimal size works. -/
theorem IsCompactElement.exists_fin_iSup_eq_of_sSup_eq {α : Type*} [CompleteLattice α] {a : α}
    (ha : IsCompactElement a) {s : Set α} (hs : sSup s = a) :
    ∃ (n : ℕ) (u : Fin n → α), (∀ i, u i ∈ s) ∧ ⨆ i, u i = a ∧
      ∀ i, ⨆ (j) (_ : j ≠ i), u j ≠ a := by
  classical
  have hex : ∃ n, ∃ u : Fin n → α, (∀ i, u i ∈ s) ∧ ⨆ i, u i = a := by
    obtain ⟨t, ht⟩ := ha.exists_finset_of_le_iSup (fun x : s ↦ x.1)
      (by rw [← sSup_eq_iSup', hs])
    refine ⟨t.card, fun i ↦ (t.equivFin.symm i).1.1, fun i ↦ (t.equivFin.symm i).1.2,
      le_antisymm (iSup_le fun i ↦ (le_sSup (t.equivFin.symm i).1.2).trans hs.le)
        (ht.trans (iSup₂_le fun x hx ↦ ?_))⟩
    exact le_iSup_of_le (t.equivFin ⟨x, hx⟩) (by simp)
  obtain ⟨hu, hsup⟩ := (Nat.find_spec hex).choose_spec
  refine ⟨Nat.find hex, _, hu, hsup, fun i hi ↦ ?_⟩
  -- Dropping the `i`-th member would give a smaller family with the same supremum.
  let e := Fintype.equivFin {j // j ≠ i}
  refine Nat.find_min hex (show Fintype.card {j // j ≠ i} < Nat.find hex from ?_)
    ⟨fun k ↦ (Nat.find_spec hex).choose (e.symm k).1, fun k ↦ hu _, ?_⟩
  · rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_unique]
    exact Nat.sub_one_lt_of_lt i.pos
  · refine Eq.trans ?_ hi
    rw [iSup_subtype']
    exact e.symm.iSup_comp (g := fun j : {j // j ≠ i} ↦ (Nat.find_spec hex).choose j.1)
