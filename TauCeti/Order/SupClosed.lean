/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.SupClosed
public import Mathlib.Order.CompleteBooleanAlgebra

import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Finset.Lattice.Prod

/-!
# Finite and disjoint joins of intersection-stable families

Finite joins of an inf-closed family are inf-closed, as are countable disjoint joins in a
frame. A property satisfying binary Mayer–Vietoris gluing extends from an inf-closed family
to its finite joins, provided it also holds at bottom. These are the lattice ingredients
of Mayer–Vietoris induction on open sets.
-/

public section

namespace TauCeti

/-- A property holding at bottom and on an inf-closed family, and preserved by binary joins
when it holds on the intersection, holds on every finite join of members of that family. -/
theorem finset_sup_of_inf_closed {α : Type*} [DistribLattice α] [OrderBot α]
    (P : α → Prop) {B : Set α} (hB_inf : InfClosed B) (hbot : P ⊥)
    (hbase : ∀ U ∈ B, P U)
    (hsup : ∀ U V, P U → P V → P (U ⊓ V) → P (U ⊔ V))
    (s : Finset α) (hs : ∀ V ∈ s, V ∈ B) : P (s.sup id) := by
  classical
  have hbase_fin (s : Finset α) (hs : ∀ V ∈ s, V ∈ B) :
      ∀ U ∈ B, P (U ⊓ s.sup id) := by
    induction s using Finset.induction_on with
    | empty => simpa using fun U (_ : U ∈ B) ↦ hbot
    | @insert V s hVs ih =>
      intro U hU
      have hV := hs V (Finset.mem_insert_self V s)
      have hs' : ∀ W ∈ s, W ∈ B := fun W hW ↦ hs W (Finset.mem_insert_of_mem hW)
      simp only [Finset.sup_insert, id_eq, inf_sup_left]
      apply hsup _ _ (hbase _ (hB_inf hU hV)) (ih hs' U hU)
      simpa [inf_assoc, inf_left_comm, inf_comm] using ih hs' (U ⊓ V)
        (hB_inf hU hV)
  induction s using Finset.induction_on with
  | empty => simpa using hbot
  | @insert V s hVs ih =>
    have hV := hs V (Finset.mem_insert_self V s)
    have hs' : ∀ W ∈ s, W ∈ B := fun W hW ↦ hs W (Finset.mem_insert_of_mem hW)
    simpa only [Finset.sup_insert, id_eq] using
      hsup V (s.sup id) (hbase V hV) (ih hs') (hbase_fin s hs' V hV)

end TauCeti

namespace InfClosed

/-- Finite joins of members of an inf-closed family are closed under infimum. -/
theorem exists_finset_sup_inf {α : Type*} [DistribLattice α] [OrderBot α]
    {B : Set α} (hB : InfClosed B) {s t : Finset α}
    (hs : ∀ U ∈ s, U ∈ B) (ht : ∀ U ∈ t, U ∈ B) :
    ∃ r : Finset α, (∀ U ∈ r, U ∈ B) ∧ r.sup id = s.sup id ⊓ t.sup id := by
  classical
  refine ⟨(s ×ˢ t).image (fun p ↦ p.1 ⊓ p.2), ?_, ?_⟩
  · intro W hW
    obtain ⟨⟨U, V⟩, hp, rfl⟩ := Finset.mem_image.mp hW
    obtain ⟨hU, hV⟩ := Finset.mem_product.mp hp
    exact hB (hs U hU) (ht V hV)
  · simpa only [Finset.sup_image, Function.comp_def, id_eq] using
      (Finset.sup_inf_sup s t id id).symm

/-- In a frame, the infimum of two countable disjoint joins of members of an inf-closed
family is again a countable disjoint join of members of that family. -/
theorem exists_disjoint_iSup_inf {α : Type*} [Order.Frame α]
    {B : Set α} (hB : InfClosed B) {s t : ℕ → α}
    (hs : Pairwise (fun i j ↦ Disjoint (s i) (s j)))
    (ht : Pairwise (fun i j ↦ Disjoint (t i) (t j)))
    (hFs : ∀ n, s n ∈ B) (hFt : ∀ n, t n ∈ B) :
    ∃ u : ℕ → α, Pairwise (fun i j ↦ Disjoint (u i) (u j)) ∧
      (∀ n, u n ∈ B) ∧ iSup u = iSup s ⊓ iSup t := by
  let f (p : ℕ × ℕ) := s p.1 ⊓ t p.2
  refine ⟨f ∘ Nat.unpair, ?_, fun n ↦ hB (hFs _) (hFt _), ?_⟩
  · intro i j hij
    by_cases hfst : (Nat.unpair i).1 = (Nat.unpair j).1
    · have hsnd : (Nat.unpair i).2 ≠ (Nat.unpair j).2 := by
        intro heq
        exact hij (Nat.pairEquiv.symm.injective (Prod.ext hfst heq))
      exact Disjoint.mono inf_le_right inf_le_right (ht hsnd)
    · exact Disjoint.mono inf_le_left inf_le_left (hs hfst)
  · rw [Function.comp_def, Nat.surjective_unpair.iSup_comp]
    exact iSup_inf_iSup.symm

end InfClosed
