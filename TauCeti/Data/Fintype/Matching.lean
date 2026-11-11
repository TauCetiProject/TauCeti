/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Data.Fintype.Fiber
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fin.Embedding

/-!
# Matching finite families with different multiplicities

Two labelings of a finite set can be matched by a permutation while retaining as many
occurrences of each label as their multiplicities permit. The unmatched positions are
bounded by the sum of the positive multiplicity differences. Applied to cell labels,
this bounds the number of vertices that must move when a partition is rebalanced.

The construction extends a fiberwise partial matching using
`Equiv.Perm.exists_extending_pair`.
-/

public section

open Finset

namespace Function

/-- Match two finite families by a permutation, changing at most the sum of their positive
multiplicity differences. No surjectivity of either family is required. -/
theorem exists_perm_card_filter_ne_le {V ι : Type*} [Fintype V] [Fintype ι]
    [DecidableEq ι] (f g : V → ι) :
    ∃ σ : Equiv.Perm V, #{x | f x ≠ g (σ x)} ≤
      ∑ i, (occCount f i - occCount g i) := by
  classical
  let k (i : ι) := min (occCount f i) (occCount g i)
  -- Embed the same initial segments into the two families of fibers.
  have he (h : V → ι) (hk : ∀ i, k i ≤ occCount h i) :
      ∃ e : (Σ i, Fin (k i)) ↪ V, ∀ a, h (e a) = a.1 := by
    let ei (i : ι) : Fin (k i) ↪ {x // h x = i} :=
      (Fin.castLEEmb (by simpa [occCount_def, Nat.card_eq_fintype_card] using hk i)).trans
        (Fintype.equivFin {x // h x = i}).symm.toEmbedding
    let e := (Embedding.sigmaMap (Embedding.refl ι) ei).trans
      (Equiv.sigmaFiberEquiv h).toEmbedding
    exact ⟨e, fun a ↦ (ei a.1 a.2).property⟩
  obtain ⟨a, ha⟩ := he f fun i ↦ min_le_left _ _
  obtain ⟨b, hb⟩ := he g fun i ↦ min_le_right _ _
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair a b a.injective b.injective
  refine ⟨σ, ?_⟩
  have hsub : (univ.filter fun x ↦ f x ≠ g (σ x)) ⊆ (univ.map a)ᶜ := by
    intro x hx
    simp only [mem_compl, mem_map, mem_univ, true_and, not_exists]
    rintro y rfl
    exact (mem_filter.1 hx).2 (by rw [hσ, ha, hb])
  calc _ ≤ #((univ.map a)ᶜ) := card_le_card hsub
    _ = Fintype.card V - ∑ i, k i := by
      rw [card_compl, card_map, card_univ, Fintype.card_sigma]
      simp only [Fintype.card_fin]
    _ = ∑ i, (occCount f i - occCount g i) := by
      have hsum : ∑ i, occCount f i = Fintype.card V := by
        simpa [Nat.card_eq_fintype_card] using
          sum_occCount_eq_card f (fun _ ↦ mem_univ _)
      rw [← hsum, ← sum_tsub_distrib _ (fun i _ ↦ min_le_left _ _)]
      exact sum_congr rfl fun i _ ↦ by omega

end Function
