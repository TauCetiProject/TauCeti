/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Subgroup.Simple

/-!
# Simplicity from normal generation by prime-order elements

A finite nontrivial group is simple if each prime-order element normally generates it:
Cauchy's theorem supplies such an element in every nontrivial normal subgroup.

It suffices to check normal generation for representatives that cover all prime-order
elements up to conjugacy. The coverage and normal-generation hypotheses are separate
proof obligations; this criterion supplies the soundness step for the normal-closure
simplicity certificates in CFSG basic properties P0.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [Finite G] [Nontrivial G]

/-- A finite nontrivial group is simple if every prime-order element normally generates it. -/
theorem isSimpleGroup_of_prime_order_normalClosure
    (h : ∀ g : G, (orderOf g).Prime → Subgroup.normalClosure ({g} : Set G) = ⊤) :
    IsSimpleGroup G := by
  refine ⟨fun H _ ↦ ?_⟩
  by_cases hH : H = ⊥
  · exact Or.inl hH
  · right
    have : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hH
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := H)).ne'
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H) p hpdvd
    have hprime : (orderOf (g : G)).Prime := by
      simpa only [Subgroup.orderOf_coe, hg] using hp
    apply top_unique
    rw [← h g hprime]
    exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr g.property)

/-- A finite nontrivial group is simple if representatives cover its prime-order elements
up to conjugacy and each representative normally generates it.

The indexing type may in particular be `Fin n` for a finite certificate. The representatives
need not be distinct, and the theorem does not require a finiteness assumption on their index. -/
theorem isSimpleGroup_of_prime_order_representatives {ι : Type*} (r : ι → G)
    (hcover : ∀ g : G, (orderOf g).Prime → ∃ i, IsConj g (r i))
    (hgenerate : ∀ i, Subgroup.normalClosure ({r i} : Set G) = ⊤) :
    IsSimpleGroup G := by
  apply isSimpleGroup_of_prime_order_normalClosure
  intro g hg
  obtain ⟨i, hi⟩ := hcover g hg
  obtain ⟨c, hc⟩ := isConj_iff.mp hi
  have hr : r i ∈ Subgroup.normalClosure ({g} : Set G) := by
    rw [← hc]
    exact Subgroup.normalClosure_normal.conj_mem g
      (Subgroup.subset_normalClosure (Set.mem_singleton g)) c
  apply top_unique
  rw [← hgenerate i]
  exact Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hr)

end TauCeti
