/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Conjugacy-class sizes under coprime powers

An element and a power coprime to its order generate the same cyclic subgroup and therefore
have the same centralizer. Their conjugacy classes have the same cardinality. This is used when
converting the Galois power-map formula for ordinary characters to central characters.
-/

public section

namespace ConjClasses

/-- Raising an element to a power coprime to its order preserves the size of its conjugacy class.
The statement also covers infinite groups, using `Nat.card`. -/
theorem card_carrier_mk_pow {G : Type*} [Group G] (g : G) {n : ℕ}
    (hn : (orderOf g).Coprime n) :
    Nat.card (ConjClasses.mk (g ^ n)).carrier = Nat.card (ConjClasses.mk g).carrier := by
  have hcentral : Subgroup.centralizer ({g ^ n} : Set G) = Subgroup.centralizer {g} := by
    ext x
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp
        (mem_zpowers_pow_iff.mpr hn.symm.gcd_eq_one : g ∈ Subgroup.zpowers (g ^ n))
      exact hm ▸ (Commute.zpow_right hx m).eq
    · exact fun hx ↦ (Commute.pow_right hx n).eq
  -- At a quotient constructor, the carrier is the set of conjugates by definition.
  have hcarrier (x : G) : (ConjClasses.mk x).carrier = conjugatesOf x := (rfl)
  simp only [hcarrier, Nat.card_coe_set_eq]
  rw [← Subgroup.index_centralizer_eq_ncard, ← Subgroup.index_centralizer_eq_ncard, hcentral]

end ConjClasses
