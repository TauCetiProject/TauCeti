/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Counting and classifying the subgroups of a finite cyclic group

A finite cyclic group has exactly one subgroup of each order dividing its cardinality, so its
subgroups are counted by the divisors of that cardinality. When the cardinality is the square of a
prime `p`, every subgroup is trivial, the unique subgroup of order `p`, or the whole group. These
finite classifications are useful when the Galois correspondence turns subgroups into
intermediate fields.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [IsCyclic G]

/-- A finite cyclic group has exactly one subgroup of each order dividing its cardinality, so
its subgroups are counted by the divisors of that cardinality. -/
theorem card_subgroups_eq_card_divisors [Finite G] :
    Nat.card (Subgroup G) = (Nat.card G).divisors.card := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_eq_of_bijective
    (fun S ↦ ⟨Nat.card S, Nat.mem_divisors.mpr ⟨S.card_subgroup_dvd_card, Nat.card_pos.ne'⟩⟩)
    ⟨fun S T h ↦ IsCyclic.subgroup_eq_iff_card_eq.mpr (congrArg Subtype.val h), ?_⟩
  rintro ⟨d, hd⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  have hdg : d ∣ orderOf g := hg ▸ Nat.dvd_of_mem_divisors hd
  exact ⟨Subgroup.zpowers (g ^ (orderOf g / d)), Subtype.ext <| (Nat.card_zpowers _).trans <|
    orderOf_pow_orderOf_div (orderOf_pos g).ne' hdg⟩

/-- In a cyclic group of order `p ^ 2` for a prime `p`, the subgroup of order `p` is the only
proper nontrivial subgroup. -/
theorem subgroup_eq_bot_or_eq_or_eq_top_of_card_eq_prime_sq {p : ℕ} (hp : p.Prime)
    (hG : Nat.card G = p ^ 2) (H : Subgroup G) (hH : Nat.card H = p) (S : Subgroup G) :
    S = ⊥ ∨ S = H ∨ S = ⊤ := by
  have : Finite G := Nat.finite_of_card_ne_zero (by simp [hG, hp.ne_zero])
  obtain ⟨k, hk, hS⟩ := (Nat.dvd_prime_pow hp).mp (hG ▸ S.card_subgroup_dvd_card)
  interval_cases k
  · exact Or.inl (S.eq_bot_iff_card.mpr (by simpa using hS))
  · exact Or.inr (Or.inl (IsCyclic.subgroup_eq_iff_card_eq.mpr (by simpa [hH] using hS)))
  · exact Or.inr (Or.inr (S.card_eq_iff_eq_top.mp (hS.trans hG.symm)))

end TauCeti
