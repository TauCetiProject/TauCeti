/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Data.SetLike.Fintype
import Mathlib.Tactic.IntervalCases

/-!
# Subgroups of a cyclic group of order four

A cyclic group of order four has exactly three subgroups. The subgroup of order two is unique,
and every subgroup is trivial, that subgroup, or the whole group. This finite classification is
useful when Galois correspondence turns subgroups into intermediate fields.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G] [Finite G] [IsCyclic G]

/-- In a cyclic group of order four, the unique subgroup of order two is the only proper
nontrivial subgroup. -/
theorem subgroup_eq_bot_or_eq_or_eq_top_of_card_eq_two
    (hG : Nat.card G = 4) (H : Subgroup G) (hH : Nat.card H = 2) (S : Subgroup G) :
    S = ⊥ ∨ S = H ∨ S = ⊤ := by
  have hdiv : Nat.card S ∣ 4 := hG ▸ S.card_subgroup_dvd_card
  have hcases : Nat.card S = 1 ∨ Nat.card S = 2 ∨ Nat.card S = 4 := by
    have hdiv' : Nat.card S ∣ 2 ^ 2 := by
      simpa only [show (2 : ℕ) ^ 2 = 4 by decide] using hdiv
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv'
    interval_cases k <;> simp_all
  rcases hcases with h | h | h
  · exact Or.inl ((Subgroup.eq_bot_iff_card S).mpr h)
  · exact Or.inr (Or.inl ((IsCyclic.subgroup_eq_iff_card_eq).mpr (h.trans hH.symm)))
  · exact Or.inr (Or.inr ((Subgroup.card_eq_iff_eq_top S).mp (hG ▸ h)))

/-- A cyclic group of order four has three subgroups. -/
theorem card_subgroups_of_card_eq_four (hG : Nat.card G = 4) :
    Nat.card (Subgroup G) = 3 := by
  classical
  have : Fintype (Subgroup G) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.mp ‹IsCyclic G›
  let H : Subgroup G := Subgroup.zpowers (g ^ 2)
  have hH : Nat.card H = 2 := by
    rw [Nat.card_zpowers, orderOf_pow, hg, hG]
    decide
  have hHbot : H ≠ ⊥ := by
    intro h
    simp [h] at hH
  have hHtop : H ≠ ⊤ := by
    intro h
    simp [h, hG] at hH
  have hbt : (⊥ : Subgroup G) ≠ ⊤ := by
    intro h
    have : Nat.card (⊥ : Subgroup G) = Nat.card (⊤ : Subgroup G) := by rw [h]
    simp [hG] at this
  have huniv : (Finset.univ : Finset (Subgroup G)) = {⊥, H, ⊤} := by
    ext S
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    exact subgroup_eq_bot_or_eq_or_eq_top_of_card_eq_two hG H hH S
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ, huniv]
  simp [hHbot.symm, hHtop, hbt]

end TauCeti
