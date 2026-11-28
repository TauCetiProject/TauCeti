/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Max

/-!
# Decreasing enumeration of a finite family bounding subset products

Given a finite set `S` and a nonnegative function `d : ι → α` into a linearly ordered commutative
semiring (`[CommSemiring α] [LinearOrder α] [IsOrderedRing α]`), sorting the values of `d` on `S`
in nonincreasing order yields a sequence `ρ : ℕ → α` of nonnegative terms whose first `#S` entries
sum to `∑ a ∈ S, d a` and whose first `#A` entries have product at least `∏ a ∈ A, d a` for every
subset `A ⊆ S` (`Finset.exists_enum_prod_le`).

## Main results

* `Finset.exists_enum_prod_le`: existence of a nonnegative sequence `ρ : ℕ → α` with
  `∑ i ∈ range #S, ρ i = ∑ a ∈ S, d a` and `∏ a ∈ A, d a ≤ ∏ i ∈ range #A, ρ i` for all `A ⊆ S`.

## Provenance

Adapted from grh-lean (https://github.com/lsernau/grh-lean at commit
72fead102f663d5c7a407964a13dc0cf9d977207, Apache 2.0, Copyright 2026 Anthropic, PBC), file
src/Lib/GLn/SchurModule/SchurNorm.lean (`exists_enum_prod_le`).
-/

public section

namespace Finset

/-- For a nonnegative function `d : ι → α` on a finite set `S` taking values in a linearly ordered
commutative semiring, there exists a sequence `ρ : ℕ → α` of nonnegative values on `range #S`
whose first `#S` terms sum to `∑ a ∈ S, d a` and whose first `#A` terms have product at least
`∏ a ∈ A, d a` for every subset `A ⊆ S`. -/
theorem exists_enum_prod_le {ι α : Type*} [CommSemiring α] [LinearOrder α] [IsOrderedRing α]
    (d : ι → α) (S : Finset ι) (hd : ∀ a ∈ S, 0 ≤ d a) :
    ∃ ρ : ℕ → α, (∀ i < #S, 0 ≤ ρ i) ∧
      ∑ i ∈ range #S, ρ i = ∑ a ∈ S, d a ∧
      ∀ A ⊆ S, ∏ a ∈ A, d a ≤ ∏ i ∈ range #A, ρ i := by
  classical
  induction S using Finset.induction_on_max_value d with
  | empty => exact ⟨0, by simp, by simp, fun A hA ↦ by simp [subset_empty.mp hA]⟩
  | insert a S ha hmax ih =>
    obtain ⟨ρ, hρ_nonneg, h_sum, h_prod⟩ :=
      ih fun x hx ↦ hd x (mem_insert_of_mem hx)
    have ha0 : 0 ≤ d a := hd a (mem_insert_self a S)
    let ρ' : ℕ → α
      | 0 => d a
      | i + 1 => ρ i
    refine ⟨ρ', ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => exact ha0
      | succ i =>
        rw [card_insert_of_notMem ha] at hi
        exact hρ_nonneg i (Nat.lt_of_succ_lt_succ hi)
    · rw [card_insert_of_notMem ha, sum_range_succ', sum_insert ha, add_comm, h_sum]
    · intro A hA
      rcases A.eq_empty_or_nonempty with rfl | ⟨c, hc⟩
      · simp
      obtain ⟨b, hb, h_sub, h_le⟩ : ∃ b ∈ A, A.erase b ⊆ S ∧ d b ≤ d a := by
        by_cases haA : a ∈ A
        · refine ⟨a, haA, fun x hx ↦ ?_, le_rfl⟩
          exact (mem_insert.mp (hA (mem_of_mem_erase hx))).resolve_left (ne_of_mem_erase hx)
        · refine ⟨c, hc, fun x hx ↦ ?_, ?_⟩
          · exact (mem_insert.mp (hA (mem_of_mem_erase hx))).resolve_left
              fun hxa ↦ haA (hxa ▸ mem_of_mem_erase hx)
          · exact hmax c ((mem_insert.mp (hA hc)).resolve_left fun hca ↦ haA (hca ▸ hc))
      rw [← prod_erase_mul A d hb, ← card_erase_add_one hb, prod_range_succ']
      exact mul_le_mul (h_prod _ h_sub) h_le (hd b (hA hb))
        (prod_nonneg fun i hi ↦ hρ_nonneg i
          ((mem_range.mp hi).trans_le (card_le_card h_sub)))

end Finset
