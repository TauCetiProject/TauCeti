/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Refined pigeonhole bound after erasing a shared-fiber pair

When every nonempty fiber of `f : α → β` on a finset `s` has at least two elements,
`Finset.mul_card_image_le_card` gives `2 * #(s.image f) ≤ #s`. If `x, y ∈ s` are distinct elements
in the same fiber (`f x = f y`), erasing both `x` and `y` yields the sharper bound
`2 * #(((s.erase x).erase y).image f) + 1 ≤ #s`
(`Finset.two_mul_card_image_erase_erase_add_one_le_card`).
-/

public section

namespace Finset

/-- If every nonempty fiber of `f` on `s` has at least two elements and `x, y ∈ s` are distinct
elements with `f x = f y`, then `2 * #(((s.erase x).erase y).image f) + 1 ≤ #s`. -/
theorem two_mul_card_image_erase_erase_add_one_le_card {α β : Type*} [DecidableEq α]
    [DecidableEq β] {f : α → β} (s : Finset α) {x y : α} (hx : x ∈ s) (hy : y ∈ s)
    (hxy : x ≠ y) (hfxy : f x = f y) (hn : ∀ b ∈ s.image f, 2 ≤ #{a ∈ s | f a = b}) :
    2 * #(((s.erase x).erase y).image f) + 1 ≤ #s := by
  set U := (s.erase x).erase y
  set M := U.image f
  have hUs : U ⊆ s := (erase_subset _ _).trans (erase_subset _ _)
  by_cases hm₀ : f x ∈ M
  · obtain ⟨z, hzU, hzf⟩ := mem_image.mp hm₀
    have hzy : z ≠ y := (mem_erase.mp hzU).1
    have hzx : z ≠ x := (mem_erase.mp (mem_erase.mp hzU).2).1
    have hzs : z ∈ s := hUs hzU
    have h3 : 3 ≤ #{a ∈ s | f a = f x} := by
      have hsub : ({x, y, z} : Finset α) ⊆ {a ∈ s | f a = f x} := by
        intro a ha
        simp only [mem_insert, mem_singleton] at ha
        rcases ha with rfl | rfl | rfl
        · exact mem_filter.mpr ⟨hx, rfl⟩
        · exact mem_filter.mpr ⟨hy, hfxy.symm⟩
        · exact mem_filter.mpr ⟨hzs, hzf⟩
      have hc3 : #({x, y, z} : Finset α) = 3 := by
        rw [card_insert_of_notMem (by simp [hxy, hzx.symm]),
          card_insert_of_notMem (by simp [hzy.symm]), card_singleton]
      exact hc3 ▸ card_le_card hsub
    have hsum : 3 + 2 * #(M.erase (f x)) ≤ #s := calc
      3 + 2 * #(M.erase (f x))
        = 3 + ∑ _b ∈ M.erase (f x), 2 := by simp [Nat.mul_comm]
      _ ≤ #{a ∈ s | f a = f x} + ∑ b ∈ M.erase (f x), #{a ∈ s | f a = b} :=
        Nat.add_le_add h3 (sum_le_sum fun b hb ↦
          hn b (image_subset_image hUs (mem_of_mem_erase hb)))
      _ = ∑ b ∈ M, #{a ∈ s | f a = b} := add_sum_erase M (fun b ↦ #{a ∈ s | f a = b}) hm₀
      _ ≤ ∑ b ∈ s.image f, #{a ∈ s | f a = b} := sum_le_sum_of_subset (image_subset_image hUs)
      _ = #s := (card_eq_sum_card_image f s).symm
    have hcardM : #(M.erase (f x)) + 1 = #M := card_erase_add_one hm₀
    omega
  · have hsubE : insert (f x) M ⊆ s.image f :=
      insert_subset (mem_image_of_mem f hx) (image_subset_image hUs)
    have hcardE : 2 * #(s.image f) ≤ #s := mul_card_image_le_card s 2 hn
    have hle := card_le_card hsubE
    rw [card_insert_of_notMem hm₀] at hle
    omega

end Finset
