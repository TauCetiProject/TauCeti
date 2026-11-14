/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Multiset

/-!
# Norm bounds for multiset products in seminormed commutative rings

In a seminormed commutative ring `α`, submultiplicativity of the norm extends to nonempty multiset
products (`Multiset.norm_prod_le'`), and to arbitrary multiset products when `‖(1 : α)‖ = 1`
(`Multiset.norm_prod_le`). Uniform factor bounds `‖f x‖ ≤ B` then yield power bounds `B ^ s.card`
(`Multiset.norm_prod_le_pow_card`, `Multiset.norm_prod_map_le_pow_card`). These are the `Multiset`
counterparts of `List.norm_prod_le` and `Finset.norm_prod_le`.

## Main results

* `Multiset.norm_prod_le'`, `Multiset.norm_prod_le`: submultiplicativity of `norm` on multiset
  products.
* `Multiset.norm_prod_le_pow_card`, `Multiset.norm_prod_map_le_pow_card`: uniform factor bounds give
  `‖(s.map f).prod‖ ≤ B ^ s.card`.
-/

public section

namespace Multiset

variable {ι α : Type*}

/-- In a seminormed commutative ring, the norm of a nonempty multiset product is at most the
product of the norms. -/
theorem norm_prod_le' [SeminormedCommRing α] (s : Multiset α) (hs : s ≠ 0) :
    ‖s.prod‖ ≤ (s.map norm).prod := by
  rcases s with ⟨l⟩
  have hl : l ≠ [] := by simpa using hs
  simpa using List.norm_prod_le' hl

/-- In a seminormed commutative ring with `‖1‖ = 1`, the norm of a multiset product is at most the
product of the norms. -/
theorem norm_prod_le [SeminormedCommRing α] [NormOneClass α] (s : Multiset α) :
    ‖s.prod‖ ≤ (s.map norm).prod := by
  rcases s with ⟨l⟩
  simpa using l.norm_prod_le

/-- If every element of `s` has norm at most `B`, then `‖s.prod‖ ≤ B ^ s.card`. -/
theorem norm_prod_le_pow_card [SeminormedCommRing α] [NormOneClass α] (s : Multiset α) {B : ℝ}
    (hs : ∀ x ∈ s, ‖x‖ ≤ B) : ‖s.prod‖ ≤ B ^ s.card := by
  refine s.norm_prod_le.trans ?_
  simpa using prod_map_le_prod_map₀ norm (fun _ ↦ B) (fun _ _ ↦ norm_nonneg _) hs

/-- If `‖f x‖ ≤ B` for every `x ∈ s`, then `‖(s.map f).prod‖ ≤ B ^ s.card`. -/
theorem norm_prod_map_le_pow_card [SeminormedCommRing α] [NormOneClass α] (s : Multiset ι)
    (f : ι → α) {B : ℝ} (hf : ∀ x ∈ s, ‖f x‖ ≤ B) : ‖(s.map f).prod‖ ≤ B ^ s.card := by
  simpa using (s.map f).norm_prod_le_pow_card (by simpa using hf)

end Multiset
