/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Products over maps depending on two coordinates

For finite types `ι` and `α` and distinct indices `i ≠ j`, every pair `(x, y)` is hit by exactly
`card α ^ (card ι - 2)` maps `g : ι → α` with `g i = x` and `g j = y`. Consequently a product, or
sum, over all maps `g : ι → α` of a quantity depending only on `g i` and `g j` is a power, or
multiple, of the double product, or double sum, over `α`. Counting arguments use this to turn
a sum over labelled tuples of vertices into a sum over ordered pairs of vertices.

## Main results

* `Fintype.card_filter_apply_apply_eq`: the number of maps with prescribed values at two
  distinct coordinates.
* `Fintype.prod_apply_apply_of_ne`, `Fintype.sum_apply_apply_of_ne`: products and sums over maps
  of a function of two distinct coordinates.
-/

public section

open Finset

namespace Fintype

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] {i j : ι}

/-- For distinct coordinates `i ≠ j`, exactly `card α ^ (card ι - 2)` maps `g : ι → α` satisfy
`g i = x` and `g j = y`. -/
theorem card_filter_apply_apply_eq [DecidableEq α] (hij : i ≠ j) (x y : α) :
    #{g : ι → α | g i = x ∧ g j = y} = card α ^ (card ι - 2) := by
  have hfilter : ({g : ι → α | g i = x ∧ g j = y} : Finset (ι → α)) =
      {g ∈ piFinset (Function.update (fun _ ↦ (univ : Finset α)) i {x}) | g j = y} := by
    rw [piFinset_update_singleton_eq_filter_piFinset_eq (fun _ : ι ↦ (univ : Finset α)) i
      (Finset.mem_univ x), filter_filter,
      piFinset_univ]
  have hj : y ∈ Function.update (fun _ ↦ (univ : Finset α)) i {x} j := by
    simp [Function.update_of_ne hij.symm]
  rw [hfilter, card_filter_piFinset_eq_of_mem _ _ hj]
  have hi : i ∈ (univ : Finset ι).erase j := mem_erase.2 ⟨hij, Finset.mem_univ i⟩
  calc ∏ b ∈ univ.erase j, #(Function.update (fun _ ↦ (univ : Finset α)) i {x} b)
      = ∏ b ∈ univ.erase j, Function.update (fun _ ↦ card α) i 1 b :=
        Finset.prod_congr rfl fun b _ ↦ by obtain rfl | hb := eq_or_ne b i <;> simp [*]
    _ = card α ^ (card ι - 2) := by
        rw [Finset.prod_update_of_mem hi, one_mul, Finset.prod_const, ← erase_eq,
          Finset.card_erase_of_mem hi, Finset.card_erase_of_mem (Finset.mem_univ j),
          Finset.card_univ, Nat.sub_sub]

/-- A product over all maps `g : ι → α` of a function of two distinct coordinates `g i` and `g j`
is the double product over `α`, raised to the power `card α ^ (card ι - 2)`. -/
@[to_additive /-- A sum over all maps `g : ι → α` of a function of two distinct coordinates
`g i` and `g j` is `card α ^ (card ι - 2)` times the double sum over `α`. -/]
theorem prod_apply_apply_of_ne {M : Type*} [CommMonoid M] (hij : i ≠ j) (f : α → α → M) :
    ∏ g : ι → α, f (g i) (g j) = (∏ x, ∏ y, f x y) ^ (card α ^ (card ι - 2)) := by
  classical
  rw [← Finset.prod_fiberwise univ (fun g : ι → α ↦ (g i, g j)), ← prod_prod_type', ← prod_pow]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  rw [Finset.prod_congr rfl fun g hg ↦ congrArg (fun q ↦ f q.1 q.2) (mem_filter.1 hg).2,
    Finset.prod_const]
  congr 1
  rw [← card_filter_apply_apply_eq hij p.1 p.2]
  congr 1

end Fintype
