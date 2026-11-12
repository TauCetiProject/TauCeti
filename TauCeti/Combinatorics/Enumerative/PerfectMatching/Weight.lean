/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Weighted perfect matchings

Assign a weight to each pair of positions and multiply the weights of the arcs of a perfect
matching. A linear order chooses the smaller endpoint of each arc, so each arc contributes
exactly once. For symmetric pair weights, adjoining an arc multiplies the weight by the weight
of that pair. Consequently the sum over all perfect matchings expands by the partner of any
chosen position.

This is the combinatorial expansion used for sums of covariance products in Gaussian moment
formulas. It uses the existing restriction, extension, and fiber equivalence of perfect matchings;
no new encoding of pair partitions is introduced.
-/

public section

namespace TauCeti.PerfectMatching

open Finset

variable {α R : Type*} [Fintype α] [LinearOrder α]

section Monoid

variable [CommMonoid R]

/-- The product of the pair weights of a perfect matching, taking each arc at its smaller
endpoint. Symmetric pair weights give an unoriented arc weight. -/
def weight (D : PerfectMatching α) (w : α → α → R) : R :=
  ∏ x : α, if x < D.val x then w x (D.val x) else 1

/-- Each arc contributes at its smaller endpoint in the defining product. -/
theorem weight_def (D : PerfectMatching α) (w : α → α → R) :
    D.weight w = ∏ x : α, if x < D.val x then w x (D.val x) else 1 := (rfl)

/-- The weight depends only on the pair weights on the arcs of the matching. -/
theorem weight_congr (D : PerfectMatching α) {w v : α → α → R}
    (h : ∀ x, x < D.val x → w x (D.val x) = v x (D.val x)) :
    D.weight w = D.weight v := by
  simp only [weight_def]
  exact prod_congr rfl fun x _ ↦ by split_ifs with hx; exacts [h x hx, rfl]

/-- Unit pair weights give unit matching weight. -/
@[simp]
theorem weight_one (D : PerfectMatching α) : D.weight (fun _ _ ↦ (1 : R)) = 1 := by
  simp [weight_def]

/-- Pointwise multiplication of pair weights multiplies matching weights. -/
theorem weight_mul (D : PerfectMatching α) (w v : α → α → R) :
    D.weight (fun x y ↦ w x y * v x y) = D.weight w * D.weight v := by
  simp only [weight_def, ← prod_mul_distrib]
  apply prod_congr rfl
  intro x _
  split_ifs <;> simp

/-- On an empty type the unique matching has the empty product as its weight. -/
@[simp]
theorem weight_of_isEmpty [IsEmpty α] (D : PerfectMatching α) (w : α → α → R) :
    D.weight w = 1 := by
  simp [weight_def]

/-- Adjoining an arc to a matching multiplies its weight by that arc's weight. Symmetry allows
both orders of its endpoints, without assuming that the chosen position is the smallest one. -/
theorem weight_extend {a b : α} (hab : a ≠ b)
    (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) (w : α → α → R)
    (hw : w b a = w a b) :
    (extend hab E).weight w = w a b * E.weight (fun x y ↦ w x y) := by
  let f : α → R := fun x ↦ if x < (extend hab E).val x then w x ((extend hab E).val x) else 1
  have hpair : (∏ x ∈ ({a, b} : Finset α), f x) = w a b := by
    rw [prod_pair hab]
    simp only [f, extend_apply_left, extend_apply_right]
    rcases lt_or_gt_of_ne hab with h | h
    · simp [h, not_lt_of_gt h]
    · simp [h, not_lt_of_gt h, hw]
  have hrest : (∏ x ∈ ({a, b} : Finset α)ᶜ, f x) =
      E.weight (fun x y ↦ w x y) := by
    rw [prod_subtype (F := inferInstance) ({a, b} : Finset α)ᶜ
      (by simp : ∀ x : α, x ∈ ({a, b} : Finset α)ᶜ ↔ x ≠ a ∧ x ≠ b) f]
    simp only [weight_def]
    apply prod_congr rfl
    intro x _
    simp only [f, extend_apply_of_mem hab E x.property]
    rfl
  calc
    (extend hab E).weight w = ∏ x, f x := by rw [weight_def]
    _ = (∏ x ∈ ({a, b} : Finset α), f x) * ∏ x ∈ ({a, b} : Finset α)ᶜ, f x :=
      (prod_mul_prod_compl _ _).symm
    _ = w a b * E.weight (fun x y ↦ w x y) := by rw [hpair, hrest]

/-- Removing the arc through a chosen position factors its weight out of the product, provided
the pair weight agrees in both orientations of that arc. -/
theorem weight_eq_mul_weight_restrict (D : PerfectMatching α) (a : α) (w : α → α → R)
    (hw : w (D.val a) a = w a (D.val a)) :
    D.weight w = w a (D.val a) * (D.restrict (a := a) rfl).weight (fun x y ↦ w x y) := by
  have h := weight_extend (D.apply_ne a).symm (D.restrict (a := a) rfl) w hw
  rwa [extend_restrict] at h

end Monoid

/-- The sum of matching weights on an empty type is one: there is exactly one empty matching.
This is the initial value for expansion by partners. -/
theorem sum_weight_of_isEmpty [CommSemiring R] [IsEmpty α] (w : α → α → R) :
    (∑ D : PerfectMatching α, D.weight w) = 1 := by
  simp [card_perfectMatching α (m := 0) (by simp)]

/-- Expand the sum of matching weights by the partner of a chosen position. The inner sum runs
over matchings of the complement of the selected pair, with the original pair weights restricted
to that complement. Only weights incident to the chosen position need to be symmetric.
This also covers a singleton type, where both sides are empty sums. -/
theorem sum_weight_eq_sum_partner [CommSemiring R] (a : α) (w : α → α → R)
    (hw : ∀ b, w b a = w a b) :
    (∑ D : PerfectMatching α, D.weight w) =
      ∑ b : {b : α // b ≠ a}, w a b *
        ∑ E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}, E.weight (fun x y ↦ w x y) := by
  let partner : PerfectMatching α → {b : α // b ≠ a} := fun D ↦ ⟨D.val a, D.apply_ne a⟩
  rw [← Fintype.sum_fiberwise partner (fun D ↦ D.weight w)]
  apply sum_congr rfl
  intro b _
  rw [mul_sum]
  let e : {D : PerfectMatching α // partner D = b} ≃
      PerfectMatching {x : α // x ≠ a ∧ x ≠ b} :=
    (Equiv.subtypeEquivRight (fun D ↦ Subtype.ext_iff)).trans (fiberEquiv b.property.symm)
  apply Fintype.sum_equiv e
  intro D
  have hD : D.val.val a = b := congrArg Subtype.val D.property
  have he : e D = D.val.restrict hD := by
    simp only [e, Equiv.trans_apply, Equiv.subtypeEquivRight_apply, fiberEquiv_apply]
  rw [he]
  have h := weight_extend b.property.symm (D.val.restrict hD) w (hw _)
  rwa [extend_restrict b.property.symm D.val hD] at h

end TauCeti.PerfectMatching
