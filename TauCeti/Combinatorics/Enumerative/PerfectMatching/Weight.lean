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

/-- Constant pair weights contribute one factor for each of the half as many arcs as points. -/
@[simp]
theorem weight_const (D : PerfectMatching α) (c : R) :
    D.weight (fun _ _ ↦ c) = c ^ (Fintype.card α / 2) := by
  have hcard : Fintype.card {x : α // x < D.val x} = Fintype.card α / 2 := by
    have he := Fintype.card_congr (D.val.subtypeEquiv
      (p := fun x ↦ x < D.val x) (q := fun x ↦ ¬x < D.val x) (fun x ↦ by
        rw [D.apply_apply, not_lt]
        exact ⟨le_of_lt, fun h ↦ lt_of_le_of_ne h (D.apply_ne x).symm⟩))
    rw [Fintype.card_subtype_compl] at he
    have := Fintype.card_subtype_le (fun x ↦ x < D.val x)
    omega
  rw [weight_def, ← prod_filter, prod_const, ← Fintype.card_subtype, hcard]

/-- A multiplicative map commutes with matching weights. -/
@[simp]
theorem map_weight {S F : Type*} [CommMonoid S] [FunLike F R S] [MonoidHomClass F R S]
    (D : PerfectMatching α) (f : F) (w : α → α → R) :
    f (D.weight w) = D.weight (fun x y ↦ f (w x y)) := by
  simp only [weight_def, map_prod, apply_ite f, map_one]

/-- Transport preserves matching weights when weights are symmetric on the arcs whose
orientation is reversed. In particular, symmetric weights do not depend on the linear order
used to orient the arcs. -/
theorem weight_congr_equiv {β : Type*} [Fintype β] [LinearOrder β]
    (D : PerfectMatching α) (e : α ≃ β) (w : β → β → R)
    (hw : ∀ x, x < D.val x → e (D.val x) < e x →
      w (e (D.val x)) (e x) = w (e x) (e (D.val x))) :
    (congr e D).weight w = D.weight (fun x y ↦ w (e x) (e y)) := by
  -- Swap the ends exactly of the arcs whose orientation changes under transport.
  let f : α → α := fun x ↦ if (x < D.val x ↔ e x < e (D.val x)) then x else D.val x
  have hf : Function.Involutive f := by
    intro x
    rcases lt_or_gt_of_ne (D.apply_ne x).symm with hx | hx <;>
      rcases lt_or_gt_of_ne (e.injective.ne (D.apply_ne x).symm) with he | he <;>
      simp [f, D.apply_apply, hx, he, not_lt_of_gt hx, not_lt_of_gt he]
  simp only [weight_def]
  symm
  apply Fintype.prod_bijective (fun x ↦ e (f x)) (e.bijective.comp hf.bijective)
  intro x
  simp only [congr_val_apply, Equiv.symm_apply_apply]
  rcases lt_or_gt_of_ne (D.apply_ne x).symm with hx | hx <;>
    rcases lt_or_gt_of_ne (e.injective.ne (D.apply_ne x).symm) with he | he <;>
    simp [f, D.apply_apply, hx, he, not_lt_of_gt hx, not_lt_of_gt he, hw x]

/-- Transport along an order isomorphism preserves matching weights without a symmetry
assumption. -/
theorem weight_congr_orderIso {β : Type*} [Fintype β] [LinearOrder β]
    (D : PerfectMatching α) (e : α ≃o β) (w : β → β → R) :
    (congr e.toEquiv D).weight w = D.weight (fun x y ↦ w (e x) (e y)) :=
  weight_congr_equiv D e.toEquiv w fun _ hx he ↦ (lt_asymm he (e.lt_iff_lt.mpr hx)).elim

/-- On an empty type the unique matching has the empty product as its weight. -/
@[simp]
theorem weight_of_isEmpty [IsEmpty α] (D : PerfectMatching α) (w : α → α → R) :
    D.weight w = 1 := by
  simp [weight_def]

/-- Adjoining an arc multiplies the weight by its pair weight in increasing endpoint order. -/
theorem weight_extend_eq_min_max_mul_weight {a b : α} (hab : a ≠ b)
    (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) (w : α → α → R) :
    (extend hab E).weight w = w (min a b) (max a b) * E.weight (fun x y ↦ w x y) := by
  let f : α → R := fun x ↦ if x < (extend hab E).val x then w x ((extend hab E).val x) else 1
  have hpair : (∏ x ∈ ({a, b} : Finset α), f x) = w (min a b) (max a b) := by
    rw [prod_pair hab]
    simp only [f, extend_apply_left, extend_apply_right]
    rcases lt_or_gt_of_ne hab with h | h
    · simp [h, not_lt_of_gt h, min_eq_left h.le, max_eq_right h.le]
    · simp [h, not_lt_of_gt h, min_eq_right h.le, max_eq_left h.le]
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
    _ = w (min a b) (max a b) * E.weight (fun x y ↦ w x y) := by rw [hpair, hrest]

/-- Adjoining an arc factors out its pair weight. Symmetry is needed only when the endpoints
are given in decreasing order. -/
theorem weight_extend {a b : α} (hab : a ≠ b)
    (E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}) (w : α → α → R)
    (hw : b < a → w b a = w a b) :
    (extend hab E).weight w = w a b * E.weight (fun x y ↦ w x y) := by
  rw [weight_extend_eq_min_max_mul_weight]
  rcases lt_or_gt_of_ne hab with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
  · rw [min_eq_right h.le, max_eq_left h.le, hw h]

/-- Removing an arc factors out its pair weight in increasing endpoint order. -/
theorem weight_eq_min_max_mul_weight_restrict {a b : α} (D : PerfectMatching α)
    (hab : D.val a = b) (w : α → α → R) :
    D.weight w = w (min a b) (max a b) * (D.restrict hab).weight (fun x y ↦ w x y) := by
  have h := weight_extend_eq_min_max_mul_weight (hab ▸ D.apply_ne a).symm (D.restrict hab) w
  rwa [extend_restrict] at h

/-- Removing an arc factors out its pair weight. Symmetry is needed only when the endpoints
are given in decreasing order. -/
theorem weight_eq_mul_weight_restrict {a b : α} (D : PerfectMatching α)
    (hab : D.val a = b) (w : α → α → R) (hw : b < a → w b a = w a b) :
    D.weight w = w a b * (D.restrict hab).weight (fun x y ↦ w x y) := by
  have h := weight_extend (hab ▸ D.apply_ne a).symm (D.restrict hab) w hw
  rwa [extend_restrict] at h

end Monoid

/-- Relabeling positions preserves the sum of matching weights when weights are symmetric
on pairs whose orientation is reversed. -/
theorem sum_weight_equiv {β : Type*} [Fintype β] [LinearOrder β] [CommSemiring R]
    (e : α ≃ β) (w : β → β → R)
    (hw : ∀ x y, x < y → e y < e x → w (e y) (e x) = w (e x) (e y)) :
    (∑ D : PerfectMatching β, D.weight w) =
      ∑ D : PerfectMatching α, D.weight (fun x y ↦ w (e x) (e y)) := by
  symm
  apply Fintype.sum_equiv (congr e)
  intro D
  exact (weight_congr_equiv D e w (fun x ↦ hw x (D.val x))).symm

/-- Relabeling along an order isomorphism preserves the sum of matching weights without a
symmetry assumption. -/
theorem sum_weight_orderIso {β : Type*} [Fintype β] [LinearOrder β] [CommSemiring R]
    (e : α ≃o β) (w : β → β → R) :
    (∑ D : PerfectMatching β, D.weight w) =
      ∑ D : PerfectMatching α, D.weight (fun x y ↦ w (e x) (e y)) :=
  sum_weight_equiv e.toEquiv w fun _ _ hxy he ↦ (lt_asymm he (e.lt_iff_lt.mpr hxy)).elim

/-- The sum of matching weights on an empty type is one: there is exactly one empty matching.
This is the initial value for expansion by partners. -/
theorem sum_weight_of_isEmpty [CommSemiring R] [IsEmpty α] (w : α → α → R) :
    (∑ D : PerfectMatching α, D.weight w) = 1 := by
  simp

/-- Expand the sum of matching weights by the partner of a chosen position, taking the selected
pair in increasing endpoint order. The inner sum runs over matchings of its complement.
This also covers a singleton type, where both sides are empty sums. -/
theorem sum_weight_eq_sum_min_max_mul_sum_weight [CommSemiring R] (a : α) (w : α → α → R) :
    (∑ D : PerfectMatching α, D.weight w) =
      ∑ b : {b : α // b ≠ a}, w (min a b) (max a b) *
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
  exact weight_eq_min_max_mul_weight_restrict D.val hD w

/-- Expand matching weights by the partner of a chosen position. Only pairs whose partner is
smaller than the chosen position need to have symmetric weights. -/
theorem sum_weight_eq_sum_mul_sum_weight [CommSemiring R] (a : α) (w : α → α → R)
    (hw : ∀ b < a, w b a = w a b) :
    (∑ D : PerfectMatching α, D.weight w) =
      ∑ b : {b : α // b ≠ a}, w a b *
        ∑ E : PerfectMatching {x : α // x ≠ a ∧ x ≠ b}, E.weight (fun x y ↦ w x y) := by
  rw [sum_weight_eq_sum_min_max_mul_sum_weight]
  apply sum_congr rfl
  intro b _
  rcases lt_or_gt_of_ne b.property.symm with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
  · rw [min_eq_right h.le, max_eq_left h.le, hw b h]

end TauCeti.PerfectMatching
