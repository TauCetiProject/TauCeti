/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.KrullDimension

/-!
# Krull dimension of products, adjacent intervals and unions of upper sets

Four facts about Krull dimension that hold in every preorder. The height of a pair is at
most the sum of the heights of its components, so the Krull dimension of a product is at most the
sum of the Krull dimensions of the factors. In the other direction, for `a ≤ b ≤ c` a strict chain
in `[a, b]` and one in `[b, c]` concatenate to a strict chain in `[a, c]`, so the Krull dimension of
`[a, c]` is at least the sum of those of `[a, b]` and `[b, c]`. In a modular lattice the two
combine into additivity of Krull dimension on intervals
(`Order.krullDim_Icc_eq_krullDim_Icc_add_krullDim_Icc`).

Finally, a strict chain in a union of two upper sets lies entirely in the set that contains its
first element, so the Krull dimension of the union is the larger of the two Krull dimensions. In a
prime spectrum the closed sets are upper sets for the inclusion order, so this computes the
dimension of a union of two closed subsets, for instance the support of `M ⧸ r s M` as the union
of the supports of `M ⧸ r M` and `M ⧸ s M`.

Lastly, a strictly monotone map `f : α → β` none of whose values is maximal raises the Krull
dimension by one: every strict chain of `α` maps to a strict chain of `β` that can be extended
above its last element. In topology this is the statement that a closed subset containing no
irreducible component has smaller Krull dimension than the whole space.

## Main results

* `Order.height_prod_le`: the height of a pair is at most the sum of the heights of its
  components.
* `Order.krullDim_prod_le`: `dim (α × β) ≤ dim α + dim β`.
* `Order.krullDim_Icc_add_krullDim_Icc_le`: `dim [a, b] + dim [b, c] ≤ dim [a, c]` for
  `a ≤ b ≤ c`.
* `Order.krullDim_union_of_isUpperSet`: the Krull dimension of a union of two upper sets is the
  larger of their Krull dimensions.
* `Order.krullDim_add_one_le_of_strictMono`: `dim α + 1 ≤ dim β` for a strictly monotone
  `f : α → β` taking no maximal value.

## Implementation notes

`Order.height_prod_le` is proved by induction on a natural number bounding the sum of the heights
of the components, through `Order.height_le_coe_iff`: an element below a pair is a pair with one
component strictly smaller and the other no larger, and heights are strictly monotone where they
are finite. The lower bound for intervals bounds the Krull dimensions of `[a, b]` and `[b, c]` by
the height and the coheight of `b` in `[a, c]`, whose sum is at most the Krull dimension of
`[a, c]` (`Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`).

## References

* R. P. Stanley, *Enumerative Combinatorics, Vol. 1*, 2nd ed., Cambridge University Press (2012),
  Chapter 3, for chains and products of partially ordered sets.
-/

public section

namespace Order

variable {α β : Type*} [Preorder α] [Preorder β]

/-- **The height of a pair is at most the sum of the heights of its components.** -/
theorem height_prod_le (x : α × β) : height x ≤ height x.1 + height x.2 := by
  -- Below a pair whose components have finite height, the sum of the heights drops.
  have hlt {x y : α × β} (hy : y < x) (hfin : height x.1 + height x.2 < ⊤) :
      height y.1 + height y.2 + 1 ≤ height x.1 + height x.2 := by
    have hfin₁ : height x.1 < ⊤ := le_self_add.trans_lt hfin
    have hfin₂ : height x.2 < ⊤ := le_add_self.trans_lt hfin
    rcases Prod.lt_iff.1 hy with ⟨hy₁, hy₂⟩ | ⟨hy₁, hy₂⟩
    · rw [add_right_comm]
      exact add_le_add (Order.add_one_le_of_lt (height_strictMono hy₁
        ((height_mono hy₁.le).trans_lt hfin₁))) (height_mono hy₂)
    · rw [add_assoc]
      exact add_le_add (height_mono hy₁) (Order.add_one_le_of_lt (height_strictMono hy₂
        ((height_mono hy₂.le).trans_lt hfin₂)))
  -- Bound `height x` by every natural number bounding the right-hand side.
  suffices h : ∀ n : ℕ, ∀ x : α × β, height x.1 + height x.2 ≤ n → height x ≤ n by
    cases hx : height x.1 + height x.2 with
    | top => exact le_top
    | coe n => exact h n x hx.le
  intro n
  induction n with
  | zero =>
    intro x hx
    refine height_le_coe_iff.2 fun y hy ↦ absurd ((hlt hy (hx.trans_lt (by simp))).trans hx) ?_
    simp
  | succ n ih =>
    intro x hx
    refine height_le_coe_iff.2 fun y hy ↦ (ih y ?_).trans_lt (by exact_mod_cast n.lt_succ_self)
    have := (hlt hy (hx.trans_lt (by simp))).trans hx
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 (by exact_mod_cast this)

/-- **The Krull dimension of a product is at most the sum of the Krull dimensions of the
factors.** -/
theorem krullDim_prod_le : krullDim (α × β) ≤ krullDim α + krullDim β := by
  rw [krullDim_eq_iSup_height (α := α × β)]
  refine iSup_le fun x ↦ ?_
  calc (height x : WithBot ℕ∞) ≤ (height x.1 : WithBot ℕ∞) + height x.2 := by
        exact_mod_cast height_prod_le x
    _ ≤ krullDim α + krullDim β := add_le_add (height_le_krullDim _) (height_le_krullDim _)

/-- **Krull dimension is superadditive on adjacent intervals**: for `a ≤ b ≤ c`, a strict chain in
`[a, b]` followed by one in `[b, c]` is a strict chain in `[a, c]`. -/
theorem krullDim_Icc_add_krullDim_Icc_le {a b c : α} (hab : a ≤ b) (hbc : b ≤ c) :
    krullDim (Set.Icc a b) + krullDim (Set.Icc b c) ≤ krullDim (Set.Icc a c) := by
  let b' : Set.Icc a c := ⟨b, hab, hbc⟩
  -- `[a, b]` embeds below `b` and `[b, c]` above `b`, inside `[a, c]`.
  have h₁ : krullDim (Set.Icc a b) ≤ height b' := by
    rw [height_eq_krullDim_Iic]
    exact krullDim_le_of_strictMono
      (fun x ↦ ⟨⟨x, x.property.1, x.property.2.trans hbc⟩, x.property.2⟩) fun _ _ h ↦ h
  have h₂ : krullDim (Set.Icc b c) ≤ coheight b' := by
    rw [coheight_eq_krullDim_Ici]
    exact krullDim_le_of_strictMono
      (fun x ↦ ⟨⟨x, hab.trans x.property.1, x.property.2⟩, x.property.1⟩) fun _ _ h ↦ h
  have : Nonempty (Set.Icc a c) := ⟨b'⟩
  refine (add_le_add h₁ h₂).trans ?_
  rw [krullDim_eq_iSup_height_add_coheight_of_nonempty, ← WithBot.coe_add, WithBot.coe_le_coe]
  exact le_iSup (fun x ↦ height x + coheight x) b'

/-- The Krull dimension of a union of two upper sets is the larger of their Krull dimensions. -/
theorem krullDim_union_of_isUpperSet {s t : Set α} (hs : IsUpperSet s) (ht : IsUpperSet t) :
    krullDim ↥(s ∪ t) = max (krullDim ↥s) (krullDim ↥t) := by
  refine le_antisymm ?_ (max_le
    (krullDim_le_of_strictMono (Set.inclusion Set.subset_union_left) fun _ _ h ↦ h)
    (krullDim_le_of_strictMono (Set.inclusion Set.subset_union_right) fun _ _ h ↦ h))
  refine iSup_le fun p ↦ ?_
  -- The whole chain lies in whichever of `s` and `t` contains its first element.
  have hmem {u : Set α} (hu : IsUpperSet u) (h : (p.head : α) ∈ u) (i : Fin (p.length + 1)) :
      (p i : α) ∈ u :=
    hu (p.monotone (Fin.zero_le i)) h
  rcases p.head.property with h | h
  · exact le_max_of_le_left (LTSeries.length_le_krullDim
      ⟨p.length, fun i ↦ ⟨p i, hmem hs h i⟩, fun i ↦ p.step i⟩)
  · exact le_max_of_le_right (LTSeries.length_le_krullDim
      ⟨p.length, fun i ↦ ⟨p i, hmem ht h i⟩, fun i ↦ p.step i⟩)

/-- **A strictly monotone map into non-maximal elements raises the Krull dimension by one.** If
`f : α → β` is strictly monotone and no `f a` is maximal, then `dim α + 1 ≤ dim β`: a strict chain
in `α` maps to one in `β` whose last element can still be strictly enlarged. -/
theorem krullDim_add_one_le_of_strictMono (f : α → β) (hf : StrictMono f)
    (hmax : ∀ a, ¬IsMax (f a)) : krullDim α + 1 ≤ krullDim β := by
  rcases isEmpty_or_nonempty α with hα | hα
  · simp [krullDim_eq_bot]
  have : Nonempty β := ⟨f hα.some⟩
  rw [krullDim_eq_iSup_height_of_nonempty, krullDim_eq_iSup_height_of_nonempty, ← WithBot.coe_one,
    ← WithBot.coe_add, WithBot.coe_le_coe, ENat.iSup_add]
  refine iSup_le fun a ↦ ?_
  obtain ⟨b, hb⟩ := not_isMax_iff.mp (hmax a)
  calc height a + 1 ≤ height (f a) + 1 := by
        gcongr
        exact height_le_height_apply_of_strictMono f hf a
    _ ≤ height b := height_add_one_le hb
    _ ≤ ⨆ b, height b := le_iSup height b

end Order
