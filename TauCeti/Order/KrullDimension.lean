/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.KrullDimension
import TauCeti.Order.Hom.Set

/-!
# Krull dimension of products, adjacent intervals and unions of upper or lower sets

Facts about Krull dimension that hold in every preorder. The height of a pair is at
most the sum of the heights of its components, so the Krull dimension of a product is at most the
sum of the Krull dimensions of the factors. In the other direction, for `a ≤ b ≤ c` a strict chain
in `[a, b]` and one in `[b, c]` concatenate to a strict chain in `[a, c]`, so the Krull dimension of
`[a, c]` is at least the sum of those of `[a, b]` and `[b, c]`. In a modular lattice the two
combine into additivity of Krull dimension on intervals
(`Order.krullDim_Icc_eq_krullDim_Icc_add_krullDim_Icc`).

Finally, a strict chain in an arbitrary union of upper sets (resp. lower sets) lies entirely in a
member that contains its first (resp. last) element, so the Krull dimension of the union is the
supremum of their Krull dimensions with no finiteness hypothesis on the index family. In a prime
spectrum the closed sets are upper sets for the inclusion order, so this computes the dimension of a
union of closed subsets, for instance the support of `M ⧸ (I * J) M` as the union of the supports
of `M ⧸ I M` and `M ⧸ J M`.

## Main results

* `Order.height_prod_le`: the height of a pair is at most the sum of the heights of its
  components.
* `Order.krullDim_prod_le`: `dim (α × β) ≤ dim α + dim β`.
* `Order.krullDim_Icc_add_krullDim_Icc_le`: `dim [a, b] + dim [b, c] ≤ dim [a, c]` for
  `a ≤ b ≤ c`.
* `Order.krullDim_iUnion_of_isUpperSet`, `Order.krullDim_union_of_isUpperSet`: the Krull dimension
  of an arbitrary or binary union of upper sets is the supremum of their Krull dimensions.
* `Order.krullDim_preimage_ofDual`, `Order.krullDim_preimage_toDual`: pulling a subset back along
  `OrderDual.ofDual` or `OrderDual.toDual` preserves its Krull dimension.
* `Order.krullDim_iUnion_of_isLowerSet`, `Order.krullDim_union_of_isLowerSet`: the dual results for
  arbitrary and binary unions of lower sets.

## Implementation notes

`Order.height_prod_le` is proved by induction on a natural number bounding the sum of the heights
of the components, through `Order.height_le_coe_iff`: an element below a pair is a pair with one
component strictly smaller and the other no larger, and heights are strictly monotone where they
are finite. The lower bound for intervals bounds the Krull dimensions of `[a, b]` and `[b, c]` by
the height and the coheight of `b` in `[a, c]`, whose sum is at most the Krull dimension of
`[a, c]` (`Order.krullDim_eq_iSup_height_add_coheight_of_nonempty`). The lower-set union formulas
are deduced from the upper-set ones on `αᵒᵈ` via `Set.preimageOfDualOrderIso` and
`Order.krullDim_preimage_ofDual`.

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

/-- The Krull dimension of an arbitrary union of upper sets in a preorder is the supremum of their
Krull dimensions: every strictly increasing chain lies in a member containing its first element. -/
theorem krullDim_iUnion_of_isUpperSet {ι : Sort*} {f : ι → Set α}
    (hf : ∀ i, IsUpperSet (f i)) :
    krullDim ↥(⋃ i, f i) = ⨆ i, krullDim ↥(f i) :=
  le_antisymm
    (iSup_le fun p ↦ by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp p.head.property
      exact le_iSup_of_le i (LTSeries.length_le_krullDim
        ⟨p.length, fun k ↦ ⟨p k, hf i (p.monotone (Fin.zero_le k)) hi⟩, fun k ↦ p.step k⟩))
    (iSup_le fun i ↦ krullDim_le_of_strictMono
      (Set.inclusion (Set.subset_iUnion f i)) fun _ _ h ↦ h)

/-- The Krull dimension of a union of two upper sets is the larger of their Krull dimensions. -/
theorem krullDim_union_of_isUpperSet {s t : Set α} (hs : IsUpperSet s) (ht : IsUpperSet t) :
    krullDim ↥(s ∪ t) = max (krullDim ↥s) (krullDim ↥t) := by
  have hu : (⋃ b : Bool, if b then s else t) = s ∪ t := by ext x; simp [or_comm]
  rw [← hu, krullDim_iUnion_of_isUpperSet (f := fun b : Bool ↦ if b then s else t)
    (by rintro (_ | _) <;> simpa)]
  simp [iSup_bool_eq]

/-- Pulling a subset of a preorder back along `OrderDual.ofDual` preserves its Krull dimension. -/
@[simp]
theorem krullDim_preimage_ofDual (u : Set α) :
    krullDim ↥(OrderDual.ofDual ⁻¹' u) = krullDim ↥u :=
  (krullDim_eq_of_orderIso u.preimageOfDualOrderIso).trans krullDim_orderDual

/-- Pulling a subset of the order dual back along `OrderDual.toDual` preserves its Krull
dimension. -/
@[simp]
theorem krullDim_preimage_toDual (u : Set αᵒᵈ) :
    krullDim ↥(OrderDual.toDual ⁻¹' u) = krullDim ↥u :=
  (krullDim_eq_of_orderIso u.preimageToDualOrderIso).trans krullDim_orderDual

/-- The Krull dimension of an arbitrary union of lower sets in a preorder is the supremum of their
Krull dimensions: every strictly increasing chain lies in a member containing its last element. -/
theorem krullDim_iUnion_of_isLowerSet {ι : Sort*} {f : ι → Set α}
    (hf : ∀ i, IsLowerSet (f i)) :
    krullDim ↥(⋃ i, f i) = ⨆ i, krullDim ↥(f i) := by
  have hf' : ∀ i, IsUpperSet (OrderDual.ofDual ⁻¹' f i) :=
    fun i _ _ hab ha ↦ hf i (OrderDual.ofDual_le_ofDual.2 hab) ha
  rw [← krullDim_preimage_ofDual, Set.preimage_iUnion, krullDim_iUnion_of_isUpperSet hf']
  simp only [krullDim_preimage_ofDual]

/-- The Krull dimension of a union of two lower sets is the larger of their Krull dimensions. -/
theorem krullDim_union_of_isLowerSet {s t : Set α} (hs : IsLowerSet s) (ht : IsLowerSet t) :
    krullDim ↥(s ∪ t) = max (krullDim ↥s) (krullDim ↥t) := by
  have hs' : IsUpperSet (OrderDual.ofDual ⁻¹' s) :=
    fun _ _ hab ha ↦ hs (OrderDual.ofDual_le_ofDual.2 hab) ha
  have ht' : IsUpperSet (OrderDual.ofDual ⁻¹' t) :=
    fun _ _ hab ha ↦ ht (OrderDual.ofDual_le_ofDual.2 hab) ha
  rw [← krullDim_preimage_ofDual, Set.preimage_union,
    krullDim_union_of_isUpperSet hs' ht',
    krullDim_preimage_ofDual, krullDim_preimage_ofDual]

end Order
