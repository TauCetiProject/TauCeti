/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.KrullDimension
public import Mathlib.Order.UpperLower.Basic

/-!
# Krull dimension of unions of upper and lower sets

In a preorder `α`, every strictly ascending chain in a union `⋃ i, f i` of upper sets (resp. lower
sets) lies wholly in a single member `f i` containing its head (resp. last element). Hence
`krullDim ↥(⋃ i, f i) = ⨆ i, krullDim (f i)` with no finiteness hypothesis on the index family.
In commutative algebra this applies directly to module supports in `PrimeSpectrum R`, which are
upper sets by `Module.mem_support_mono`.

## Main results

* `Order.krullDim_iUnion_of_isUpperSet`, `Order.krullDim_union_of_isUpperSet`
* `Order.krullDim_iUnion_of_isLowerSet`, `Order.krullDim_union_of_isLowerSet`
-/

public section

namespace Order

variable {α : Type*} [Preorder α]

/-- The Krull dimension of an arbitrary union of upper sets in a preorder is the supremum of their
Krull dimensions: every strictly increasing chain lies in a member containing its first element. -/
theorem krullDim_iUnion_of_isUpperSet {ι : Sort*} {f : ι → Set α}
    (hf : ∀ i, IsUpperSet (f i)) :
    krullDim (⋃ i, f i : Set α) = ⨆ i, krullDim (f i) :=
  le_antisymm
    (iSup_le fun p ↦ by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp p.head.2
      exact le_iSup_of_le i (LTSeries.length_le_krullDim
        ⟨p.length, fun k ↦ ⟨p k, hf i (p.monotone (Fin.zero_le k)) hi⟩, fun k ↦ p.step k⟩))
    (iSup_le fun i ↦ krullDim_le_of_strictMono
      (fun x : f i ↦ (⟨x.1, Set.subset_iUnion f i x.2⟩ : ↥(⋃ i, f i))) fun _ _ h ↦ h)

/-- The Krull dimension of the union of two upper sets in a preorder is the supremum of their Krull
dimensions. -/
theorem krullDim_union_of_isUpperSet {s t : Set α} (hs : IsUpperSet s) (ht : IsUpperSet t) :
    krullDim (s ∪ t : Set α) = krullDim s ⊔ krullDim t := by
  have hu : (⋃ b : Bool, if b then s else t) = s ∪ t := by ext x; simp [or_comm]
  rw [← hu, krullDim_iUnion_of_isUpperSet (f := fun b : Bool ↦ if b then s else t)
    (by rintro (_ | _) <;> simpa)]
  simp [iSup_bool_eq]

/-- The Krull dimension of an arbitrary union of lower sets in a preorder is the supremum of their
Krull dimensions: every strictly increasing chain lies in a member containing its last element. -/
theorem krullDim_iUnion_of_isLowerSet {ι : Sort*} {f : ι → Set α}
    (hf : ∀ i, IsLowerSet (f i)) :
    krullDim (⋃ i, f i : Set α) = ⨆ i, krullDim (f i) :=
  le_antisymm
    (iSup_le fun p ↦ by
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp p.last.2
      exact le_iSup_of_le i (LTSeries.length_le_krullDim
        ⟨p.length, fun k ↦ ⟨p k, hf i (p.monotone (Fin.le_last k)) hi⟩, fun k ↦ p.step k⟩))
    (iSup_le fun i ↦ krullDim_le_of_strictMono
      (fun x : f i ↦ (⟨x.1, Set.subset_iUnion f i x.2⟩ : ↥(⋃ i, f i))) fun _ _ h ↦ h)

/-- The Krull dimension of the union of two lower sets in a preorder is the supremum of their Krull
dimensions. -/
theorem krullDim_union_of_isLowerSet {s t : Set α} (hs : IsLowerSet s) (ht : IsLowerSet t) :
    krullDim (s ∪ t : Set α) = krullDim s ⊔ krullDim t := by
  have hu : (⋃ b : Bool, if b then s else t) = s ∪ t := by ext x; simp [or_comm]
  rw [← hu, krullDim_iUnion_of_isLowerSet (f := fun b : Bool ↦ if b then s else t)
    (by rintro (_ | _) <;> simpa)]
  simp [iSup_bool_eq]

end Order
