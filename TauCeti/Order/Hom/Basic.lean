/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Hom.Basic

/-!
# Order embeddings and order isomorphisms

For any `[LE α]`, an order embedding `f : α ↪o β` carries the pointwise preorder and partial order
lifted from `α → β` (`f ≤ g ↔ ∀ x, f x ≤ g x`), matching the Mathlib instances on `α →o β`.

When `α` is a linear order, a strictly monotone map out of `α` is an order embedding
(`OrderEmbedding.ofStrictMono`), and every order embedding is strictly monotone. Together these
identify `α ↪o β` with the subtype of strictly monotone maps `α → β`
(`OrderEmbedding.equivSubtypeStrictMono`).

`OrderIso.toOrderEmbedding_toEmbedding` records that viewing an order isomorphism `e : α ≃o β`
as an order embedding preserves its underlying `Function.Embedding`.
-/

public section

namespace OrderEmbedding

section Preorder

variable {α β : Type*} [LE α]

/-- The preorder structure on `α ↪o β` is pointwise inequality: `f ≤ g ↔ ∀ x, f x ≤ g x`. -/
instance instPreorder [Preorder β] : Preorder (α ↪o β) :=
  Preorder.lift DFunLike.coe

/-- The partial order structure on `α ↪o β` is pointwise inequality. -/
instance instPartialOrder [PartialOrder β] : PartialOrder (α ↪o β) :=
  PartialOrder.lift DFunLike.coe DFunLike.coe_injective

theorem le_def [Preorder β] {f g : α ↪o β} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_le_coe [Preorder β] {f g : α ↪o β} : (f : α → β) ≤ g ↔ f ≤ g :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_lt_coe [Preorder β] {f g : α ↪o β} : (f : α → β) < g ↔ f < g :=
  Iff.rfl

end Preorder

section StrictMono

variable {α β : Type*} [LinearOrder α] [Preorder β]

/-- For a linear order `α`, an order embedding `α ↪o β` is the same as a strictly monotone map
`α → β`. -/
@[expose, simps]
def equivSubtypeStrictMono : (α ↪o β) ≃ {f : α → β // StrictMono f} where
  toFun f := ⟨f, f.strictMono⟩
  invFun f := ofStrictMono f.val f.property
  left_inv _ := DFunLike.coe_injective (coe_ofStrictMono _)
  right_inv _ := Subtype.ext (coe_ofStrictMono _)

end StrictMono

end OrderEmbedding

namespace OrderIso

/-- Viewing an order isomorphism as an order embedding preserves the underlying
`Function.Embedding`. -/
@[simp]
theorem toOrderEmbedding_toEmbedding {α β : Type*} [LE α] [LE β] (e : α ≃o β) :
    e.toOrderEmbedding.toEmbedding = e.toEmbedding := by
  ext x
  rw [RelEmbedding.coe_toEmbedding, coe_toOrderEmbedding, ← RelIso.coe_toEmbedding]

end OrderIso
