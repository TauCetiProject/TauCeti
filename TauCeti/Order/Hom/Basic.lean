/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Hom.Basic

/-!
# Pointwise order and strictly monotone equivalence for order embeddings

An order embedding `f : α ↪o β` carries the pointwise preorder and partial order lifted from
`α → β` (`f ≤ g ↔ ∀ x, f x ≤ g x`), matching the Mathlib instances on `α →o β`.

When `α` is a linear order, a strictly monotone map out of `α` is an order embedding
(`OrderEmbedding.ofStrictMono`), and every order embedding is strictly monotone. Together these
identify `α ↪o β` with the subtype of strictly monotone maps `α → β`
(`OrderEmbedding.equivSubtypeStrictMono`).
-/

public section

namespace OrderEmbedding

section Preorder

variable {α β : Type*} [Preorder α]

/-- The preorder structure on `α ↪o β` is pointwise inequality: `f ≤ g ↔ ∀ x, f x ≤ g x`. -/
instance instPreorder [Preorder β] : Preorder (α ↪o β) :=
  Preorder.lift DFunLike.coe

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
  invFun f := ofStrictMono f.1 f.2
  left_inv _ := DFunLike.coe_injective (coe_ofStrictMono _)
  right_inv _ := Subtype.ext (coe_ofStrictMono _)

end StrictMono

end OrderEmbedding
