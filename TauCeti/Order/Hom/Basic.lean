/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Hom.Basic

/-!
# Order embeddings and order isomorphisms

A strictly monotone map out of a linear order is an order embedding
(`OrderEmbedding.ofStrictMono`), and every order embedding is strictly monotone. Together these
identify the order embeddings `α ↪o β` with the subtype of strictly monotone maps `α → β`
(`OrderEmbedding.equivSubtypeStrictMono`).

`OrderIso.toOrderEmbedding_toEmbedding` records that viewing an order isomorphism `e : α ≃o β`
as an order embedding preserves its underlying `Function.Embedding`.
-/

public section

namespace OrderEmbedding

variable {α β : Type*} [LinearOrder α] [Preorder β]

/-- For a linear order `α`, an order embedding `α ↪o β` is the same as a strictly monotone map
`α → β`. -/
@[expose, simps]
def equivSubtypeStrictMono : (α ↪o β) ≃ {f : α → β // StrictMono f} where
  toFun f := ⟨f, f.strictMono⟩
  invFun f := ofStrictMono f.1 f.2
  left_inv _ := DFunLike.coe_injective (coe_ofStrictMono _)
  right_inv _ := Subtype.ext (coe_ofStrictMono _)

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
