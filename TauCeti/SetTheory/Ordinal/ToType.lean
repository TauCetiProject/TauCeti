/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Ordinal.Basic

/-!
# Inclusions between the canonical well-orders of ordinals

For ordinals `o₁ ≤ o₂`, every ordinal below `o₁` is below `o₂`, which gives an order embedding
`o₁.ToType ↪o o₂.ToType` of the canonical well-orders.

## Main definitions

* `TauCeti.toTypeOrderEmbeddingOfLE`: the order embedding `o₁.ToType ↪o o₂.ToType` for `o₁ ≤ o₂`.

## Main results

* `TauCeti.toOrd_toTypeOrderEmbeddingOfLE`: the embedding preserves the ordinal represented by
  each element.
-/

public section

universe u

open Ordinal

namespace TauCeti

variable {o₁ o₂ : Ordinal.{u}}

/-- For `o₁ ≤ o₂`, the order embedding `o₁.ToType ↪o o₂.ToType` sending the element representing
an ordinal `a < o₁` to the element representing `a < o₂`. -/
noncomputable def toTypeOrderEmbeddingOfLE (h : o₁ ≤ o₂) : o₁.ToType ↪o o₂.ToType :=
  OrderEmbedding.ofStrictMono
    (fun a => ToType.mk ⟨(ToType.toOrd a).val, (ToType.toOrd a).property.trans_le h⟩)
    fun _ _ hxy => ToType.mk.strictMono (Subtype.mk_lt_mk.2 (ToType.mk.symm.strictMono hxy))

/-- `toTypeOrderEmbeddingOfLE` preserves the ordinal represented by each element. -/
@[simp]
theorem toOrd_toTypeOrderEmbeddingOfLE (h : o₁ ≤ o₂) (a : o₁.ToType) :
    (ToType.toOrd (toTypeOrderEmbeddingOfLE h a) : Ordinal) = ToType.toOrd a :=
  congrArg Subtype.val (ToType.mk.symm_apply_apply _)

end TauCeti
