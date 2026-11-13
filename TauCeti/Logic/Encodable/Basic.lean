/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Encodable.Basic

/-!
# Decoding along embeddings

Some of Mathlib's encodable types sit inside others with the same codes, and Mathlib's decoders
respect this: decoding a number in a decidable subtype and forgetting the proof is decoding it in
the ambient type and keeping the result when it satisfies the predicate. This file records such
identities `(decode n).map f = (decode n).filter p`, for an embedding `f : α → β` whose image is
cut out by a Boolean test `p` on `β`: for `Subtype.val` and `Fin.val`, and for the sum of two
embeddings with this property. `Encodable.map_listMap_decode` extends them to lists.
-/

public section

namespace Encodable

/-- Decoding in a decidable subtype and forgetting the proof is decoding in the ambient type and
keeping the elements satisfying the predicate. -/
theorem map_val_decode_subtype {α : Type*} [Encodable α] {P : α → Prop} [DecidablePred P]
    (n : ℕ) :
    (decode (α := {a // P a}) n).map Subtype.val = (decode (α := α) n).filter fun a => P a := by
  simp only [decode, decodeSubtype]
  cases decode (α := α) n <;> simp [Option.filter]

/-- Decoding in `Fin k` and forgetting the bound is decoding in `ℕ` and keeping the numbers below
`k`. -/
theorem map_val_decode_fin (k n : ℕ) :
    (decode (α := Fin k) n).map Fin.val = (decode (α := ℕ) n).filter fun i => i < k := by
  rw [Fin.encodable, decode_ofEquiv, Option.map_map]
  -- `Fin.val ∘ Fin.equivSubtype.symm` is `Subtype.val` by definition of `Fin.equivSubtype`.
  exact map_val_decode_subtype n

/-- Decoding along the sum of two embeddings: if decoding along `f₁` and along `f₂` keeps exactly
the elements passing `p₁` and `p₂`, decoding along `Sum.map f₁ f₂` keeps exactly the elements
passing `Sum.elim p₁ p₂`. -/
theorem map_sumMap_decode {α₁ α₂ β₁ β₂ : Type*} [Encodable α₁] [Encodable α₂] [Encodable β₁]
    [Encodable β₂] {f₁ : α₁ → β₁} {f₂ : α₂ → β₂} {p₁ : β₁ → Bool} {p₂ : β₂ → Bool}
    (h₁ : ∀ n, (decode n).map f₁ = (decode n).filter p₁)
    (h₂ : ∀ n, (decode n).map f₂ = (decode n).filter p₂) (n : ℕ) :
    (decode (α := α₁ ⊕ α₂) n).map (Sum.map f₁ f₂) =
      (decode (α := β₁ ⊕ β₂) n).filter (Sum.elim p₁ p₂) := by
  simp only [decode_sum_val, decodeSum]
  cases Nat.bodd n <;> simp [Option.filter_map, Function.comp_def, ← h₁, ← h₂, Option.map_map]

end Encodable
