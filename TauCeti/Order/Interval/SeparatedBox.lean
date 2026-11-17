/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Sub.Defs

/-!
# Separated box endpoints in preorders

Two endpoint families `a, b : ι → α` between preorders satisfy `TauCeti.IsSeparatedBox a b`
when `a i ≤ b i` for every `i` and `b i ≤ a j` whenever `i < j`.

This purely order-theoretic condition describes separated product boxes along an ordered index
set, and is preserved under precomposition with strictly monotone index maps
(`IsSeparatedBox.comp`) and right subtraction in an ordered-subtraction setting
(`IsSeparatedBox.sub_const`).
-/

public section

namespace TauCeti

/-- Box endpoints `a, b : ι → α` are separated when each coordinate interval is well-ordered
(`a i ≤ b i`) and earlier right endpoints do not exceed later left endpoints. -/
def IsSeparatedBox {ι α : Type*} [Preorder ι] [Preorder α] (a b : ι → α) : Prop :=
  (∀ i, a i ≤ b i) ∧ ∀ ⦃i j : ι⦄, i < j → b i ≤ a j

/-- Explicit characterization of separated box endpoints. -/
theorem isSeparatedBox_iff {ι α : Type*} [Preorder ι] [Preorder α] {a b : ι → α} :
    IsSeparatedBox a b ↔ (∀ i, a i ≤ b i) ∧ ∀ ⦃i j : ι⦄, i < j → b i ≤ a j :=
  Iff.rfl

/-- Construct `IsSeparatedBox` from coordinatewise order and strict-index separation. -/
theorem IsSeparatedBox.mk {ι α : Type*} [Preorder ι] [Preorder α] {a b : ι → α}
    (hle : ∀ i, a i ≤ b i) (hsep : ∀ ⦃i j : ι⦄, i < j → b i ≤ a j) : IsSeparatedBox a b :=
  ⟨hle, hsep⟩

/-- Separated box endpoints satisfy `a i ≤ b i` in every coordinate. -/
theorem IsSeparatedBox.le {ι α : Type*} [Preorder ι] [Preorder α] {a b : ι → α}
    (h : IsSeparatedBox a b) (i : ι) : a i ≤ b i :=
  h.1 i

/-- Separated box endpoints place `b i` at or before `a j` whenever `i < j`. -/
theorem IsSeparatedBox.le_of_lt {ι α : Type*} [Preorder ι] [Preorder α] {a b : ι → α}
    (h : IsSeparatedBox a b) {i j : ι} (hij : i < j) : b i ≤ a j :=
  h.2 hij

/-- Precomposing separated box endpoints with a strictly monotone index map preserves separation. -/
theorem IsSeparatedBox.comp {ι ι' α : Type*} [Preorder ι] [Preorder ι'] [Preorder α]
    {a b : ι → α} (h : IsSeparatedBox a b) {f : ι' → ι} (hf : StrictMono f) :
    IsSeparatedBox (a ∘ f) (b ∘ f) :=
  IsSeparatedBox.mk (fun i => h.le (f i)) fun _ _ hij => h.le_of_lt (hf hij)

/-- Subtracting a constant on the right preserves separation of box endpoints. -/
theorem IsSeparatedBox.sub_const {ι α : Type*} [Preorder ι] [Preorder α] [AddCommSemigroup α]
    [Sub α] [OrderedSub α] {a b : ι → α} (h : IsSeparatedBox a b) (c : α) :
    IsSeparatedBox (fun i => a i - c) (fun i => b i - c) :=
  IsSeparatedBox.mk (fun i => tsub_le_tsub_right (h.le i) c) fun _ _ hij =>
    tsub_le_tsub_right (h.le_of_lt hij) c

end TauCeti
