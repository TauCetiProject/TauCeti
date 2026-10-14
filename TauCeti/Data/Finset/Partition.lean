/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sum

/-!
# Tagging a partition of a finite set

Tagging vertices according to a predicate embeds a type into its disjoint sum with itself.
The finite-set image formula compares constructions on a single vertex type with constructions
on disjoint vertex types.
-/

public section

namespace TauCeti

/-- Embed a type into its disjoint sum with itself, tagging elements on the left when they
satisfy `p` and on the right otherwise. -/
def partitionEmbedding {α : Type*} (p : α → Prop) [DecidablePred p] : α ↪ α ⊕ α where
  toFun x := if p x then Sum.inl x else Sum.inr x
  inj' := Function.LeftInverse.injective (g := Sum.elim id id) fun x => by
    simp [apply_ite]

/-- The partition embedding tags an element according to the predicate. -/
@[simp]
theorem partitionEmbedding_apply {α : Type*} (p : α → Prop) [DecidablePred p] (x : α) :
    partitionEmbedding p x = if p x then Sum.inl x else Sum.inr x := (rfl)

end TauCeti

namespace Finset

/-- Tagging a finite set according to a predicate gives the disjoint sum of its two parts. -/
@[simp]
theorem image_partitionEmbedding {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    s.image (TauCeti.partitionEmbedding p) =
      (s.filter p).disjSum (s.filter fun x => ¬ p x) := by
  ext (x | x) <;> simp [mem_image, apply_ite] <;> grind

end Finset
