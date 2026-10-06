/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Sum

/-!
# Tagging a partition of a finite set

Tagging vertices according to a predicate turns a partition into a disjoint sum. This formula
compares constructions on a single vertex type with constructions on disjoint vertex types.
-/

public section

namespace Finset

/-- Tagging a finite set according to a predicate gives the disjoint sum of its two parts. -/
@[simp]
theorem image_ite_inl_inr {α : Type*} [DecidableEq α] (s : Finset α)
    (p : α → Prop) [DecidablePred p] :
    s.image (fun x => if p x then Sum.inl x else Sum.inr x) =
      (s.filter p).disjSum (s.filter fun x => ¬ p x) := by
  ext (x | x) <;> simp [mem_image, apply_ite] <;> grind

end Finset
