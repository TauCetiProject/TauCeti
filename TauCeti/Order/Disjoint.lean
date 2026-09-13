/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Logic.Pairwise
public import Mathlib.Order.Disjoint

/-!
# Pairwise disjoint families

`Pairwise.disjoint_iff_ne` characterizes disjointness in a pairwise disjoint family of non-bottom
elements by inequality of the indices. It reduces disjointness questions for such a family to
questions about its labels.
-/

public section

namespace Pairwise

/-- In a pairwise disjoint family whose elements are all different from bottom, two elements are
disjoint exactly when their indices differ. -/
theorem disjoint_iff_ne {α : Type*} [PartialOrder α] [OrderBot α] {ι : Type*} {f : ι → α}
    (h : Pairwise (Function.onFun Disjoint f)) (hne : ∀ i, f i ≠ ⊥) (i j : ι) :
    Disjoint (f i) (f j) ↔ i ≠ j := by
  constructor
  · intro hd hij
    exact (Disjoint.ne (hne i) hd) (congrArg f hij)
  · intro hij
    exact h hij

end Pairwise
