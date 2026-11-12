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

`Pairwise.disjoint_iff_ne` characterizes disjointness in a pairwise disjoint family by inequality
of the indices, as soon as one of the two elements is different from bottom. It reduces
disjointness questions for such a family to questions about its labels.
-/

public section

namespace Pairwise

/-- In a pairwise disjoint family, an element different from bottom is disjoint from another
member of the family exactly when their indices differ. -/
theorem disjoint_iff_ne {α : Type*} [PartialOrder α] [OrderBot α] {ι : Type*} {f : ι → α}
    (h : Pairwise (Function.onFun Disjoint f)) {i j : ι} (hi : f i ≠ ⊥) :
    Disjoint (f i) (f j) ↔ i ≠ j :=
  ⟨fun hd hij ↦ hd.ne hi (congrArg f hij), fun hij ↦ h hij⟩

end Pairwise
