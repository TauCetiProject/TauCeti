/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Path

/-!
# Basic facts about paths

## Main declarations

* `Path.trans_mem_of_mem` -- a concatenation of two paths lying in a set lies in that set.
-/

public section

open Set

namespace Path

variable {X : Type*} [TopologicalSpace X]

/-- A concatenation of two paths lying in a set lies in that set. -/
theorem trans_mem_of_mem {x y z : X} (P : Path x y) (Q : Path y z) {s : Set X}
    (hP : ∀ t, P t ∈ s) (hQ : ∀ t, Q t ∈ s) : ∀ t, P.trans Q t ∈ s :=
  range_subset_iff.1 <| (Path.trans_range _ _).trans_subset <|
    union_subset (range_subset_iff.2 hP) (range_subset_iff.2 hQ)

end Path
