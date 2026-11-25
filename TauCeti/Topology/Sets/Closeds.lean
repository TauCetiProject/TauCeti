/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sets.Closeds

/-!
# Membership in the complement of a closed set

A point lies in the open complement `TopologicalSpace.Closeds.compl s` of a closed set `s` exactly
when it does not lie in `s` (`TopologicalSpace.Closeds.mem_compl`).
-/

public section

namespace TopologicalSpace.Closeds

variable {α : Type*} [TopologicalSpace α]

/-- A point lies in the open complement of a closed set exactly when it does not lie in the closed
set. -/
@[simp]
lemma mem_compl {s : Closeds α} {x : α} : x ∈ s.compl ↔ x ∉ s :=
  Iff.rfl

end TopologicalSpace.Closeds
