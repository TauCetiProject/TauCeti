/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Action.Subobjects
public import Mathlib.Algebra.Ring.Action.Invariant

/-!
# Invariant subrings under restricted actions

An invariant subring for a group action remains invariant after restricting the action to a
subgroup. This instance lets constructions such as ramification groups be applied directly to a
subgroup of the acting group.
-/

public section

namespace Subgroup

variable {G R : Type*} [Group G] [Ring R] [MulSemiringAction G R]
variable (H : Subgroup G) (S : Subring R) [IsInvariantSubring G S]

/-- A subring invariant under a group action is invariant under the restricted action of every
subgroup. -/
instance isInvariantSubring : IsInvariantSubring H S where
  smul_mem h _ hx := IsInvariantSubring.smul_mem (h : G) hx

end Subgroup
