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

An invariant subring for a monoid action remains invariant after restricting the action to a
submonoid, or to any other submonoid-like subobject such as a subgroup. This instance lets
constructions such as ramification groups be applied directly to a subgroup of the acting group.
-/

public section

namespace Submonoid

variable {M R : Type*} [Monoid M] [Ring R] [MulSemiringAction M R]
variable {S : Type*} [SetLike S M] [SubmonoidClass S M] (s : S)
variable (U : Subring R) [IsInvariantSubring M U]

/-- A subring invariant under a monoid action is invariant under the restricted action of every
submonoid-like subobject, such as a submonoid or a subgroup. -/
instance isInvariantSubring : IsInvariantSubring s U where
  smul_mem m _ hx := IsInvariantSubring.smul_mem (m : M) hx

end Submonoid
