/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ClosedSubmodule

/-!
# Closed submodules are closed under negation

Mathlib registers a closed submodule as an `AddSubmonoidClass` and an `SMulMemClass`, but not as
an `AddSubgroupClass`, even when the scalars form a ring. This file adds that instance, so that the
generic subgroup membership lemmas (`neg_mem`, `sub_mem`, `sub_mem_comm_iff`, …) apply to closed
submodules directly, without passing through the underlying `Submodule`.

## Main declarations

* `ClosedSubmodule.instAddSubgroupClass`: a closed submodule over a ring is closed under
  negation, hence an additive subgroup class.
-/

public section

namespace ClosedSubmodule

variable {R M : Type*} [Ring R] [AddCommGroup M] [TopologicalSpace M] [Module R M]

/-- A closed submodule over a ring is an additive subgroup class: it is closed under negation
because its underlying submodule is. -/
instance instAddSubgroupClass : AddSubgroupClass (ClosedSubmodule R M) M where
  neg_mem {s} _ hx := s.toSubmodule.neg_mem hx

end ClosedSubmodule
