/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Quotients of a topological module by an open submodule

The quotient of a topological module by an open submodule is discrete; in particular the quotient
of a discrete topological module by any submodule is discrete, since in a discrete module every
submodule is open.

Mathlib's `QuotientAddGroup.discreteTopology` is the statement for the quotient of a topological
additive group by an *open* subgroup, and supplies the whole proof; because it is a theorem
rather than an instance (Mathlib notes that `IsOpen` would have to be a class for that), instance
search cannot use it, so this file records it for `M ⧸ p` as a theorem, and the discrete case as
an instance. This is the same bridge from `QuotientAddGroup` to `Submodule.Quotient` that
Mathlib's own `Submodule.isTopologicalAddGroup_quotient` and `Submodule.t3_quotient_of_isClosed`
provide.
-/

public section

namespace Submodule.Quotient

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [TopologicalSpace M]
  [SeparatelyContinuousAdd M]

/-- The quotient of a topological module by an open submodule is discrete. -/
theorem discreteTopology_of_isOpen (p : Submodule R M) (hp : IsOpen (p : Set M)) :
    DiscreteTopology (M ⧸ p) :=
  QuotientAddGroup.discreteTopology (N := p.toAddSubgroup) hp

/-- The quotient of a discrete topological module by a submodule is discrete. -/
instance discreteTopology [DiscreteTopology M] (p : Submodule R M) : DiscreteTopology (M ⧸ p) :=
  discreteTopology_of_isOpen p (isOpen_discrete _)

end Submodule.Quotient
