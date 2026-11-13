/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Algebra.Module.Submodule.Lattice
public import Mathlib.LinearAlgebra.Prod

/-!
# A submodule of a topological module is a topological module

A submodule carries the subspace topology. Of the three continuity classes that make that
topology a module topology, Mathlib supplies **two outright** and **one under extra hypotheses**:

* `SMulMemClass.continuousSMul` gives the jointly continuous action `A × ↥p → ↥p` on any `SetLike`
  subobject, with no side conditions beyond the ambient `ContinuousSMul A M`.
* the unnamed `SetLike` instance `instContinuousConstSMulSubtypeMem` of
  `Mathlib.Topology.Algebra.Module.Basic` gives `ContinuousConstSMul A ↥p` on any subobject
  closed under the action, asking only `ContinuousConstSMul A M` and no topology on the scalars.
* `Submodule.isTopologicalAddGroup` gives `ContinuousAdd ↥p`, but only for a `Ring A` acting on
  an `AddCommGroup M` that is already a topological *group*.

So there is exactly one gap, and it is what this file fills: **`ContinuousAdd` at the generality
of its own class**. An `AddCommMonoid` ambient with `ContinuousAdd` is outside
`Submodule.isTopologicalAddGroup`'s hypotheses, and `AddSubmonoid.continuousAdd`, which is at the
right generality, is not keyed on `Submodule`.

## Main results

* `Submodule.continuousAdd`: addition on `↥p` is continuous, asking only `ContinuousAdd` of the
  ambient module rather than a topological group structure.
* `AddSubgroup.discreteTopology_toIntSubmodule`: the `ℤ`-submodule of a discrete additive
  subgroup is discrete, so that a discrete subgroup can be fed to the `ℤ`-lattice API.
* `Submodule.discreteTopology_toAddSubgroup`: conversely, the additive subgroup of a discrete
  submodule is discrete, so that the quotient group by a lattice carries the manifold structure
  of a quotient by a discrete subgroup.
* `Submodule.instDiscreteTopologyProd`: the product of two discrete submodules is discrete.
-/

public section

namespace Submodule

variable {A M : Type*} [Semiring A] [AddCommMonoid M] [TopologicalSpace M] [Module A M]

/-- **Addition on a submodule is continuous.** Mathlib has this for an `AddSubmonoid`, and for a
`Submodule` only through `Submodule.isTopologicalAddGroup`, which needs the ambient module to be a
topological group. A `ContinuousAdd` ambient is enough. -/
instance continuousAdd [ContinuousAdd M] (p : Submodule A M) : ContinuousAdd p :=
  inferInstanceAs (ContinuousAdd p.toAddSubmonoid)

end Submodule

/-- **The `ℤ`-submodule of a discrete additive subgroup is discrete**: the two carry the same
subspace topology. -/
instance AddSubgroup.discreteTopology_toIntSubmodule {M : Type*} [AddCommGroup M]
    [TopologicalSpace M] (H : AddSubgroup M) [DiscreteTopology H] :
    DiscreteTopology H.toIntSubmodule :=
  inferInstanceAs (DiscreteTopology H)

/-- **The additive subgroup of a discrete submodule is discrete**: the two carry the same
subspace topology. -/
instance Submodule.discreteTopology_toAddSubgroup {R M : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [TopologicalSpace M] (p : Submodule R M) [DiscreteTopology p] :
    DiscreteTopology p.toAddSubgroup :=
  inferInstanceAs (DiscreteTopology p)

/-- The product of two discrete submodules is a discrete submodule of the product module. -/
instance Submodule.instDiscreteTopologyProd {R M M₂ : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [TopologicalSpace M] [AddCommMonoid M₂] [Module R M₂] [TopologicalSpace M₂]
    (p : Submodule R M) (q : Submodule R M₂) [DiscreteTopology p] [DiscreteTopology q] :
    DiscreteTopology (p.prod q) :=
  DiscreteTopology.of_continuous_injective (f := p.prodEquiv q)
    ((continuous_subtype_val.fst.subtype_mk _).prodMk (continuous_subtype_val.snd.subtype_mk _))
    (p.prodEquiv q).injective
