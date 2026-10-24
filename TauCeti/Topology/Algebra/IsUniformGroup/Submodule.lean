/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# The uniform structure on a submodule

A submodule carries the subspace uniformity, and both facts one needs about it hold for the
underlying subobject: `Subgroup.isUniformGroup` gives the additive version for an `AddSubgroup`,
and the countably generated uniformity is inherited by any subtype. Neither is keyed on
`Submodule`, so typeclass search does not find either at `↥p`.

Mathlib works around the first by hand: `Topology/Algebra/Module/FiniteDimension.lean` installs
`s.toAddSubgroup.isUniformAddGroup` locally at two separate proofs, once with `let` and once with
`haveI`.

## Main results

* `Submodule.isUniformAddGroup`: `↥p` is a uniform additive group.
* `Submodule.isCountablyGenerated_uniformity`: `↥p` inherits a countably generated uniformity.

## Use

The open mapping theorems over a ring with a zero sequence of units state metrisability of a module
as a countably generated uniformity on a uniform additive group; for the target, completeness and
these two properties are what make it a Baire space. These instances let the theorems be applied
when one side is a submodule. A strict map is a map that is open onto its image, so strictness is
a statement about the corestriction `f.rangeRestrict : M → ↥(LinearMap.range f)`, whose target is
a submodule; this is how `TauCeti.HasZeroSequenceOfUnits.isStrictMap_of_isClosed_range` uses them.
A closed submodule is complete by `IsClosed.completeSpace_coe`, and
`TauCeti.Huber.isClosed_of_module_finite_topologicalClosure` works inside the topological closure
of a submodule to show that a submodule with module-finite closure is closed, which gives the
closedness of every submodule of a noetherian module over a complete Tate ring (Wedhorn, *Adic
Spaces*, Proposition 6.17).
-/

public section

open scoped Uniformity

namespace Submodule

/-- **A submodule of a uniform additive group is a uniform additive group.** This is
`AddSubgroup.isUniformAddGroup` at `p.toAddSubgroup`, which typeclass search does not reach from a
`Submodule`; Mathlib's `Topology/Algebra/Module/FiniteDimension.lean` supplies it by hand twice. -/
instance isUniformAddGroup {A M : Type*} [Ring A] [AddCommGroup M] [UniformSpace M]
    [IsUniformAddGroup M] [Module A M] (p : Submodule A M) : IsUniformAddGroup p :=
  inferInstanceAs (IsUniformAddGroup p.toAddSubgroup)

/-- **A submodule inherits a countably generated uniformity**, since its uniformity is the one
comapped along the inclusion. This is the hypothesis the open mapping theorem states
metrisability as. -/
instance isCountablyGenerated_uniformity {A M : Type*} [Semiring A] [AddCommMonoid M]
    [UniformSpace M] [(𝓤 M).IsCountablyGenerated] [Module A M] (p : Submodule A M) :
    (𝓤 p).IsCountablyGenerated :=
  inferInstanceAs ((𝓤 (p : Set M)).IsCountablyGenerated)

end Submodule
