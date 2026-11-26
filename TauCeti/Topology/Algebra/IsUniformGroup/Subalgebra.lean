/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# The uniform additive group structure on a subalgebra

A subalgebra `S : Subalgebra R A` over a commutative ring `R` in a ring `A` carries the subspace
uniformity, and its additive subgroup `S.toSubring.toAddSubgroup` inherits `IsUniformAddGroup` via
`AddSubgroup.isUniformAddGroup`. Because that instance is not keyed on `Subalgebra`, typeclass
search does not reach `IsUniformAddGroup S` directly; this file supplies
`Subalgebra.isUniformAddGroup` alongside `TauCeti.Topology.Algebra.IsUniformGroup.Subring` and
`TauCeti.Topology.Algebra.IsUniformGroup.Submodule`.
-/

public section

namespace Subalgebra

/-- **A subalgebra of a uniform additive group is a uniform additive group.** This forwards
`AddSubgroup.isUniformAddGroup` along `S.toSubring.toAddSubgroup`, which typeclass search does not
reach directly from a `Subalgebra`. -/
instance isUniformAddGroup {R A : Type*} [CommRing R] [Ring A] [Algebra R A] [UniformSpace A]
    [IsUniformAddGroup A] (S : Subalgebra R A) : IsUniformAddGroup S :=
  inferInstanceAs (IsUniformAddGroup S.toSubring.toAddSubgroup)

end Subalgebra
