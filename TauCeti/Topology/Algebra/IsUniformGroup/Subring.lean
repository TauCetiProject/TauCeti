/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Subring.Defs
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-!
# The uniform structure on a subring

A subring carries the subspace uniformity, and the two facts one needs about it hold already for
the underlying subobject: `AddSubgroup.isUniformAddGroup` gives the additive group structure at
`S.toAddSubgroup`, and a countably generated uniformity is inherited by any subtype. Neither is
keyed on `Subring`, so typeclass search reaches neither at `↥S`.

That is the same keying gap `TauCeti.Topology.Algebra.IsUniformGroup.Submodule` fills for
submodules, and this file is its `Subring` counterpart. Both are uniform-space facts, which is why
they live beside each other here rather than in `TauCeti.Topology.Algebra.Ring.Subring`, whose
subject is the *topological* structure of a subring.

Only `NonAssocRing` is needed: that is what `Subring` itself asks, and the proofs use nothing but
the additive subgroup and the subtype uniformity.

## Main results

* `Subring.isUniformAddGroup`: `↥S` is a uniform additive group.
* `Subring.isCountablyGenerated_uniformity`: `↥S` inherits a countably generated uniformity.

## The consumer

Both are wanted at the ring of definition of a rational localisation, where
`TauCeti.Huber.PairOfDefinition.isStronglyNoetherian_completion` needs the completion of a subring
to be a uniform additive group with countably generated uniformity.
-/

public section

open Filter
open scoped Topology Uniformity

namespace Subring

/-- **A subring of a uniform additive group is a uniform additive group.** This is Mathlib's
`AddSubgroup.isUniformAddGroup` at `S.toAddSubgroup`, which typeclass search does not reach from a
`Subring`. -/
instance isUniformAddGroup {R : Type*} [NonAssocRing R] [UniformSpace R] [IsUniformAddGroup R]
    (S : Subring R) : IsUniformAddGroup S :=
  inferInstanceAs (IsUniformAddGroup S.toAddSubgroup)

/-- **A subring inherits a countably generated uniformity**, its uniformity being the one comapped
along the inclusion. -/
instance isCountablyGenerated_uniformity {R : Type*} [NonAssocRing R] [UniformSpace R]
    [(𝓤 R).IsCountablyGenerated] (S : Subring R) : (𝓤 S).IsCountablyGenerated :=
  inferInstanceAs ((𝓤 (S : Set R)).IsCountablyGenerated)

end Subring

end
