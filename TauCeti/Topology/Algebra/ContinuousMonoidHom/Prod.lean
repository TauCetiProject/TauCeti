/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The projections of a product of topological monoids

Mathlib's continuous projections `ContinuousMonoidHom.fst` and `ContinuousMonoidHom.snd` of a
product of topological monoids are built from the projections `MonoidHom.fst` and
`MonoidHom.snd`. This file records that their underlying homomorphisms are those projections, so
that statements about the continuous projections can be compared with statements about the
underlying homomorphisms by rewriting. The underlying homomorphism is stated through the coercion
from continuous homomorphisms to homomorphisms, which is the simp normal form of
`ContinuousMonoidHom.toMonoidHom` (`ContinuousMonoidHom.coe_toMonoidHom`).

## Main statements

* `ContinuousMonoidHom.coe_fst` and `ContinuousMonoidHom.coe_snd`: the underlying homomorphisms
  of the continuous projections.
-/

public section

namespace ContinuousMonoidHom

variable (A B : Type*) [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]

/-- The underlying homomorphism of the continuous first projection is `MonoidHom.fst`. -/
@[to_additive (attr := simp) /-- The underlying additive homomorphism of the continuous first
projection is `AddMonoidHom.fst`. -/]
theorem coe_fst : (fst A B : A × B →* A) = MonoidHom.fst A B :=
  rfl

/-- The underlying homomorphism of the continuous second projection is `MonoidHom.snd`. -/
@[to_additive (attr := simp) /-- The underlying additive homomorphism of the continuous second
projection is `AddMonoidHom.snd`. -/]
theorem coe_snd : (snd A B : A × B →* B) = MonoidHom.snd A B :=
  rfl

end ContinuousMonoidHom
