/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.Algebra.Ring.Action.Subobjects
public import Mathlib.Algebra.Ring.Action.Invariant
import TauCeti.Algebra.Group.Action.MulDistribMulAction

/-!
# Invariant subrings and fixed-point unit reflection

An invariant subring for a monoid action remains invariant after restricting the action to a
submonoid, or to any other submonoid-like subobject such as a subgroup. This instance lets
constructions such as ramification groups be applied directly to a subgroup of the acting group.

We also record that inclusions from `FixedPoints.subring B G` and `FixedPoints.subalgebra A B G`
into `B` reflect and preserve units (`TauCeti.isUnit_coe_fixedPoints_subring_iff`,
`TauCeti.isUnit_coe_fixedPoints_subalgebra_iff`).
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

namespace TauCeti

/-- Inclusion `FixedPoints.subring B G →+* B` reflects and preserves units. -/
@[simp] theorem isUnit_coe_fixedPoints_subring_iff {B G : Type*} [Ring B] [Monoid G]
    [MulSemiringAction G B] {x : FixedPoints.subring B G} : IsUnit (x : B) ↔ IsUnit x :=
  ⟨fun hx ↦ ((isUnit_coe_fixedPoints_submonoid_iff (x := ⟨x.1, x.2⟩)).mp hx).map
    (⟨⟨fun z ↦ ⟨z.1, z.2⟩, rfl⟩, fun _ _ ↦ rfl⟩ : _ →* FixedPoints.subring B G),
   fun hx ↦ hx.map (FixedPoints.subring B G).subtype⟩

/-- Inclusion `FixedPoints.subalgebra A B G →ₐ[A] B` reflects and preserves units. -/
@[simp] theorem isUnit_coe_fixedPoints_subalgebra_iff {A B G : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    {x : FixedPoints.subalgebra A B G} : IsUnit (x : B) ↔ IsUnit x :=
  ⟨fun hx ↦ ((isUnit_coe_fixedPoints_submonoid_iff (x := ⟨x.1, x.2⟩)).mp hx).map
    (⟨⟨fun z ↦ ⟨z.1, z.2⟩, rfl⟩, fun _ _ ↦ rfl⟩ : _ →* FixedPoints.subalgebra A B G),
   fun hx ↦ hx.map (FixedPoints.subalgebra A B G).val⟩

end TauCeti
