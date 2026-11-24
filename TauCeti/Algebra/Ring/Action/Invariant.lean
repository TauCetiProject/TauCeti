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
`TauCeti.isUnit_coe_fixedPoints_subalgebra_iff`) and divisibility under left-cancellative
multiplication (`TauCeti.coe_dvd_coe_fixedPoints_subsemiring_iff`,
`TauCeti.coe_dvd_coe_fixedPoints_subring_iff`, `TauCeti.coe_dvd_coe_fixedPoints_subalgebra_iff`),
together with the canonical ring isomorphism `TauCeti.fixedPointsSubringEquivSubalgebra`.
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
  ⟨fun hx ↦ ((isUnit_coe_fixedPoints_submonoid_iff (x := ⟨x.val, x.property⟩)).mp hx).map
    (⟨⟨fun z ↦ ⟨z.val, z.property⟩, rfl⟩, fun _ _ ↦ rfl⟩ : _ →* FixedPoints.subring B G),
   fun hx ↦ hx.map (FixedPoints.subring B G).subtype⟩

/-- Inclusion `FixedPoints.subalgebra A B G →ₐ[A] B` reflects and preserves units. -/
@[simp] theorem isUnit_coe_fixedPoints_subalgebra_iff {A B G : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    {x : FixedPoints.subalgebra A B G} : IsUnit (x : B) ↔ IsUnit x :=
  ⟨fun hx ↦ ((isUnit_coe_fixedPoints_submonoid_iff (x := ⟨x.val, x.property⟩)).mp hx).map
    (⟨⟨fun z ↦ ⟨z.val, z.property⟩, rfl⟩, fun _ _ ↦ rfl⟩ : _ →* FixedPoints.subalgebra A B G),
   fun hx ↦ hx.map (FixedPoints.subalgebra A B G).val⟩

section FixedPointsEquiv
variable (A B G : Type*) [CommSemiring A] [Ring B] [Algebra A B] [Monoid G]
  [MulSemiringAction G B] [SMulCommClass G A B]
/-- The canonical ring isomorphism `FixedPoints.subring B G ≃+* FixedPoints.subalgebra A B G`. -/
def fixedPointsSubringEquivSubalgebra :
    FixedPoints.subring B G ≃+* FixedPoints.subalgebra A B G :=
  { toFun x := ⟨x.val, x.property⟩, invFun x := ⟨x.val, x.property⟩,
    left_inv _ := rfl, right_inv _ := rfl, map_mul' _ _ := rfl, map_add' _ _ := rfl }
@[simp] theorem coe_fixedPointsSubringEquivSubalgebra_apply (x : FixedPoints.subring B G) :
    ((fixedPointsSubringEquivSubalgebra A B G x : FixedPoints.subalgebra A B G) : B) = x := by rfl
@[simp] theorem coe_fixedPointsSubringEquivSubalgebra_symm_apply
    (x : FixedPoints.subalgebra A B G) :
    (((fixedPointsSubringEquivSubalgebra A B G).symm x : FixedPoints.subring B G) : B) = x := by rfl
end FixedPointsEquiv

section FixedPointsDvd
variable {B G : Type*} [Monoid G]
/-- Inclusion `FixedPoints.subsemiring B G →+* B` under left-cancellative multiplication reflects
and preserves divisibility. -/
@[simp] theorem coe_dvd_coe_fixedPoints_subsemiring_iff [Semiring B] [IsLeftCancelMulZero B]
    [MulSemiringAction G B] {x y : FixedPoints.subsemiring B G} : (x : B) ∣ (y : B) ↔ x ∣ y := by
  refine ⟨fun ⟨q, hq⟩ ↦ ?_, (FixedPoints.subsemiring B G).subtype.map_dvd⟩
  by_cases hx : x = 0; · subst hx; exact ⟨0, Subtype.ext (by simpa using hq)⟩
  refine ⟨⟨q, fun g ↦ mul_left_cancel₀ (Subtype.coe_ne_coe.2 hx) ?_⟩, Subtype.ext hq⟩
  calc (x : B) * (g • q) = g • ((x : B) * q) := by rw [smul_mul', x.property g]
    _ = (x : B) * q := by rw [← hq, y.property g]
@[simp] theorem coe_dvd_coe_fixedPoints_subring_iff [Ring B] [IsLeftCancelMulZero B]
    [MulSemiringAction G B] {x y : FixedPoints.subring B G} : (x : B) ∣ (y : B) ↔ x ∣ y :=
  ⟨fun h ↦ let ⟨q, hq⟩ := (coe_dvd_coe_fixedPoints_subsemiring_iff
      (x := ⟨x.val, x.property⟩) (y := ⟨y.val, y.property⟩)).1 h
    ⟨⟨q.val, q.property⟩, Subtype.ext (congrArg Subtype.val hq)⟩,
   (FixedPoints.subring B G).subtype.map_dvd⟩
@[simp] theorem coe_dvd_coe_fixedPoints_subalgebra_iff {A : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [IsLeftCancelMulZero B] [MulSemiringAction G B] [SMulCommClass G A B]
    {x y : FixedPoints.subalgebra A B G} : (x : B) ∣ (y : B) ↔ x ∣ y :=
  ⟨fun h ↦ let ⟨q, hq⟩ := (coe_dvd_coe_fixedPoints_subsemiring_iff
      (x := ⟨x.val, x.property⟩) (y := ⟨y.val, y.property⟩)).1 h
    ⟨⟨q.val, q.property⟩, Subtype.ext (congrArg Subtype.val hq)⟩,
   (FixedPoints.subalgebra A B G).val.toRingHom.map_dvd⟩
end FixedPointsDvd

end TauCeti
