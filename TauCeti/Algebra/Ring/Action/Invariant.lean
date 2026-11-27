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

We also record the canonical equivalences between fixed-point subobjects
(`TauCeti.fixedPointsSubmonoidEquivSubsemiring`, `TauCeti.fixedPointsSubsemiringEquivSubring`,
`TauCeti.fixedPointsSubsemiringEquivSubalgebra`, `TauCeti.fixedPointsSubringEquivSubalgebra`),
that inclusions from `FixedPoints.subring B G` and `FixedPoints.subalgebra A B G` into `B` reflect
and preserve units (`TauCeti.isUnit_coe_fixedPoints_subring_iff`,
`TauCeti.isUnit_coe_fixedPoints_subalgebra_iff`) and divisibility under left-cancellative
multiplication (`TauCeti.coe_dvd_coe_fixedPoints_subsemiring_iff`,
`TauCeti.coe_dvd_coe_fixedPoints_subring_iff`, `TauCeti.coe_dvd_coe_fixedPoints_subalgebra_iff`),
and the tower infrastructure `B^G ≤ B^H` (`TauCeti.fixedPointsSubalgebra_le`,
`TauCeti.fixedPointsSubalgebraAlgebra`, `TauCeti.coe_algebraMap_fixedPointsSubalgebra`,
`TauCeti.isScalarTower_fixedPointsSubalgebra`, `TauCeti.faithfulSMul_fixedPointsSubalgebra`).
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

section FixedPointsEquiv

/-- The canonical multiplicative equivalence
`FixedPoints.submonoid G B ≃* FixedPoints.subsemiring B G`. -/
def fixedPointsSubmonoidEquivSubsemiring (B G : Type*) [Semiring B] [Monoid G]
    [MulSemiringAction G B] : FixedPoints.submonoid G B ≃* FixedPoints.subsemiring B G where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem coe_fixedPointsSubmonoidEquivSubsemiring_apply {B G : Type*} [Semiring B] [Monoid G]
    [MulSemiringAction G B] (x : FixedPoints.submonoid G B) :
    ((fixedPointsSubmonoidEquivSubsemiring B G x : FixedPoints.subsemiring B G) : B) = x :=
  (rfl)

@[simp]
theorem coe_fixedPointsSubmonoidEquivSubsemiring_symm_apply {B G : Type*} [Semiring B] [Monoid G]
    [MulSemiringAction G B] (x : FixedPoints.subsemiring B G) :
    (((fixedPointsSubmonoidEquivSubsemiring B G).symm x : FixedPoints.submonoid G B) : B) = x :=
  (rfl)

/-- The canonical ring isomorphism `FixedPoints.subsemiring B G ≃+* FixedPoints.subring B G`. -/
def fixedPointsSubsemiringEquivSubring (B G : Type*) [Ring B] [Monoid G]
    [MulSemiringAction G B] : FixedPoints.subsemiring B G ≃+* FixedPoints.subring B G where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_fixedPointsSubsemiringEquivSubring_apply {B G : Type*} [Ring B] [Monoid G]
    [MulSemiringAction G B] (x : FixedPoints.subsemiring B G) :
    ((fixedPointsSubsemiringEquivSubring B G x : FixedPoints.subring B G) : B) = x :=
  (rfl)

@[simp]
theorem coe_fixedPointsSubsemiringEquivSubring_symm_apply {B G : Type*} [Ring B] [Monoid G]
    [MulSemiringAction G B] (x : FixedPoints.subring B G) :
    (((fixedPointsSubsemiringEquivSubring B G).symm x : FixedPoints.subsemiring B G) : B) = x :=
  (rfl)

/-- The canonical ring isomorphism
`FixedPoints.subsemiring B G ≃+* FixedPoints.subalgebra A B G`. -/
def fixedPointsSubsemiringEquivSubalgebra (A B G : Type*) [CommSemiring A] [Semiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] :
    FixedPoints.subsemiring B G ≃+* FixedPoints.subalgebra A B G where
  toFun x := ⟨x.val, x.property⟩
  invFun x := ⟨x.val, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem coe_fixedPointsSubsemiringEquivSubalgebra_apply {A B G : Type*} [CommSemiring A]
    [Semiring B] [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    (x : FixedPoints.subsemiring B G) :
    ((fixedPointsSubsemiringEquivSubalgebra A B G x : FixedPoints.subalgebra A B G) : B) = x :=
  (rfl)

@[simp]
theorem coe_fixedPointsSubsemiringEquivSubalgebra_symm_apply {A B G : Type*} [CommSemiring A]
    [Semiring B] [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    (x : FixedPoints.subalgebra A B G) :
    (((fixedPointsSubsemiringEquivSubalgebra A B G).symm x : FixedPoints.subsemiring B G) : B) =
      x :=
  (rfl)

variable (A B G : Type*) [CommSemiring A] [Ring B] [Algebra A B] [Monoid G]
  [MulSemiringAction G B] [SMulCommClass G A B]

/-- The canonical ring isomorphism `FixedPoints.subring B G ≃+* FixedPoints.subalgebra A B G`. -/
def fixedPointsSubringEquivSubalgebra :
    FixedPoints.subring B G ≃+* FixedPoints.subalgebra A B G :=
  (fixedPointsSubsemiringEquivSubring B G).symm.trans (fixedPointsSubsemiringEquivSubalgebra A B G)

@[simp]
theorem coe_fixedPointsSubringEquivSubalgebra_apply (x : FixedPoints.subring B G) :
    ((fixedPointsSubringEquivSubalgebra A B G x : FixedPoints.subalgebra A B G) : B) = x :=
  (rfl)

@[simp]
theorem coe_fixedPointsSubringEquivSubalgebra_symm_apply
    (x : FixedPoints.subalgebra A B G) :
    (((fixedPointsSubringEquivSubalgebra A B G).symm x : FixedPoints.subring B G) : B) = x :=
  (rfl)

end FixedPointsEquiv

/-- Inclusion `FixedPoints.subring B G →+* B` reflects and preserves units. -/
@[simp]
theorem isUnit_coe_fixedPoints_subring_iff {B G : Type*} [Ring B] [Monoid G]
    [MulSemiringAction G B] {x : FixedPoints.subring B G} : IsUnit (x : B) ↔ IsUnit x :=
  let e := (fixedPointsSubmonoidEquivSubsemiring B G).trans
    (fixedPointsSubsemiringEquivSubring B G).toMulEquiv
  (isUnit_coe_fixedPoints_submonoid_iff (x := e.symm x)).trans (MulEquiv.isUnit_map e.symm)

/-- Inclusion `FixedPoints.subalgebra A B G →ₐ[A] B` reflects and preserves units. -/
@[simp]
theorem isUnit_coe_fixedPoints_subalgebra_iff {A B G : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    {x : FixedPoints.subalgebra A B G} : IsUnit (x : B) ↔ IsUnit x :=
  let e := (fixedPointsSubmonoidEquivSubsemiring B G).trans
    (fixedPointsSubsemiringEquivSubalgebra A B G).toMulEquiv
  (isUnit_coe_fixedPoints_submonoid_iff (x := e.symm x)).trans (MulEquiv.isUnit_map e.symm)

section FixedPointsDvd

variable {B G : Type*} [Monoid G]

/-- Inclusion `FixedPoints.subsemiring B G →+* B` under left-cancellative multiplication reflects
and preserves divisibility. -/
@[simp]
theorem coe_dvd_coe_fixedPoints_subsemiring_iff [Semiring B] [IsLeftCancelMulZero B]
    [MulSemiringAction G B] {x y : FixedPoints.subsemiring B G} : (x : B) ∣ (y : B) ↔ x ∣ y := by
  refine ⟨fun ⟨q, hq⟩ ↦ ?_, (FixedPoints.subsemiring B G).subtype.map_dvd⟩
  by_cases hx : x = 0; · subst hx; exact ⟨0, Subtype.ext (by simpa using hq)⟩
  refine ⟨⟨q, fun g ↦ mul_left_cancel₀ (Subtype.coe_ne_coe.2 hx) ?_⟩, Subtype.ext hq⟩
  calc (x : B) * (g • q) = g • ((x : B) * q) := by rw [smul_mul', x.property g]
    _ = (x : B) * q := by rw [← hq, y.property g]

/-- Inclusion `FixedPoints.subring B G →+* B` under left-cancellative multiplication reflects and
preserves divisibility. -/
@[simp]
theorem coe_dvd_coe_fixedPoints_subring_iff [Ring B] [IsLeftCancelMulZero B]
    [MulSemiringAction G B] {x y : FixedPoints.subring B G} : (x : B) ∣ (y : B) ↔ x ∣ y :=
  let e := fixedPointsSubsemiringEquivSubring B G
  (coe_dvd_coe_fixedPoints_subsemiring_iff (x := e.symm x) (y := e.symm y)).trans
    (map_dvd_iff e.symm.toMulEquiv)

/-- Inclusion `FixedPoints.subalgebra A B G →ₐ[A] B` under left-cancellative multiplication reflects
and preserves divisibility. -/
@[simp]
theorem coe_dvd_coe_fixedPoints_subalgebra_iff {A : Type*} [CommSemiring A] [Semiring B]
    [Algebra A B] [IsLeftCancelMulZero B] [MulSemiringAction G B] [SMulCommClass G A B]
    {x y : FixedPoints.subalgebra A B G} : (x : B) ∣ (y : B) ↔ x ∣ y :=
  let e := fixedPointsSubsemiringEquivSubalgebra A B G
  (coe_dvd_coe_fixedPoints_subsemiring_iff (x := e.symm x) (y := e.symm y)).trans
    (map_dvd_iff e.symm.toMulEquiv)

end FixedPointsDvd

section FixedPointsTower

/-- Elements fixed by `G` are fixed by any submonoid-like subobject `H` of `G`. -/
theorem fixedPointsSubalgebra_le {A B G S : Type*} [CommSemiring A] [Semiring B] [Algebra A B]
    [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B] [SetLike S G] [SubmonoidClass S G]
    (H : S) : FixedPoints.subalgebra A B G ≤ FixedPoints.subalgebra A B H :=
  fun _ hx h ↦ hx (h : G)

/-- The `FixedPoints.subalgebra A B G`-algebra structure on `FixedPoints.subalgebra A B H` given
by inclusion. -/
@[instance_reducible]
def fixedPointsSubalgebraAlgebra (A B : Type*) {G S : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    [SetLike S G] [SubmonoidClass S G] (H : S) :
    Algebra (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H) :=
  (Subalgebra.inclusion (fixedPointsSubalgebra_le H)).toAlgebra

/-- The algebra map `FixedPoints.subalgebra A B G →ₐ[A] FixedPoints.subalgebra A B H` acts as the
identity on underlying elements of `B`. -/
@[simp]
theorem coe_algebraMap_fixedPointsSubalgebra {A B G S : Type*} [CommSemiring A] [CommSemiring B]
    [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    [SetLike S G] [SubmonoidClass S G] (H : S) (x : FixedPoints.subalgebra A B G) :
    letI := fixedPointsSubalgebraAlgebra A B H
    ((algebraMap (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H) x :
      FixedPoints.subalgebra A B H) : B) = x :=
  (rfl)

/-- Scalar tower `B^G → B^H → B` for `H ≤ G`. -/
theorem isScalarTower_fixedPointsSubalgebra (A B : Type*) {G S : Type*} [CommSemiring A]
    [CommSemiring B] [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    [SetLike S G] [SubmonoidClass S G] (H : S) :
    letI := fixedPointsSubalgebraAlgebra A B H
    IsScalarTower (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H) B :=
  let _ := fixedPointsSubalgebraAlgebra A B H
  Subalgebra.inclusion.isScalarTower_right (fixedPointsSubalgebra_le H) B

/-- Inclusion `B^G → B^H` is faithful. -/
theorem faithfulSMul_fixedPointsSubalgebra (A B : Type*) {G S : Type*} [CommSemiring A]
    [CommSemiring B] [Algebra A B] [Monoid G] [MulSemiringAction G B] [SMulCommClass G A B]
    [SetLike S G] [SubmonoidClass S G] (H : S) :
    letI := fixedPointsSubalgebraAlgebra A B H
    FaithfulSMul (FixedPoints.subalgebra A B G) (FixedPoints.subalgebra A B H) :=
  let _ := fixedPointsSubalgebraAlgebra A B H
  Subalgebra.inclusion.faithfulSMul (fixedPointsSubalgebra_le H)

end FixedPointsTower

end TauCeti
