/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Ring

/-!
# Representable presheaves of rings

Let `C` be a braided cartesian monoidal category. If an object `X` of `C` represents a presheaf
of rings `F`, that is, `Hom(Y, X) ≃ F(Y)` naturally in `Y`, then `X` is a ring object of `C`
(`CategoryTheory.RingObj.ofRepresentableBy`): its zero, addition, negation, one and
multiplication are the morphisms which correspond, under the representation, to the operations of
the rings `F(Y)`. For this structure the representation is an isomorphism of rings
`Hom(Y, X) ≃+* F(Y)` for every `Y` (`CategoryTheory.RingObj.homRingEquivOfRepresentableBy`). If
`F` is a presheaf of commutative rings, then `X` is a commutative ring object
(`CategoryTheory.CommRingObj.ofRepresentableBy`), with the same ring isomorphisms
(`CategoryTheory.CommRingObj.homRingEquivOfRepresentableBy`).

This is the ring analogue of Mathlib's `MonObj.ofRepresentableBy`, `GrpObj.ofRepresentableBy` and
`IsCommMonObj.ofRepresentableBy`, and is how ring schemes such as affine space are constructed
from their functors of points.
-/

public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped MonObj AddMonObj

namespace CategoryTheory

universe w v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] (X : C)

namespace RingObj

variable (F : Cᵒᵖ ⥤ RingCat.{w}) (α : (F ⋙ forget _).RepresentableBy X)

/-- The additive group object structure of `X` whose operations correspond, under the
representation `α`, to the additive groups of the rings `F(Y)`. -/
private abbrev addGrpObjOfRepresentableBy : AddGrpObj X :=
  .ofRepresentableBy X (F ⋙ forget₂ RingCat AddCommGrpCat ⋙ forget₂ AddCommGrpCat AddGrpCat) α

/-- The monoid object structure of `X` whose operations correspond, under the representation
`α`, to the multiplicative monoids of the rings `F(Y)`. -/
private abbrev monObjOfRepresentableBy : MonObj X :=
  .ofRepresentableBy X (F ⋙ forget₂ RingCat SemiRingCat ⋙ forget₂ SemiRingCat MonCat) α

private lemma homEquiv'_add (Y : C) (a b : Y ⟶ X) :
    letI := addGrpObjOfRepresentableBy X F α
    α.homEquiv' (a + b) = α.homEquiv' a + α.homEquiv' b := by
  let := addGrpObjOfRepresentableBy X F α
  -- `a + b` is `lift a b ≫ σ` (`Hom.add_def`) and `σ` is the `add` field of
  -- `AddMonObj.ofRepresentableBy`; `AddMonObj.ofRepresentableBy_add` states it with the addition
  -- of `F(Y)` seen through `AddMonCat`, on which `map_add` does not fire, so restate the goal with
  -- the ring addition of `F(Y)`
  change α.homEquiv' (lift a b ≫ α.homEquiv'.symm (α.homEquiv' (fst X X) +
    α.homEquiv' (snd X X))) = α.homEquiv' a + α.homEquiv' b
  simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_add]
  simp only [← α.homEquiv'_comp, lift_fst, lift_snd]

private lemma homEquiv'_mul (Y : C) (a b : Y ⟶ X) :
    letI := monObjOfRepresentableBy X F α
    α.homEquiv' (a * b) = α.homEquiv' a * α.homEquiv' b := by
  let := monObjOfRepresentableBy X F α
  -- as for `homEquiv'_add`, restate `a * b = lift a b ≫ μ` with the ring multiplication of `F(Y)`
  change α.homEquiv' (lift a b ≫ α.homEquiv'.symm (α.homEquiv' (fst X X) *
    α.homEquiv' (snd X X))) = α.homEquiv' a * α.homEquiv' b
  simp only [α.homEquiv'_comp, Equiv.apply_symm_apply, map_mul]
  simp only [← α.homEquiv'_comp, lift_fst, lift_snd]

variable [BraidedCategory C]

/-- If `X` represents a presheaf of rings `F`, then `X` is a ring object: its operations
correspond under the representation to the ring operations of the `F(Y)`
(`RingObj.homRingEquivOfRepresentableBy`). -/
@[instance_reducible]
def ofRepresentableBy : RingObj X :=
  letI := addGrpObjOfRepresentableBy X F α
  letI := monObjOfRepresentableBy X F α
  { add_comm := by
      -- the addition `σ` is the sum of the two projections, which the braiding exchanges
      have h : fst X X + snd X X = σ := by
        rw [Hom.add_def, lift_fst_snd, Category.id_comp]
      rw [← h, AddMonObj.comp_add, braiding_hom_fst, braiding_hom_snd]
      exact α.homEquiv'.injective (by
        rw [homEquiv'_add, homEquiv'_add, _root_.add_comm])
    mul_add := (mul_add_iff X).2 fun Y a b c ↦ α.homEquiv'.injective (by
      simp only [homEquiv'_add, homEquiv'_mul, _root_.mul_add])
    add_mul := (add_mul_iff X).2 fun Y a b c ↦ α.homEquiv'.injective (by
      simp only [homEquiv'_add, homEquiv'_mul, _root_.add_mul]) }

open scoped RingObj in
/-- For the ring object structure `RingObj.ofRepresentableBy`, the representation `α` is an
isomorphism of rings `Hom(Y, X) ≃+* F(Y)`. -/
def homRingEquivOfRepresentableBy (Y : C) :
    letI := RingObj.ofRepresentableBy X F α
    (Y ⟶ X) ≃+* F.obj (op Y) :=
  letI := RingObj.ofRepresentableBy X F α
  { toEquiv := α.homEquiv'
    map_add' := homEquiv'_add X F α Y
    map_mul' := homEquiv'_mul X F α Y }

open scoped RingObj in
/-- The ring isomorphism `homRingEquivOfRepresentableBy` is the representation. -/
lemma homRingEquivOfRepresentableBy_apply (Y : C) (f : Y ⟶ X) :
    letI := RingObj.ofRepresentableBy X F α
    homRingEquivOfRepresentableBy X F α Y f = α.homEquiv' f :=
  (rfl)

open scoped RingObj in
/-- The inverse of the ring isomorphism `homRingEquivOfRepresentableBy` is the inverse of the
representation. -/
lemma homRingEquivOfRepresentableBy_symm_apply (Y : C) (x : F.obj (op Y)) :
    letI := RingObj.ofRepresentableBy X F α
    (homRingEquivOfRepresentableBy X F α Y).symm x = α.homEquiv'.symm x :=
  (rfl)

end RingObj

namespace CommRingObj

variable [BraidedCategory C] (F : Cᵒᵖ ⥤ CommRingCat.{w}) (α : (F ⋙ forget _).RepresentableBy X)

/-- If `X` represents a presheaf of commutative rings `F`, then `X` is a commutative ring object:
the ring object `RingObj.ofRepresentableBy` of the underlying presheaf of rings, whose
multiplication is commutative. -/
@[instance_reducible]
def ofRepresentableBy : CommRingObj X :=
  letI := RingObj.ofRepresentableBy X (F ⋙ forget₂ CommRingCat RingCat) α
  { mul_comm := by
      -- the monoid object structures of `RingObj.ofRepresentableBy` and of
      -- `IsCommMonObj.ofRepresentableBy` are equal only after unfolding the forgetful functors,
      -- which `exact` does but the structure instance notation `__ :=` does not
      exact (IsCommMonObj.ofRepresentableBy X (F ⋙ forget₂ CommRingCat CommMonCat) α).mul_comm }

open scoped CommRingObj in
/-- For the commutative ring object structure `CommRingObj.ofRepresentableBy`, the
representation `α` is an isomorphism of commutative rings `Hom(Y, X) ≃+* F(Y)`: the ring
isomorphism `RingObj.homRingEquivOfRepresentableBy` of the underlying presheaf of rings. -/
def homRingEquivOfRepresentableBy (Y : C) :
    letI := ofRepresentableBy X F α
    (Y ⟶ X) ≃+* F.obj (op Y) :=
  RingObj.homRingEquivOfRepresentableBy X (F ⋙ forget₂ CommRingCat RingCat) α Y

open scoped CommRingObj in
/-- The ring isomorphism `homRingEquivOfRepresentableBy` is the representation. -/
lemma homRingEquivOfRepresentableBy_apply (Y : C) (f : Y ⟶ X) :
    letI := ofRepresentableBy X F α
    homRingEquivOfRepresentableBy X F α Y f = α.homEquiv' f :=
  (rfl)

open scoped CommRingObj in
/-- The inverse of the ring isomorphism `homRingEquivOfRepresentableBy` is the inverse of the
representation. -/
lemma homRingEquivOfRepresentableBy_symm_apply (Y : C) (x : F.obj (op Y)) :
    letI := ofRepresentableBy X F α
    (homRingEquivOfRepresentableBy X F α Y).symm x = α.homEquiv'.symm x :=
  (rfl)

end CommRingObj

end CategoryTheory
