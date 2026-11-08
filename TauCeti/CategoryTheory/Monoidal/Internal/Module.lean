/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Monoidal.Internal.Module

/-!
# Commutative monoid objects in `ModuleCat R`

Mathlib's `ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing` makes the carrier of a monoid
object in `ModuleCat R` a ring, whose multiplication is `x * y = μ (x ⊗ₜ y)`, and
`ModuleCat.monModuleEquivalenceAlgebra` identifies monoid objects in `ModuleCat R` with
`R`-algebras. This file records that the ring is commutative when the monoid object is
commutative, and restricts Mathlib's equivalence to an equivalence
`CommMon (ModuleCat R) ≌ CommAlgCat R` between commutative monoid objects in `ModuleCat R` and
commutative `R`-algebras.

## Main definitions

* `ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toCommRing`: the commutative ring structure on a
  commutative monoid object in `ModuleCat R`.
* `ModuleCat.commMonModuleEquivalenceCommAlgebra`: the equivalence
  `CommMon (ModuleCat R) ≌ CommAlgCat R`.
-/

public section

open CategoryTheory MonoidalCategory

namespace TauCeti

universe u

variable {R : Type u} [CommRing R]

open ModuleCat.MonModuleEquivalenceAlgebra in
/-- The commutative ring structure on a commutative monoid object in `ModuleCat R`: the ring
structure `ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toRing`, with multiplication
`x * y = μ (x ⊗ₜ y)`.

Mathlib makes `MonObj.toRing` only a scoped instance, since it does not round trip from a ring to
a monoid object and back; for the same reason, this is not an instance. -/
@[expose, instance_reducible]
noncomputable def _root_.ModuleCat.MonModuleEquivalenceAlgebra.MonObj.toCommRing
    (A : ModuleCat.{u} R) [MonObj A] [IsCommMonObj A] : CommRing A :=
  { MonObj.toRing A with
    mul_comm x y := congr($(ModuleCat.hom_ext_iff.mp (IsCommMonObj.mul_comm A)) (y ⊗ₜ x)) }

end TauCeti

namespace ModuleCat

universe u

variable {R : Type u} [CommRing R]

namespace CommMonModuleEquivalenceCommAlgebra

open MonModuleEquivalenceAlgebra

attribute [local instance] MonObj.toCommRing

/-- Converting a commutative monoid object in `ModuleCat R` to a bundled commutative algebra:
the restriction of `ModuleCat.MonModuleEquivalenceAlgebra.functor`. -/
@[expose]
noncomputable def functor : CommMon (ModuleCat.{u} R) ⥤ CommAlgCat.{u} R where
  obj A := CommAlgCat.of R A.X
  map f := CommAlgCat.ofHom (MonModuleEquivalenceAlgebra.functor.map f.hom).hom

/-- Converting a bundled commutative algebra `A` to a commutative monoid object in `ModuleCat R`,
with unit `Algebra.linearMap R A` and multiplication `LinearMap.mul' R A`: the restriction of
`ModuleCat.MonModuleEquivalenceAlgebra.inverse`. -/
@[expose]
noncomputable def inverse : CommAlgCat.{u} R ⥤ CommMon (ModuleCat.{u} R) where
  obj A :=
    letI := inverseObj (AlgCat.of R A)
    { X := ModuleCat.of R A
      comm.mul_comm := by
        ext : 1
        exact TensorProduct.ext' fun x y ↦ mul_comm y x }
  map f := CommMon.homMk (MonModuleEquivalenceAlgebra.inverse.map (AlgCat.ofHom f.hom))

@[simp]
theorem functor_map_apply {A B : CommMon (ModuleCat.{u} R)} (f : A ⟶ B) (x : A.X) :
    functor.map f x = f.hom.hom x :=
  rfl

@[simp]
theorem inverse_obj_X (A : CommAlgCat.{u} R) : (inverse.obj A).X = ModuleCat.of R A :=
  rfl

@[simp]
theorem inverse_map_hom_hom {A B : CommAlgCat.{u} R} (f : A ⟶ B) :
    (inverse.map f).hom.hom = ModuleCat.ofHom f.hom.toLinearMap :=
  rfl

end CommMonModuleEquivalenceCommAlgebra

open CommMonModuleEquivalenceCommAlgebra MonModuleEquivalenceAlgebra

attribute [local instance] MonObj.toCommRing

/-- The category of commutative monoid objects in `ModuleCat R` is equivalent to the category of
bundled commutative `R`-algebras. This is the restriction of
`ModuleCat.monModuleEquivalenceAlgebra`. -/
noncomputable def commMonModuleEquivalenceCommAlgebra :
    CommMon (ModuleCat.{u} R) ≌ CommAlgCat.{u} R where
  functor := functor
  inverse := inverse
  unitIso := NatIso.ofComponents
    (fun A ↦ CommMon.mkIso (Iso.refl _) (by ext; rfl) (by ext : 1; exact TensorProduct.ext rfl))
    (fun f ↦ by ext : 3; rfl)
  counitIso := NatIso.ofComponents
    (fun A ↦ CommAlgCat.isoMk
      { toFun := _root_.id
        invFun := _root_.id
        left_inv _ := rfl
        right_inv _ := rfl
        map_add' _ _ := rfl
        map_mul' x y := LinearMap.mul'_apply (R := R) (a := x) (b := y)
        commutes' _ := rfl })
    (fun f ↦ by ext; rfl)

@[simp]
theorem commMonModuleEquivalenceCommAlgebra_functor :
    commMonModuleEquivalenceCommAlgebra.functor =
      (functor : CommMon (ModuleCat.{u} R) ⥤ CommAlgCat.{u} R) :=
  (rfl)

@[simp]
theorem commMonModuleEquivalenceCommAlgebra_inverse :
    commMonModuleEquivalenceCommAlgebra.inverse =
      (inverse : CommAlgCat.{u} R ⥤ CommMon (ModuleCat.{u} R)) :=
  (rfl)

instance : (functor : CommMon (ModuleCat.{u} R) ⥤ CommAlgCat.{u} R).IsEquivalence := by
  rw [← commMonModuleEquivalenceCommAlgebra_functor]
  infer_instance

instance : (inverse : CommAlgCat.{u} R ⥤ CommMon (ModuleCat.{u} R)).IsEquivalence := by
  rw [← commMonModuleEquivalenceCommAlgebra_inverse]
  infer_instance

end ModuleCat
