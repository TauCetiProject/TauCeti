/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv

/-!
# Simultaneous universe lifting of algebras and their automorphisms

Lift both the scalar ring and an algebra, using Mathlib's `ULift.algebra'` scalar action.
The automorphism group of the lifted algebra is identified with the original automorphism
group by conjugating with the down/up equivalences. This identification allows cocycles
indexed by algebra automorphisms to be transported to larger universes.
-/

public section

universe u v w t t₁ t₂

attribute [local instance] ULift.algebra'

namespace ULift

variable {R : Type u} [CommSemiring R] {A : Type v} [Semiring A] [Algebra R A]

/-- Lifting the scalar ring and the algebra commutes with their algebra maps. -/
theorem algebraMap_comp_ringEquiv_symm :
    (algebraMap (ULift.{t} R) (ULift.{t₁} A)).comp
        ((ULift.ringEquiv.symm : R ≃+* ULift.{t} R) : R →+* ULift.{t} R) =
      ((ULift.ringEquiv.symm : A ≃+* ULift.{t₁} A) : A →+* ULift.{t₁} A).comp
        (algebraMap R A) :=
  RingHom.ext fun _ ↦ rfl

end ULift

namespace AlgEquiv

variable {R : Type u} [CommSemiring R] {A : Type v} [Semiring A] [Algebra R A]
  {B : Type w} [Semiring B] [Algebra R B]

/-- Lift an algebra equivalence together with its scalar ring. -/
def ulift (e : A ≃ₐ[R] B) : ULift.{t₁} A ≃ₐ[ULift.{t} R] ULift.{t₂} B :=
  AlgEquiv.ofAlgHom e.toAlgHom.ulift e.symm.toAlgHom.ulift
    (by ext x; exact e.apply_symm_apply x.down)
    (by ext x; exact e.symm_apply_apply x.down)

@[simp]
theorem ulift_apply (e : A ≃ₐ[R] B) (x : ULift.{t₁} A) :
    (e.ulift : ULift.{t₁} A ≃ₐ[ULift.{t} R] ULift.{t₂} B) x =
      ULift.up (e x.down) := (rfl)

@[simp]
theorem ulift_symm_apply (e : A ≃ₐ[R] B) (x : ULift.{t₂} B) :
    (e.ulift : ULift.{t₁} A ≃ₐ[ULift.{t} R] ULift.{t₂} B).symm x =
      ULift.up (e.symm x.down) := (rfl)

/-- Lifting both scalars and the algebra preserves its full automorphism group. -/
def uliftAutEquiv : (A ≃ₐ[R] A) ≃* (ULift.{t} A ≃ₐ[ULift.{t} R] ULift.{t} A) where
  toFun := ulift
  invFun e :=
    { toRingEquiv := ULift.ringEquiv.symm.trans (e.toRingEquiv.trans ULift.ringEquiv)
      commutes' r := congrArg ULift.down (e.commutes (ULift.up r)) }
  left_inv e := by ext x; rfl
  right_inv e := by ext x; rfl
  map_mul' e f := by ext x; rfl

@[simp]
theorem uliftAutEquiv_apply (e : A ≃ₐ[R] A) (x : ULift.{t} A) :
    uliftAutEquiv e x = ULift.up (e x.down) := (rfl)

@[simp]
theorem uliftAutEquiv_symm_apply
    (e : ULift.{t} A ≃ₐ[ULift.{t} R] ULift.{t} A) (x : A) :
    uliftAutEquiv.symm e x = (e (ULift.up x)).down := (rfl)

/-- The inverse automorphism transport intertwines the up map with evaluation. -/
theorem uliftAutEquiv_symm_apply_up
    (e : ULift.{t} A ≃ₐ[ULift.{t} R] ULift.{t} A) (x : A) :
    ULift.ringEquiv.symm (uliftAutEquiv.symm e x) = e (ULift.ringEquiv.symm x) := by
  apply ULift.down_injective
  exact uliftAutEquiv_symm_apply e x

end AlgEquiv
