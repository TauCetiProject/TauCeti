/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Compatible algebra maps out of a relative tensor product

For algebras `A` and `B` over `C`, itself an algebra over `k`, maps from `A ⊗[C] B`
to a commutative `k`-algebra are pairs of `k`-algebra maps agreeing on `C`. The target
need not have a prescribed `C`-algebra structure. `AlgHom.tensorProductLift`
is the algebra-map version of `Algebra.TensorProduct.liftRingHom`.

This universal property identifies points of an affine fibre product with compatible pairs
of points, without fixing their common image in the base.
-/

public section

open TensorProduct

open Algebra.TensorProduct

namespace AlgHom

variable {k C A B R : Type*} [CommSemiring k] [CommSemiring C] [Algebra k C]
  [Semiring A] [Algebra C A] [Algebra k A] [IsScalarTower k C A]
  [Semiring B] [Algebra C B] [Algebra k B] [IsScalarTower k C B]

section Lift

variable [CommSemiring R] [Algebra k R]

/-- Extend two `k`-algebra maps agreeing on `C` to `A ⊗[C] B`. No `C`-algebra structure
on the target is prescribed. -/
noncomputable def tensorProductLift (x : A →ₐ[k] R) (y : B →ₐ[k] R)
    (h : x.comp (IsScalarTower.toAlgHom k C A) =
      y.comp (IsScalarTower.toAlgHom k C B)) : A ⊗[C] B →ₐ[k] R :=
  { liftRingHom x.toRingHom y.toRingHom (congrArg AlgHom.toRingHom h) with
    commutes' := fun r ↦ by
      simp [algebraMap_def, liftRingHom_tmul] }

/-- The compatible lift multiplies the values on pure tensors. -/
@[simp]
theorem tensorProductLift_tmul (x : A →ₐ[k] R) (y : B →ₐ[k] R)
    (h : x.comp (IsScalarTower.toAlgHom k C A) =
      y.comp (IsScalarTower.toAlgHom k C B)) (a : A) (b : B) :
    tensorProductLift x y h (a ⊗ₜ[C] b) = x a * y b :=
  liftRingHom_tmul _ _ _ _ _

/-- Restricting a compatible lift to the left factor recovers the first map. -/
@[simp]
theorem tensorProductLift_comp_includeLeft (x : A →ₐ[k] R) (y : B →ₐ[k] R)
    (h : x.comp (IsScalarTower.toAlgHom k C A) =
      y.comp (IsScalarTower.toAlgHom k C B)) :
    (tensorProductLift x y h).comp includeLeft = x := by
  ext a
  simp

/-- Restricting a compatible lift to the right factor recovers the second map. -/
@[simp]
theorem tensorProductLift_comp_includeRight (x : A →ₐ[k] R) (y : B →ₐ[k] R)
    (h : x.comp (IsScalarTower.toAlgHom k C A) =
      y.comp (IsScalarTower.toAlgHom k C B)) :
    (tensorProductLift x y h).comp (includeRight.restrictScalars k) = y := by
  ext b
  simp

end Lift

section Restriction

variable [Semiring R] [Algebra k R]

/-- The restrictions of a point of a relative tensor product agree on the middle algebra. -/
theorem comp_includeLeft_eq_comp_includeRight (x : A ⊗[C] B →ₐ[k] R) :
    (x.comp Algebra.TensorProduct.includeLeft).comp (IsScalarTower.toAlgHom k C A) =
      (x.comp (Algebra.TensorProduct.includeRight.restrictScalars k)).comp
        (IsScalarTower.toAlgHom k C B) := by
  ext c
  exact congrArg x (DFunLike.congr_fun
    (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap (R := C) (A := A) (B := B)) c)

end Restriction

variable [CommSemiring R] [Algebra k R]

/-- Restriction from a relative tensor product has image exactly the pairs of algebra maps
agreeing on the middle algebra. -/
theorem range_tensorProduct_restrict :
    Set.range (fun x : A ⊗[C] B →ₐ[k] R ↦
      (x.comp Algebra.TensorProduct.includeLeft,
        x.comp (Algebra.TensorProduct.includeRight.restrictScalars k))) =
      {p | p.1.comp (IsScalarTower.toAlgHom k C A) =
        p.2.comp (IsScalarTower.toAlgHom k C B)} := by
  ext p
  constructor
  · rintro ⟨x, rfl⟩
    exact x.comp_includeLeft_eq_comp_includeRight
  · intro hp
    exact ⟨p.1.tensorProductLift p.2 hp, by ext <;> simp⟩

end AlgHom
