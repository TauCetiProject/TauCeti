/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
import TauCeti.Algebra.HopfAlgebra.SymmetricAlgebra

/-!
# The additive group

The affine scheme `Spec (SymmetricAlgebra R M)` is the **additive (vector) group** on `M`.
Its functor of points is computed here: for a commutative `R`-algebra `A`, the
convolution monoid of `R`-algebra maps `SymmetricAlgebra R M →ₐ[R] A` is the additive monoid
of `R`-linear maps `M →ₗ[R] A`, with convolution corresponding to addition. Taking `M = R`
recovers the one-dimensional additive group `𝔾ₐ = Spec R[X]`, whose `A`-valued points are
`(A, +)`; the `R`-points are this construction specialized to `A = R`.

This is the worked example `𝔾ₐ` from the Tau Ceti reductive-groups roadmap
(`TauCetiRoadmap/ReductiveGroups/README.md`, "Worked examples" and Layer 0, "R-points as a
group"), in the same spirit as the multiplicative group `𝔾ₘ`.

## Main declarations

* `TauCeti.AdditiveGroup.pointsMulEquiv`: the convolution monoid of points
  `SymmetricAlgebra R M →ₐ[R] A` is the additive monoid `M →ₗ[R] A`.
* `TauCeti.AdditiveGroup.gaPointsMulEquiv`: the monoid of `A`-valued points of `𝔾ₐ` over `R`
  is the additive monoid of `A`.

## References

The symmetric-algebra Hopf structure is supplied by
`TauCeti.Algebra.HopfAlgebra.SymmetricAlgebra`, on top of Mathlib's symmetric-algebra
bialgebra and convolution monoid APIs.
-/

open Coalgebra HopfAlgebra SymmetricAlgebra WithConv
open scoped TensorProduct

namespace TauCeti

namespace AdditiveGroup

universe u v w

section Points

variable {R : Type u} [CommSemiring R] {M : Type v} [AddCommMonoid M] [Module R M]
variable {A : Type w} [CommSemiring A] [Algebra R A]

/-- **The convolution monoid of points of a vector group.** For a commutative `R`-algebra `A`,
the convolution monoid of `R`-algebra maps out of `SymmetricAlgebra R M` is the additive monoid
of `R`-linear maps `M →ₗ[R] A`: a point `F` corresponds to the linear map `x ↦ F (ι x)`, and
convolution of points corresponds to addition of linear maps. -/
noncomputable def pointsMulEquiv :
    WithConv (SymmetricAlgebra R M →ₐ[R] A) ≃* Multiplicative (M →ₗ[R] A) where
  toFun F := Multiplicative.ofAdd (SymmetricAlgebra.lift.symm F.ofConv)
  invFun φ := toConv (SymmetricAlgebra.lift (Multiplicative.toAdd φ))
  left_inv F := by
    simp only [toAdd_ofAdd, Equiv.apply_symm_apply, toConv_ofConv]
  right_inv φ := by
    simp only [Equiv.symm_apply_apply, ofAdd_toAdd]
  map_mul' F G := by
    have h : SymmetricAlgebra.lift.symm (F * G).ofConv =
        SymmetricAlgebra.lift.symm F.ofConv + SymmetricAlgebra.lift.symm G.ofConv := by
      ext x
      simp [LinearMap.add_apply]
    exact (congrArg Multiplicative.ofAdd h).trans (ofAdd_add _ _)

/-- A point of the additive group, as a linear map, is `x ↦ F (ι x)`. -/
@[simp]
theorem toAdd_pointsMulEquiv (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    Multiplicative.toAdd (pointsMulEquiv F) = SymmetricAlgebra.lift.symm F.ofConv :=
  rfl

/-- The linear map underlying a point evaluates as `x ↦ F (ι x)`. -/
@[simp]
theorem toAdd_pointsMulEquiv_apply (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) (x : M) :
    Multiplicative.toAdd (pointsMulEquiv F) x = F.ofConv (ι R M x) :=
  TauCeti.SymmetricAlgebra.lift_symm_apply F.ofConv x

/-- The inverse equivalence sends a linear map to the corresponding algebra map. -/
@[simp]
theorem pointsMulEquiv_symm_apply (φ : Multiplicative (M →ₗ[R] A)) :
    (pointsMulEquiv (R := R) (M := M) (A := A)).symm φ =
      toConv (SymmetricAlgebra.lift (Multiplicative.toAdd φ)) :=
  rfl

end Points

section RingPoints

variable {R : Type u} [CommRing R] {M : Type v} [AddCommMonoid M] [Module R M]
variable {A : Type w} [CommRing A] [Algebra R A]

/-- Over commutative rings, `pointsMulEquiv` identifies the convolution inverse of a point with
negation of the corresponding linear map. -/
@[simp]
theorem pointsMulEquiv_inv (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    pointsMulEquiv (F⁻¹) = (pointsMulEquiv F)⁻¹ :=
  map_inv pointsMulEquiv F

/-- In additive notation, the convolution inverse of a point corresponds to negating its linear
map of generator values. -/
@[simp]
theorem toAdd_pointsMulEquiv_inv (F : WithConv (SymmetricAlgebra R M →ₐ[R] A)) :
    Multiplicative.toAdd (pointsMulEquiv (F⁻¹)) = -Multiplicative.toAdd (pointsMulEquiv F) := by
  rw [pointsMulEquiv_inv]
  rfl

end RingPoints

section Ga

variable {R : Type u} [CommSemiring R] {A : Type w} [CommSemiring A] [Algebra R A]

/-- **The one-dimensional additive monoid of points** for `𝔾ₐ = Spec (SymmetricAlgebra R R)`.
Specializing the vector group to `M = R`, the convolution monoid of `A`-valued points over `R`
is the additive monoid `(A, +)`. -/
noncomputable def gaPointsMulEquiv :
    WithConv (SymmetricAlgebra R R →ₐ[R] A) ≃* Multiplicative A :=
  pointsMulEquiv.trans
    (AddEquiv.toMultiplicative (LinearMap.ringLmapEquivSelf R R A).toAddEquiv)

/-- A point of `𝔾ₐ` is the additive group element obtained by evaluating it at the generator
`ι 1`. -/
@[simp]
theorem toAdd_gaPointsMulEquiv (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    Multiplicative.toAdd (gaPointsMulEquiv F) = F.ofConv (ι R R 1) := by
  rw [gaPointsMulEquiv]
  simp

/-- The inverse equivalence sends an element of the value algebra to the corresponding
`A`-valued point of `𝔾ₐ`. -/
@[simp]
theorem gaPointsMulEquiv_symm_apply_ι (a : Multiplicative A) :
    ((gaPointsMulEquiv (R := R) (A := A)).symm a).ofConv (ι R R 1) =
      Multiplicative.toAdd a := by
  rw [gaPointsMulEquiv]
  simp

end Ga

section GaRing

variable {R : Type u} [CommRing R] {A : Type w} [CommRing A] [Algebra R A]

/-- Over commutative rings, `gaPointsMulEquiv` identifies the convolution inverse of a
`𝔾ₐ`-point with negation in the value ring. -/
@[simp]
theorem gaPointsMulEquiv_inv (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    gaPointsMulEquiv (F⁻¹) = (gaPointsMulEquiv F)⁻¹ :=
  map_inv gaPointsMulEquiv F

/-- In additive notation, the convolution inverse of a `𝔾ₐ`-point is the negative of its value
on the generator `ι 1`. -/
@[simp]
theorem toAdd_gaPointsMulEquiv_inv (F : WithConv (SymmetricAlgebra R R →ₐ[R] A)) :
    Multiplicative.toAdd (gaPointsMulEquiv (F⁻¹)) = -Multiplicative.toAdd (gaPointsMulEquiv F) := by
  rw [gaPointsMulEquiv_inv]
  rfl

end GaRing

end AdditiveGroup

end TauCeti
