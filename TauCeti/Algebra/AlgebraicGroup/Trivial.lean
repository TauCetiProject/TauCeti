/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# The trivial affine group

This file records the functor-of-points calculation for the trivial affine group scheme. Its
coordinate Hopf algebra is the base ring `R`, with Mathlib's canonical Hopf algebra structure
on `R` over itself. For every commutative `R`-algebra `A`, there is exactly one `R`-algebra
homomorphism `R →ₐ[R] A`, namely `Algebra.ofId R A`; consequently the convolution group of
`A`-points is the one-element group `PUnit`.

This is the terminal-object example in the Hopf-algebra/functor-of-points side of the
ReductiveGroups roadmap, Layer 0. It is the identity object needed by the product and affine
group scheme dictionary: `Spec R` over `Spec R` represents the trivial group-valued functor.

## Main declarations

* `TauCeti.TrivialGroup.point`: the unique `A`-point, `Algebra.ofId R A`.
* `TauCeti.TrivialGroup.pointsMulEquiv`: the convolution group of points is `PUnit`.
* `TauCeti.TrivialGroup.pointsMulEquiv_mapValue`: the equivalence is natural in the value
  algebra.

## References

This uses Mathlib's `Algebra.ofId`, its `Subsingleton (R →ₐ[R] A)` instance, and the
canonical Hopf algebra structure on `R` over itself from `Mathlib.RingTheory.HopfAlgebra.Basic`.
-/

public section

open WithConv

namespace TauCeti

namespace TrivialGroup

universe u v w

variable {R : Type u} {A : Type v}
variable [CommSemiring R] [CommSemiring A] [Algebra R A]

/-- The unique `A`-point of the trivial affine group represented by the Hopf algebra `R`. -/
abbrev point : R →ₐ[R] A :=
  Algebra.ofId R A

/-- The unique point evaluates by the algebra map. -/
@[simp]
theorem point_apply (r : R) : point (R := R) (A := A) r = algebraMap R A r :=
  rfl

/-- Every `A`-point of the trivial affine group is the canonical algebra map. -/
theorem point_eq (f : R →ₐ[R] A) : f = point (R := R) (A := A) :=
  Subsingleton.elim f (point (R := R) (A := A))

/-- Pointwise form of `point_eq`: every point evaluates as the algebra map. -/
theorem apply_eq_algebraMap (f : R →ₐ[R] A) (r : R) : f r = algebraMap R A r := by
  rw [point_eq f, point_apply]

/-- Algebra maps out of the coordinate Hopf algebra `R` are equivalent to the one-point type. -/
@[expose] noncomputable def pointEquiv : (R →ₐ[R] A) ≃ PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := point (R := R) (A := A)
  left_inv := fun f => (point_eq f).symm
  right_inv _ := rfl

@[simp]
theorem pointEquiv_apply (f : R →ₐ[R] A) :
    pointEquiv (R := R) (A := A) f = PUnit.unit :=
  rfl

@[simp]
theorem pointEquiv_symm_apply (u : PUnit.{1}) :
    (pointEquiv (R := R) (A := A)).symm u = point (R := R) (A := A) :=
  rfl

/-- The functor of points of the trivial affine group is the one-element group.

The source is the convolution group of `R`-algebra maps out of the Hopf algebra `R`; since
there is only one such algebra map, the convolution group is multiplicatively equivalent to
`PUnit`. -/
@[expose] noncomputable def pointsMulEquiv : WithConv (R →ₐ[R] A) ≃* PUnit.{1} where
  toFun _ := PUnit.unit
  invFun _ := toConv (point (R := R) (A := A))
  left_inv f := by
    apply WithConv.ofConv_injective
    exact Subsingleton.elim _ _
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp]
theorem pointsMulEquiv_apply (f : WithConv (R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := A) f = PUnit.unit :=
  rfl

@[simp]
theorem pointsMulEquiv_symm_apply (u : PUnit.{1}) :
    (pointsMulEquiv (R := R) (A := A)).symm u = toConv (point (R := R) (A := A)) :=
  rfl

/-- The unique convolution point is the identity point. -/
theorem convPoint_eq_one (f : WithConv (R →ₐ[R] A)) : f = 1 := by
  apply WithConv.ofConv_injective
  rw [AlgHom.convOne_def]
  exact Subsingleton.elim _ _

/-- Evaluating the inverse of a trivial-group point gives the algebra map. -/
@[simp]
theorem convInv_apply (f : WithConv (R →ₐ[R] A)) (r : R) :
    f⁻¹ r = algebraMap R A r := by
  rw [convPoint_eq_one f]
  rw [AlgHom.convOne_def]
  rfl

section Naturality

variable {B : Type w} [CommSemiring B] [Algebra R B]

/-- The unique point is natural in the value algebra. -/
@[simp]
theorem comp_point (φ : A →ₐ[R] B) :
    φ.comp (point (R := R) (A := A)) = point (R := R) (A := B) :=
  point_eq _

/-- The plain points equivalence is natural in the value algebra. -/
@[simp]
theorem pointEquiv_comp (φ : A →ₐ[R] B) (f : R →ₐ[R] A) :
    pointEquiv (R := R) (A := B) (φ.comp f) =
      pointEquiv (R := R) (A := A) f :=
  rfl

/-- The trivial-group points equivalence is natural in the value algebra. -/
@[simp]
theorem pointsMulEquiv_mapValue (φ : A →ₐ[R] B) (f : WithConv (R →ₐ[R] A)) :
    pointsMulEquiv (R := R) (A := B)
        (AlgHom.mapValue (H := R) φ f) =
      pointsMulEquiv (R := R) (A := A) f :=
  rfl

/-- Naturality of the inverse trivial-group points equivalence in the value algebra. -/
@[simp]
theorem mapValue_pointsMulEquiv_symm_apply (φ : A →ₐ[R] B) (u : PUnit.{1}) :
    AlgHom.mapValue (H := R) φ ((pointsMulEquiv (R := R) (A := A)).symm u) =
      (pointsMulEquiv (R := R) (A := B)).symm u := by
  apply (pointsMulEquiv (R := R) (A := B)).injective
  rw [pointsMulEquiv_mapValue]

end Naturality

end TrivialGroup

end TauCeti
