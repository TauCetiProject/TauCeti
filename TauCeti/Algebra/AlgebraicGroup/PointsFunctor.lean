/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# The functor of points of a Hopf algebra

For a Hopf algebra `H` over a commutative ring `R`, the `A`-points of the affine group
scheme represented by `H` are the `R`-algebra homomorphisms `H →ₐ[R] A`, equipped with the
convolution group structure. This file packages that construction as a functor

`CommAlgCat R ⥤ GrpCat`.

The group structure and its functoriality in the value algebra are proved in
`TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints`; here we add only the categorical wrapper
needed to use those groups as the functor-of-points view in the reductive-groups roadmap.

## Main definitions

* `HopfAlgebra.pointsFunctor`: the functor sending a commutative `R`-algebra `A` to the
  convolution group on `H →ₐ[R] A`.

## References

This advances the Tau Ceti reductive-groups roadmap, Layer 0, "R-points as a group":
the points of a Hopf algebra are functorial in commutative value algebras and form a group
by convolution.
-/

open CategoryTheory WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable (R : Type u) [CommRing R] (H : Type v) [Semiring H] [_root_.HopfAlgebra R H]

/-- The functor of points of the affine group represented by a Hopf algebra `H`.

It sends a commutative `R`-algebra `A` to the convolution group on algebra homomorphisms
`H →ₐ[R] A`, and sends an algebra map `A ⟶ B` to post-composition with that map. -/
noncomputable def pointsFunctor : CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (WithConv (H →ₐ[R] A))
  map {A B} φ := GrpCat.ofHom (AlgHom.mapValue (H := H) φ.hom)
  map_id A := by
    apply GrpCat.hom_ext
    simp
  map_comp {A B C} φ ψ := by
    apply GrpCat.hom_ext
    simp [AlgHom.mapValue_comp]

namespace PointsFunctor

variable {R H}

/-- The value of `pointsFunctor R H` at a commutative `R`-algebra `A` is the convolution
group on `R`-algebra homomorphisms `H →ₐ[R] A`. -/
@[simp]
lemma obj_carrier (A : CommAlgCat.{w} R) :
    ((pointsFunctor R H).obj A : Type (max v w)) = WithConv (H →ₐ[R] A) :=
  rfl

/-- On an algebra map `φ : A ⟶ B`, the functor of points acts by post-composition. -/
@[simp]
lemma map_apply {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : WithConv (H →ₐ[R] A)) (h : H) :
    (((pointsFunctor R H).map φ f : WithConv (H →ₐ[R] B)).ofConv h) =
      φ.hom (f.ofConv h) := by
  rfl

/-- On the identity algebra map, the functor of points is the identity group homomorphism. -/
@[simp]
lemma map_id_apply (A : CommAlgCat.{w} R) (f : WithConv (H →ₐ[R] A)) :
    (pointsFunctor R H).map (𝟙 A) f = f := by
  simp
  rfl

/-- The functor of points respects composition of algebra maps. -/
@[simp]
lemma map_comp_apply {A B C : CommAlgCat.{w} R} (φ : A ⟶ B) (ψ : B ⟶ C)
    (f : WithConv (H →ₐ[R] A)) :
    (pointsFunctor R H).map (φ ≫ ψ) f =
      (pointsFunctor R H).map ψ ((pointsFunctor R H).map φ f) := by
  simp
  rfl

end PointsFunctor

end HopfAlgebra

end TauCeti
