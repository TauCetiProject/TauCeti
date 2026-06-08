/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# The functor of points of a Hopf algebra

The reductive-groups roadmap asks for the functor of points of an affine group scheme in
Layer 0.  The file `TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints` proves the algebraic
ingredient: for a Hopf algebra `H` over `R` and a commutative `R`-algebra `A`, the
convolution monoid on `H →ₐ[R] A` is a group, and post-composition in `A` is compatible
with convolution.

This file packages that data as the bundled functor
`HopfAlgebra.pointsFunctor H : CommAlgCat R ⥤ GrpCat`.  On objects it sends `A` to the
convolution group `WithConv (H →ₐ[R] A)`, and on morphisms it sends
`φ : A ⟶ B` to post-composition with `φ`.

This is not yet the full scheme-side representability statement.  It is the concrete
`R`-algebra valued group functor that the affine group scheme `Spec H` represents when `H`
is commutative.
-/

open CategoryTheory Coalgebra HopfAlgebra WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w

variable {R : Type u} {H : Type v} [CommRing R] [Semiring H] [_root_.HopfAlgebra R H]

/-- The convolution group of `A`-valued points of a Hopf algebra `H` over `R`.

An element of `points H A` is an `R`-algebra homomorphism `H →ₐ[R] A`; multiplication is
convolution, the identity is the counit, and inverse is post-composition with the antipode.
-/
abbrev points (H : Type v) [Semiring H] [_root_.HopfAlgebra R H] (A : CommAlgCat.{w} R) :
    Type (max v w) :=
  WithConv (H →ₐ[R] A)

/-- The group-valued functor of points of a Hopf algebra.

For a commutative `R`-algebra `A`, its value is the convolution group of algebra
homomorphisms `H →ₐ[R] A`.  A morphism `A ⟶ B` acts by post-composition. -/
noncomputable def pointsFunctor (H : Type v) [Semiring H] [_root_.HopfAlgebra R H] :
    CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (points (R := R) H A)
  map {A B} φ := GrpCat.ofHom (TauCeti.AlgHom.mapValue (H := H) φ.hom)
  map_id A := by
    refine GrpCat.ext fun f => ?_
    exact congrFun (congrArg DFunLike.coe (TauCeti.AlgHom.mapValue_id (H := H) (A := A))) f
  map_comp {A B C} φ ψ := by
    refine GrpCat.ext fun f => ?_
    exact congrFun
      (congrArg DFunLike.coe (TauCeti.AlgHom.mapValue_comp (H := H) ψ.hom φ.hom)) f

/-- The functor of points sends `A` to the convolution group of algebra maps `H →ₐ[R] A`. -/
@[simp]
lemma pointsFunctor_obj (A : CommAlgCat.{w} R) :
    (pointsFunctor (R := R) H).obj A = GrpCat.of (points (R := R) H A) :=
  rfl

/-- The functor of points sends a map of value algebras to post-composition. -/
@[simp]
lemma pointsFunctor_map {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (pointsFunctor (R := R) H).map φ =
      GrpCat.ofHom (TauCeti.AlgHom.mapValue (H := H) φ.hom) :=
  rfl

/-- Pointwise, the functor of points acts on morphisms by post-composition. -/
@[simp]
lemma pointsFunctor_map_apply {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : (pointsFunctor (R := R) H).obj A) :
    ((pointsFunctor (R := R) H).map φ f : WithConv (H →ₐ[R] B)) =
      toConv (φ.hom.comp f.ofConv) :=
  rfl

/-- Evaluation after applying the functor of points is ordinary post-composition. -/
@[simp]
lemma pointsFunctor_map_apply_apply {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : (pointsFunctor (R := R) H).obj A) (h : H) :
    ((pointsFunctor (R := R) H).map φ f : WithConv (H →ₐ[R] B)).ofConv h =
      φ.hom (f.ofConv h) :=
  rfl

/-- The points functor sends identity morphisms to identity maps. -/
@[simp]
lemma pointsFunctor_map_id (A : CommAlgCat.{w} R) :
    (pointsFunctor (R := R) H).map (𝟙 A) =
      𝟙 ((pointsFunctor (R := R) H).obj A) :=
  (pointsFunctor (R := R) H).map_id A

/-- The points functor sends composition of value-algebra maps to composition of group maps. -/
@[simp]
lemma pointsFunctor_map_comp {A B C : CommAlgCat.{w} R} (φ : A ⟶ B) (ψ : B ⟶ C) :
    (pointsFunctor (R := R) H).map (φ ≫ ψ) =
      (pointsFunctor (R := R) H).map φ ≫ (pointsFunctor (R := R) H).map ψ :=
  (pointsFunctor (R := R) H).map_comp φ ψ

/-- Multiplication in `points H A` is the convolution product. -/
lemma points_mul_apply (A : CommAlgCat.{w} R) (f g : points (R := R) H A) (h : H) :
    (f * g) h =
      Algebra.TensorProduct.lift f.ofConv g.ofConv (fun _ _ => .all ..) (Coalgebra.comul h) :=
  AlgHom.convMul_apply f g h

/-- The map on points preserves convolution products. -/
@[simp]
lemma pointsFunctor_map_mul {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f g : (pointsFunctor (R := R) H).obj A) :
    (pointsFunctor (R := R) H).map φ (f * g) =
      (pointsFunctor (R := R) H).map φ f * (pointsFunctor (R := R) H).map φ g :=
  map_mul (TauCeti.AlgHom.mapValue (H := H) φ.hom) f g

/-- The map on points preserves the identity point. -/
@[simp]
lemma pointsFunctor_map_one {A B : CommAlgCat.{w} R} (φ : A ⟶ B) :
    (pointsFunctor (R := R) H).map φ (1 : (pointsFunctor (R := R) H).obj A) = 1 :=
  map_one (TauCeti.AlgHom.mapValue (H := H) φ.hom)

/-- The map on points preserves inverses. -/
@[simp]
lemma pointsFunctor_map_inv {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f : (pointsFunctor (R := R) H).obj A) :
    (pointsFunctor (R := R) H).map φ f⁻¹ =
      ((pointsFunctor (R := R) H).map φ f)⁻¹ :=
  map_inv (TauCeti.AlgHom.mapValue (H := H) φ.hom) f

/-- The map on points preserves quotients in the convolution group. -/
@[simp]
lemma pointsFunctor_map_div {A B : CommAlgCat.{w} R} (φ : A ⟶ B)
    (f g : (pointsFunctor (R := R) H).obj A) :
    (pointsFunctor (R := R) H).map φ (f / g) =
      (pointsFunctor (R := R) H).map φ f / (pointsFunctor (R := R) H).map φ g :=
  map_div (TauCeti.AlgHom.mapValue (H := H) φ.hom) f g

end HopfAlgebra

end TauCeti
