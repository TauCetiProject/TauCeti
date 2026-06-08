/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Grp.Basic

/-!
# The functor of points of a Hopf algebra

This file packages the convolution group from
`TauCeti.Algebra.AlgebraicGroup.FunctorOfPoints` as the functor of points of a Hopf algebra.
For a Hopf algebra `H` over a commutative ring `R`, its `A`-points are the `R`-algebra maps
`H →ₐ[R] A`, with multiplication given by convolution. Post-composition in the value algebra
then gives a functor

```
CommAlgCat R ⥤ GrpCat
```

This is the categorical form of the "R-points as a group" item in Layer 0 of the Tau Ceti
reductive-groups roadmap. The convolution monoid and inverse are provided by the preceding
Tau Ceti file, which in turn builds on Mathlib's convolution API.
-/

open CategoryTheory

namespace TauCeti

namespace HopfAlgebra

universe u v w

/-- The functor of points of a Hopf algebra, valued in groups via convolution.

It sends a commutative `R`-algebra `A` to the convolution group of algebra maps
`H →ₐ[R] A`, and sends `φ : A ⟶ B` to post-composition with `φ`. -/
noncomputable def pointsFunctor (R : Type u) (H : Type v) [CommRing R] [Semiring H]
    [_root_.HopfAlgebra R H] : CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj A := GrpCat.of (TauCeti.Bialgebra.AlgPoints R H A)
  map {A B} φ := GrpCat.ofHom (AlgHom.mapValue (H := H) φ.hom)
  map_id A := by
    rw [CommAlgCat.hom_id, AlgHom.mapValue_id, GrpCat.ofHom_id]
  map_comp φ ψ := by
    rw [CommAlgCat.hom_comp, AlgHom.mapValue_comp, GrpCat.ofHom_comp]

namespace pointsFunctor

variable {R : Type u} {H : Type v} [CommRing R] [Semiring H] [_root_.HopfAlgebra R H]
variable {A B : CommAlgCat.{w} R}

/-- The morphism induced by a bundled commutative algebra map is `AlgHom.mapValue`. -/
@[simp]
lemma map_hom (φ : A ⟶ B) :
    (pointsFunctor R H).map φ = GrpCat.ofHom (AlgHom.mapValue (H := H) φ.hom) :=
  rfl

/-- Pointwise, the points functor acts by post-composition with a bundled morphism. -/
@[simp]
lemma map_apply (φ : A ⟶ B) (f : TauCeti.Bialgebra.AlgPoints R H A) :
    (pointsFunctor R H).map φ f =
      TauCeti.Bialgebra.AlgPoints.ofHom (φ.hom.comp f.hom) :=
  rfl

/-- Pointwise on `H`, the points functor applies the bundled value-algebra morphism. -/
@[simp]
lemma map_apply_apply (φ : A ⟶ B) (f : TauCeti.Bialgebra.AlgPoints R H A) (h : H) :
    ((pointsFunctor R H).map φ f : TauCeti.Bialgebra.AlgPoints R H B).hom h =
      φ.hom (f.hom h) :=
  rfl

variable {A B : Type w} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Evaluating the points functor at `A` gives the convolution group of `A`-points. -/
@[simp]
lemma obj_of :
    (pointsFunctor R H).obj (CommAlgCat.of R A) =
      GrpCat.of (TauCeti.Bialgebra.AlgPoints R H A) :=
  rfl

/-- The morphism induced by an algebra map on the points functor is `AlgHom.mapValue`. -/
@[simp]
lemma map_ofHom_hom (φ : A →ₐ[R] B) :
    (pointsFunctor R H).map (CommAlgCat.ofHom φ) =
      GrpCat.ofHom (AlgHom.mapValue (H := H) φ) :=
  rfl

/-- Pointwise, the points functor acts by post-composition. -/
@[simp]
lemma map_ofHom_apply (φ : A →ₐ[R] B) (f : TauCeti.Bialgebra.AlgPoints R H A) :
    (pointsFunctor R H).map (CommAlgCat.ofHom φ) f =
      TauCeti.Bialgebra.AlgPoints.ofHom (φ.comp f.hom) :=
  rfl

/-- Pointwise on `H`, the points functor acts by applying the value-algebra morphism. -/
@[simp]
lemma map_ofHom_apply_apply (φ : A →ₐ[R] B)
    (f : TauCeti.Bialgebra.AlgPoints R H A) (h : H) :
    ((pointsFunctor R H).map (CommAlgCat.ofHom φ) f :
        TauCeti.Bialgebra.AlgPoints R H B).hom h =
      φ (f.hom h) :=
  rfl

end pointsFunctor

end HopfAlgebra

end TauCeti
