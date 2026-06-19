/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.CommHopfAlgCat
import Mathlib.Algebra.Category.HopfAlgCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import TauCeti.Algebra.AlgebraicGroup.HopfMap
import TauCeti.Algebra.AlgebraicGroup.PointsFunctor

/-!
# Commutative Hopf algebras and their functor of points

This file packages the contravariant functor that sends a commutative coordinate Hopf algebra
`H` over a commutative ring `R` to its group-valued functor of points `A ↦ Hom_R(H, A)`.

The category of commutative Hopf algebras is Mathlib's bundled `CommHopfAlgCat`; this file
adds the functor-of-points stack on top of it.

This is the categorical form of the first concrete target in the Tau Ceti reductive-groups
roadmap, Layer 0, "R-points as a group": for a commutative Hopf algebra representing an
affine group scheme, the functor of points is group-valued by convolution, and a morphism of
coordinate Hopf algebras acts on points by pre-composition.

## Main declarations

* `CommHopfAlgCat.mapPointsFunctor`: a coordinate morphism `H ⟶ K` induces a natural
  transformation from the points functor of `K` to the points functor of `H`.
* `CommHopfAlgCat.pointsFunctor`: the contravariant functor
  `(CommHopfAlgCat R)ᵒᵖ ⥤ CommAlgCat R ⥤ GrpCat`.

## References

The bundled category `CommHopfAlgCat`, its forgetful functor to `CommBialgCat`, and the
equivalence `CommHopfAlgCat.commHopfAlgCatEquivCogrpCommAlgCat` with cogroup objects in
commutative algebras are Mathlib's `Mathlib.Algebra.Category.CommHopfAlgCat`. The points
functoriality uses Mathlib's convolution monoid and bialgebra morphism API, in particular
`AlgHom.convMul_comp_bialgHom_distrib` from
`Mathlib.RingTheory.Bialgebra.Convolution`, through the Tau Ceti wrapper
`AlgHom.mapDomain`.
-/

open CategoryTheory WithConv

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- Turn a morphism in `CommHopfAlgCat` back into a bialgebra morphism.

This is a thin wrapper around Mathlib's `CommHopfAlgCat.Hom.hom` kept so the points-functor
API below (and its downstream consumers) can refer to the underlying bialgebra morphism under
a stable name. -/
abbrev toBialgHom {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K) : H →ₐc[R] K :=
  φ.hom

/-- A morphism of coordinate commutative Hopf algebras induces a natural transformation
between their group-valued points functors, contravariantly in the coordinate algebra.

At a commutative `R`-algebra `A`, this sends an `A`-valued point `f : K →ₐ[R] A` to
`f ∘ φ : H →ₐ[R] A`. -/
noncomputable def mapPointsFunctor {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K) :
    HopfAlgebra.pointsFunctor (R := R) (H := K) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := H) where
  app A := GrpCat.ofHom
    (AlgHom.mapDomain (H₁ := H) (H₂ := K) (A := A) (toBialgHom φ))
  naturality {A B} ψ := by
    simp only [HopfAlgebra.pointsFunctor_map, HopfAlgebra.mapPoints]
    exact GrpCat.hom_ext (AlgHom.mapValue_mapDomain (toBialgHom φ) ψ.hom)

/-- On points, `mapPointsFunctor φ` is pre-composition with `φ`. -/
@[simp]
lemma mapPointsFunctor_app_apply {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K)
    (A : CommAlgCat.{w} R) (f : HopfAlgebra.points (R := R) (H := K) A) :
    (mapPointsFunctor φ).app A f =
      toConv (f.ofConv.comp (toBialgHom φ : H →ₐ[R] K)) := by
  exact AlgHom.mapDomain_apply (A := A) (toBialgHom φ) f

/-- Pointwise form of `mapPointsFunctor_app_apply`. -/
@[simp]
lemma mapPointsFunctor_app_apply_apply {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K)
    (A : CommAlgCat.{w} R) (f : HopfAlgebra.points (R := R) (H := K) A) (h : H) :
    (((mapPointsFunctor φ).app A f).ofConv) h = f.ofConv (toBialgHom φ h) := by
  exact AlgHom.mapDomain_apply_apply (A := A) (toBialgHom φ) f h

/-- `mapPointsFunctor` sends the identity coordinate morphism to the identity natural
transformation. -/
@[simp]
lemma mapPointsFunctor_id (H : CommHopfAlgCat.{v} R) :
    mapPointsFunctor (𝟙 H) =
      𝟙 (HopfAlgebra.pointsFunctor (R := R) (H := H) :
        CommAlgCat.{w} R ⥤ GrpCat.{max v w}) := by
  ext A f
  simp

/-- `mapPointsFunctor` sends coordinate-algebra composition to reverse composition of natural
transformations. -/
lemma mapPointsFunctor_comp {H K L : CommHopfAlgCat.{v} R} (φ : H ⟶ K) (ψ : K ⟶ L) :
    mapPointsFunctor (φ ≫ ψ) =
      mapPointsFunctor ψ ≫ mapPointsFunctor φ := by
  ext A f
  simp [mapPointsFunctor_app_apply, AlgHom.comp_assoc]

/-- The contravariant functor assigning to a commutative Hopf algebra its group-valued
functor of points.

A coordinate Hopf algebra `H` is sent to the functor `A ↦ WithConv (H →ₐ[R] A)`. A morphism
`φ : H ⟶ K` is sent contravariantly to the natural transformation that pre-composes
`K`-points by `φ`. -/
noncomputable def pointsFunctor :
    (CommHopfAlgCat.{v} R)ᵒᵖ ⥤ CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj H := HopfAlgebra.pointsFunctor (R := R) (H := H.unop)
  map φ := mapPointsFunctor φ.unop
  map_id H := mapPointsFunctor_id (R := R) H.unop
  map_comp φ ψ := mapPointsFunctor_comp (R := R) ψ.unop φ.unop

/-- The object part of `pointsFunctor` is the points functor of the underlying commutative
Hopf algebra. -/
lemma pointsFunctor_obj (H : (CommHopfAlgCat.{v} R)ᵒᵖ) :
    (pointsFunctor (R := R)).obj H =
      HopfAlgebra.pointsFunctor (R := R) (H := H.unop) :=
  rfl

/-- The morphism part of `pointsFunctor` is pre-composition in the coordinate commutative
Hopf algebra. -/
lemma pointsFunctor_map {H K : (CommHopfAlgCat.{v} R)ᵒᵖ} (φ : H ⟶ K) :
    (pointsFunctor (R := R)).map φ =
      mapPointsFunctor φ.unop :=
  rfl

/-- Pointwise form of the morphism part of `pointsFunctor`. -/
@[simp]
lemma pointsFunctor_map_app_apply_apply {H K : (CommHopfAlgCat.{v} R)ᵒᵖ}
    (φ : H ⟶ K) (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := H.unop) A) (h : K.unop) :
    ((((pointsFunctor (R := R)).map φ).app A f).ofConv) h =
      f.ofConv (toBialgHom φ.unop h) := by
  rw [pointsFunctor_map]
  exact mapPointsFunctor_app_apply_apply (R := R) φ.unop A f h

end CommHopfAlgCat

/-!
### Deprecated declarations

The declarations below were part of Tau Ceti's hand-rolled `CommHopfAlgCat`, defined as a
`CategoryTheory.ObjectProperty.FullSubcategory` of `HopfAlgCat R`. They are superseded by
Mathlib's bundled `CommHopfAlgCat` and kept here only as deprecated wrappers so existing
references continue to compile.
-/

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- Deprecated. The underlying ring of an object of `CommHopfAlgCat R` is commutative; this is
now provided directly by Mathlib's bundled `CommHopfAlgCat`. -/
@[deprecated "Provided by Mathlib's bundled CommHopfAlgCat" (since := "2026-06-19")]
abbrev commRing (H : CommHopfAlgCat.{v} R) : CommRing H := inferInstance

/-- Deprecated. The underlying type of an object of `CommHopfAlgCat R` is a Hopf algebra; this
is now provided directly by Mathlib's bundled `CommHopfAlgCat`. -/
@[deprecated "Provided by Mathlib's bundled CommHopfAlgCat" (since := "2026-06-19")]
abbrev hopfAlgebra (H : CommHopfAlgCat.{v} R) : _root_.HopfAlgebra R H := inferInstance

@[deprecated CommHopfAlgCat.hom_id (since := "2026-06-19")]
lemma toBialgHom_id {H : CommHopfAlgCat.{v} R} :
    toBialgHom (𝟙 H : H ⟶ H) = BialgHom.id R H :=
  rfl

@[deprecated CommHopfAlgCat.hom_comp (since := "2026-06-19")]
lemma toBialgHom_comp {H K L : CommHopfAlgCat.{v} R} (φ : H ⟶ K) (ψ : K ⟶ L) :
    toBialgHom (φ ≫ ψ) = (toBialgHom ψ).comp (toBialgHom φ) :=
  rfl

@[deprecated CommHopfAlgCat.ofHom_hom (since := "2026-06-19")]
lemma ofHom_toBialgHom {H K : CommHopfAlgCat.{v} R} (φ : H ⟶ K) :
    _root_.CommHopfAlgCat.ofHom (toBialgHom φ) = φ :=
  rfl

@[deprecated CommHopfAlgCat.hom_ofHom (since := "2026-06-19")]
lemma toBialgHom_ofHom {H K : Type v} [CommRing H] [CommRing K]
    [_root_.HopfAlgebra R H] [_root_.HopfAlgebra R K] (φ : H →ₐc[R] K) :
    toBialgHom (_root_.CommHopfAlgCat.ofHom (R := R) φ) = φ :=
  rfl

end CommHopfAlgCat

/-- Deprecated. The object property on `HopfAlgCat R` selecting commutative Hopf algebras. It
backed Tau Ceti's hand-rolled `CommHopfAlgCat` as a `FullSubcategory` of `HopfAlgCat R`; the
category is now Mathlib's bundled `CommHopfAlgCat`, so this property is unused. -/
@[deprecated "Unused after rebasing onto mathlib's bundled CommHopfAlgCat" (since := "2026-06-19")]
def commHopfAlgProperty (R : Type u) [CommRing R] :
    ObjectProperty (_root_.HopfAlgCat.{v} R) :=
  fun H => ∀ x y : H, x * y = y * x

end TauCeti
