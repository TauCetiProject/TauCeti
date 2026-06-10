/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.Category.CommBialgCat
import Mathlib.Algebra.Category.HopfAlgCat.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import TauCeti.Algebra.AlgebraicGroup.HopfMap
import TauCeti.Algebra.AlgebraicGroup.PointsFunctor

/-!
# Commutative Hopf algebras and their functor of points

This file bundles commutative Hopf algebras over a commutative ring `R` into a category and
packages the contravariant functor that sends such a coordinate Hopf algebra `H` to its
group-valued functor of points `A ↦ Hom_R(H, A)`.

This is the categorical form of the first concrete target in the Tau Ceti reductive-groups
roadmap, Layer 0, "R-points as a group": for a commutative Hopf algebra representing an
affine group scheme, the functor of points is group-valued by convolution, and a morphism of
coordinate Hopf algebras acts on points by pre-composition.

## Main declarations

* `CommHopfAlgCat`: the category of commutative Hopf algebras over `R`.
* `CommHopfAlgCat.mapPointsFunctor`: a coordinate morphism `H ⟶ K` induces a natural
  transformation from the points functor of `K` to the points functor of `H`.
* `CommHopfAlgCat.pointsFunctor`: the contravariant functor
  `(CommHopfAlgCat R)ᵒᵖ ⥤ CommAlgCat R ⥤ GrpCat`.

## References

The bundled-category and forgetful-functor skeleton for `CommHopfAlgCat` follows Mathlib's
`Mathlib.Algebra.Category.HopfAlgCat.Basic` and
`Mathlib.Algebra.Category.CommBialgCat`. The points functoriality uses Mathlib's
convolution monoid and bialgebra morphism API, in particular
`AlgHom.convMul_comp_bialgHom_distrib` from
`Mathlib.RingTheory.Bialgebra.Convolution`, through the Tau Ceti wrapper
`AlgHom.mapDomain`.
-/

open CategoryTheory WithConv

namespace TauCeti

universe u v w

/-- The object property on `HopfAlgCat R` selecting commutative Hopf algebras. -/
def commHopfAlgProperty (R : Type u) [CommRing R] :
    ObjectProperty (_root_.HopfAlgCat.{v} R) :=
  fun H => ∀ x y : H, x * y = y * x

/-- The category of commutative Hopf algebras over a commutative ring `R`.

This is the full subcategory of Mathlib's `HopfAlgCat R` on objects whose multiplication is
commutative. Morphisms are therefore the existing `HopfAlgCat` morphisms, i.e. bialgebra
morphisms. A bialgebra morphism between Hopf algebras automatically preserves the antipode, by
`BialgHom.map_antipode`, so no extra field is needed in the morphism type. -/
abbrev CommHopfAlgCat (R : Type u) [CommRing R] :=
  (commHopfAlgProperty (R := R)).FullSubcategory

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R]

instance : CoeSort (CommHopfAlgCat.{u, v} R) (Type v) :=
  ⟨fun H => H.obj⟩

instance commRing (H : CommHopfAlgCat.{u, v} R) : CommRing H :=
  CommRing.mk H.property

instance hopfAlgebra (H : CommHopfAlgCat.{u, v} R) : _root_.HopfAlgebra R H :=
  inferInstanceAs (_root_.HopfAlgebra R H.obj)

variable (R) in
set_option backward.privateInPublic.warn false in
/-- Construct a bundled commutative Hopf algebra from the usual unbundled typeclasses. -/
abbrev of (H : Type v) [CommRing H] [_root_.HopfAlgebra R H] : CommHopfAlgCat.{u, v} R :=
  ⟨_root_.HopfAlgCat.of R H, fun x y => mul_comm x y⟩

/-- Turn a morphism in `CommHopfAlgCat` back into a bialgebra morphism. -/
abbrev toBialgHom {H K : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K) : H →ₐc[R] K :=
  φ.hom.toBialgHom

/-- Typecheck a bialgebra morphism as a morphism in `CommHopfAlgCat`. -/
abbrev ofHom {H K : Type v} [CommRing H] [CommRing K]
    [_root_.HopfAlgebra R H] [_root_.HopfAlgebra R K] (φ : H →ₐc[R] K) :
    of R H ⟶ of R K :=
  ObjectProperty.homMk (_root_.HopfAlgCat.ofHom φ)

/-- Two morphisms of commutative Hopf algebras are equal when their underlying bialgebra
morphisms are equal. -/
@[ext]
lemma hom_ext {H K : CommHopfAlgCat.{u, v} R} {φ ψ : H ⟶ K}
    (h : toBialgHom φ = toBialgHom ψ) : φ = ψ :=
  ObjectProperty.hom_ext (P := commHopfAlgProperty R)
    (_root_.HopfAlgCat.hom_ext φ.hom ψ.hom h)

@[simp]
lemma toBialgHom_id {H : CommHopfAlgCat.{u, v} R} :
    toBialgHom (𝟙 H : H ⟶ H) = BialgHom.id R H :=
  rfl

@[simp]
lemma toBialgHom_comp {H K L : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K) (ψ : K ⟶ L) :
    toBialgHom (φ ≫ ψ) = (toBialgHom ψ).comp (toBialgHom φ) :=
  rfl

@[simp]
lemma ofHom_toBialgHom {H K : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K) :
    ofHom (toBialgHom φ) = φ :=
  rfl

@[simp]
lemma toBialgHom_ofHom {H K : Type v} [CommRing H] [CommRing K]
    [_root_.HopfAlgebra R H] [_root_.HopfAlgebra R K] (φ : H →ₐc[R] K) :
    toBialgHom (ofHom (R := R) φ) = φ :=
  rfl

/-- The forgetful functor from commutative Hopf algebras to commutative bialgebras. -/
instance hasForgetToCommBialgCat :
    HasForget₂ (CommHopfAlgCat.{u, v} R) (CommBialgCat.{v} R) where
  forget₂ :=
    { obj H := CommBialgCat.of R H
      map φ := CommBialgCat.ofHom (toBialgHom φ) }

@[simp]
lemma forget₂_commBialgCat_obj (H : CommHopfAlgCat.{u, v} R) :
    (forget₂ (CommHopfAlgCat.{u, v} R) (CommBialgCat.{v} R)).obj H =
      CommBialgCat.of R H :=
  rfl

@[simp]
lemma forget₂_commBialgCat_map {H K : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K) :
    (forget₂ (CommHopfAlgCat.{u, v} R) (CommBialgCat.{v} R)).map φ =
      CommBialgCat.ofHom (toBialgHom φ) :=
  rfl

@[simp]
lemma forget₂_hopfAlgCat_obj (H : CommHopfAlgCat.{u, v} R) :
    (forget₂ (CommHopfAlgCat.{u, v} R) (_root_.HopfAlgCat.{v} R)).obj H =
      H.obj :=
  rfl

@[simp]
lemma forget₂_hopfAlgCat_map {H K : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K) :
    (forget₂ (CommHopfAlgCat.{u, v} R) (_root_.HopfAlgCat.{v} R)).map φ =
      φ.hom :=
  rfl

/-- A morphism of coordinate commutative Hopf algebras induces a natural transformation
between their group-valued points functors, contravariantly in the coordinate algebra.

At a commutative `R`-algebra `A`, this sends an `A`-valued point `f : K →ₐ[R] A` to
`f ∘ φ : H →ₐ[R] A`. -/
noncomputable def mapPointsFunctor {H K : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K) :
    HopfAlgebra.pointsFunctor (R := R) (H := K) ⟶
      HopfAlgebra.pointsFunctor (R := R) (H := H) where
  app A := GrpCat.ofHom
    (AlgHom.mapDomain (H₁ := H) (H₂ := K) (A := A) (toBialgHom φ))
  naturality {A B} ψ := by
    simp only [HopfAlgebra.pointsFunctor_map, HopfAlgebra.mapPoints]
    exact GrpCat.hom_ext (AlgHom.mapValue_mapDomain (toBialgHom φ) ψ.hom)

/-- On points, `mapPointsFunctor φ` is pre-composition with `φ`. -/
@[simp]
lemma mapPointsFunctor_app_apply {H K : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K)
    (A : CommAlgCat.{w} R) (f : HopfAlgebra.points (R := R) (H := K) A) :
    (mapPointsFunctor φ).app A f =
      toConv (f.ofConv.comp (toBialgHom φ : H →ₐ[R] K)) := by
  exact AlgHom.mapDomain_apply (A := A) (toBialgHom φ) f

/-- Pointwise form of `mapPointsFunctor_app_apply`. -/
@[simp]
lemma mapPointsFunctor_app_apply_apply {H K : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K)
    (A : CommAlgCat.{w} R) (f : HopfAlgebra.points (R := R) (H := K) A) (h : H) :
    (((mapPointsFunctor φ).app A f).ofConv) h = f.ofConv (toBialgHom φ h) := by
  exact AlgHom.mapDomain_apply_apply (A := A) (toBialgHom φ) f h

/-- `mapPointsFunctor` sends the identity coordinate morphism to the identity natural
transformation. -/
@[simp]
lemma mapPointsFunctor_id (H : CommHopfAlgCat.{u, v} R) :
    mapPointsFunctor (𝟙 H) =
      𝟙 (HopfAlgebra.pointsFunctor (R := R) (H := H) :
        CommAlgCat.{w} R ⥤ GrpCat.{max v w}) := by
  ext A f
  simp

/-- `mapPointsFunctor` sends coordinate-algebra composition to reverse composition of natural
transformations. -/
lemma mapPointsFunctor_comp {H K L : CommHopfAlgCat.{u, v} R} (φ : H ⟶ K) (ψ : K ⟶ L) :
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
    (CommHopfAlgCat.{u, v} R)ᵒᵖ ⥤ CommAlgCat.{w} R ⥤ GrpCat.{max v w} where
  obj H := HopfAlgebra.pointsFunctor (R := R) (H := H.unop)
  map φ := mapPointsFunctor φ.unop
  map_id H := mapPointsFunctor_id (R := R) H.unop
  map_comp φ ψ := mapPointsFunctor_comp (R := R) ψ.unop φ.unop

/-- The object part of `pointsFunctor` is the points functor of the underlying commutative
Hopf algebra. -/
lemma pointsFunctor_obj (H : (CommHopfAlgCat.{u, v} R)ᵒᵖ) :
    (pointsFunctor (R := R)).obj H =
      HopfAlgebra.pointsFunctor (R := R) (H := H.unop) :=
  rfl

/-- The morphism part of `pointsFunctor` is pre-composition in the coordinate commutative
Hopf algebra. -/
lemma pointsFunctor_map {H K : (CommHopfAlgCat.{u, v} R)ᵒᵖ} (φ : H ⟶ K) :
    (pointsFunctor (R := R)).map φ =
      mapPointsFunctor φ.unop :=
  rfl

/-- Pointwise form of the morphism part of `pointsFunctor`. -/
@[simp]
lemma pointsFunctor_map_app_apply_apply {H K : (CommHopfAlgCat.{u, v} R)ᵒᵖ}
    (φ : H ⟶ K) (A : CommAlgCat.{w} R)
    (f : HopfAlgebra.points (R := R) (H := H.unop) A) (h : K.unop) :
    ((((pointsFunctor (R := R)).map φ).app A f).ofConv) h =
      f.ofConv (toBialgHom φ.unop h) := by
  rw [pointsFunctor_map]
  exact mapPointsFunctor_app_apply_apply (R := R) φ.unop A f h

end CommHopfAlgCat

end TauCeti
