/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Restriction of scalars for commutative algebra categories

Given a ring homomorphism `k → K`, a commutative `K`-algebra is in particular a commutative
`k`-algebra, and a `K`-algebra homomorphism is a `k`-algebra homomorphism. This file packages
that change of rings as a functor `CommAlgCat K ⥤ CommAlgCat k`.

Mathlib provides the analogous `AlgCat.restrictScalars` on the
(not-necessarily-commutative) algebra category; this is its commutative counterpart.

## Main declarations

* `TauCeti.CommAlgCat.restrictScalarsObj`: the underlying commutative `k`-algebra of a
  commutative `K`-algebra, along a fixed ring homomorphism `k →+* K`.
* `TauCeti.CommAlgCat.restrictScalars`: the restriction-of-scalars functor
  `CommAlgCat K ⥤ CommAlgCat k` along a fixed ring homomorphism `k →+* K`.
* `TauCeti.CommAlgCat.restrictScalarsMap_hom`: the underlying algebra hom of a restricted
  categorical morphism.
-/

public section

open CategoryTheory

namespace TauCeti

namespace CommAlgCat

universe x u w

variable {k : Type u} {K : Type w} [CommRing k] [CommRing K]

/-- Restrict a commutative `K`-algebra to a commutative `k`-algebra along `f : k →+* K`. -/
noncomputable abbrev restrictScalarsObj (f : k →+* K) (A : _root_.CommAlgCat.{x} K) :
    _root_.CommAlgCat.{x} k :=
  letI : Algebra k A := Algebra.compHom A f
  _root_.CommAlgCat.of k A

/-- The restricted `k`-algebra structure has scalar map `algebraMap K A ∘ f`. -/
@[simp]
lemma algebraMap_restrictScalarsObj (f : k →+* K) (A : _root_.CommAlgCat.{x} K) (r : k) :
    algebraMap k (restrictScalarsObj f A) r = algebraMap K A (f r) :=
  rfl

/-- Restrict a morphism of commutative `K`-algebras to a morphism of commutative
`k`-algebras along `f : k →+* K`. -/
noncomputable abbrev restrictScalarsMap {A B : _root_.CommAlgCat.{x} K}
    (f : k →+* K) (χ : A ⟶ B) :
    restrictScalarsObj f A ⟶ restrictScalarsObj f B :=
  letI : Algebra k K := f.toAlgebra
  letI : Algebra k A := Algebra.compHom A f
  letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra k B := Algebra.compHom B f
  letI : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
  _root_.CommAlgCat.ofHom (χ.hom.restrictScalars k)

/-- The underlying algebra hom of a restricted categorical morphism is restriction of scalars
on the original algebra hom. -/
@[simp]
lemma restrictScalarsMap_hom {A B : _root_.CommAlgCat.{x} K}
    (f : k →+* K) (χ : A ⟶ B) :
    (restrictScalarsMap f χ).hom =
      letI : Algebra k K := f.toAlgebra
      letI : Algebra k A := Algebra.compHom A f
      letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
      letI : Algebra k B := Algebra.compHom B f
      letI : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
      χ.hom.restrictScalars k :=
  rfl

/-- The restriction-of-scalars functor `CommAlgCat K ⥤ CommAlgCat k` along `f : k →+* K`. -/
@[expose] noncomputable def restrictScalars (f : k →+* K) :
    _root_.CommAlgCat.{x} K ⥤ _root_.CommAlgCat.{x} k where
  obj A := restrictScalarsObj f A
  map χ := restrictScalarsMap f χ

/-- The object part of `restrictScalars` is restriction of scalars on algebras. -/
@[simp]
lemma restrictScalars_obj (f : k →+* K) (A : _root_.CommAlgCat.{x} K) :
    (restrictScalars f).obj A = restrictScalarsObj f A :=
  rfl

/-- The morphism part of `restrictScalars` is restriction of scalars on morphisms. -/
@[simp]
lemma restrictScalars_map (f : k →+* K) {A B : _root_.CommAlgCat.{x} K} (χ : A ⟶ B) :
    (restrictScalars f).map χ = restrictScalarsMap f χ :=
  rfl

/-- The underlying algebra hom of `restrictScalars.map` is restriction of scalars on the
original algebra hom. -/
@[simp]
lemma restrictScalars_map_hom (f : k →+* K) {A B : _root_.CommAlgCat.{x} K} (χ : A ⟶ B) :
    ((restrictScalars f).map χ).hom =
      letI : Algebra k K := f.toAlgebra
      letI : Algebra k A := Algebra.compHom A f
      letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
      letI : Algebra k B := Algebra.compHom B f
      letI : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
      χ.hom.restrictScalars k :=
  rfl

end CommAlgCat

end TauCeti
