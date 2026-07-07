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

* `TauCeti.CommAlgCat.restrictScalars`: the underlying commutative `k`-algebra of a commutative
  `K`-algebra.
* `TauCeti.CommAlgCat.restrictScalarsFunctor`: the restriction-of-scalars functor
  `CommAlgCat K ⥤ CommAlgCat k` along `k → K`.
-/

public section

open CategoryTheory

namespace TauCeti

namespace CommAlgCat

universe x u w

variable {k : Type u} {K : Type w} [CommRing k] [CommRing K] [Algebra k K]

/-- Restrict a commutative `K`-algebra to a commutative `k`-algebra along `k → K`. -/
noncomputable abbrev restrictScalars (A : _root_.CommAlgCat.{x} K) :
    _root_.CommAlgCat.{x} k :=
  letI : Algebra k A := Algebra.compHom A (algebraMap k K)
  _root_.CommAlgCat.of k A

/-- Restrict a morphism of commutative `K`-algebras to a morphism of commutative
`k`-algebras. -/
noncomputable abbrev restrictScalarsMap {A B : _root_.CommAlgCat.{x} K}
    (χ : A ⟶ B) : restrictScalars (k := k) A ⟶ restrictScalars (k := k) B :=
  letI : Algebra k A := Algebra.compHom A (algebraMap k K)
  letI : IsScalarTower k K A := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra k B := Algebra.compHom B (algebraMap k K)
  letI : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
  _root_.CommAlgCat.ofHom (χ.hom.restrictScalars k)

/-- The restriction-of-scalars functor `CommAlgCat K ⥤ CommAlgCat k` along `k → K`. -/
@[expose] noncomputable def restrictScalarsFunctor :
    _root_.CommAlgCat.{x} K ⥤ _root_.CommAlgCat.{x} k where
  obj A := restrictScalars (k := k) A
  map χ := restrictScalarsMap (k := k) χ

/-- The object part of `restrictScalarsFunctor` is restriction of scalars on algebras. -/
@[simp]
lemma restrictScalarsFunctor_obj (A : _root_.CommAlgCat.{x} K) :
    (restrictScalarsFunctor (k := k) (K := K)).obj A = restrictScalars (k := k) A :=
  rfl

/-- The morphism part of `restrictScalarsFunctor` is restriction of scalars on morphisms. -/
@[simp]
lemma restrictScalarsFunctor_map {A B : _root_.CommAlgCat.{x} K} (χ : A ⟶ B) :
    (restrictScalarsFunctor (k := k) (K := K)).map χ = restrictScalarsMap (k := k) χ :=
  rfl

end CommAlgCat

end TauCeti
