/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.NeronModel.MappingProperty

/-!
# Marked finite-type Néron models and their uniqueness

For a morphism of schemes `j : η ⟶ S` and `A` in `Over η`, a `NeronModel j A` is an object
`model` of `Over S` with smooth, separated, quasi-compact structure morphism and the Néron
mapping property, together with a marking `genericIso` of its pullback along `j` with `A`
(Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2, Definition 1 and Proposition 2, pp. 12–13).

Every generic morphism `f` from the pullback of a smooth `Y` to `A` extends uniquely to an
`S`-morphism `M.extend Y f : Y ⟶ M.model`. The extensions between two marked models of `A` are
mutually inverse, and `NeronModel.unique_iso` says there is exactly one isomorphism of models
compatible with the markings (Bosch–Lütkebohmert–Raynaud, §1.2, Proposition 2(a)).

The marking matters: changing it changes the compatibility equation, so `unique_iso` is
stronger than the unmarked statement that any two Néron models are isomorphic.

## Main declarations

* `TauCeti.AlgebraicGeometry.NeronModel`: marked finite-type Néron models.
* `NeronModel.extend`: extension of a generic morphism from a smooth test object.
* `NeronModel.extend_isIso`: the extension between two marked models is an isomorphism.
* `NeronModel.unique_iso`: uniqueness of marked Néron models up to unique isomorphism.
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {η S : Scheme.{u}} (j : η ⟶ S)

/-- A marked finite-type Néron model of `A` in `Over η` relative to `j : η ⟶ S`: an object of
`Over S` with smooth, separated and quasi-compact structure morphism and the Néron mapping
property, with an isomorphism of its pullback along `j` with `A`
(Bosch–Lütkebohmert–Raynaud, §1.2, Definition 1). -/
structure NeronModel (A : Over η) where
  /-- The model, an object of `Over S`. -/
  model : Over S
  /-- The marking: the pullback of the model along `j` is identified with `A`. -/
  genericIso : (Over.pullback j).obj model ≅ A
  /-- The structure morphism of the model is smooth. -/
  smooth : Smooth model.hom
  /-- The structure morphism of the model is separated. -/
  separated : IsSeparated model.hom
  /-- The structure morphism of the model is quasi-compact. -/
  quasiCompact : QuasiCompact model.hom
  /-- The model has the Néron mapping property relative to `j`. -/
  mapping : NeronMappingProperty j model

namespace NeronModel

attribute [instance] smooth separated quasiCompact

variable {j} {A : Over η} (M : NeronModel j A)

/-- Marked extensionality: two morphisms from a smooth test object to the model whose marked
restrictions agree are equal. -/
theorem hom_ext {Y : Over S} [Smooth Y.hom] {f g : Y ⟶ M.model}
    (h : (Over.pullback j).map f ≫ M.genericIso.hom =
      (Over.pullback j).map g ≫ M.genericIso.hom) : f = g :=
  M.mapping.hom_ext (by simpa using h)

/-- Every morphism from the pullback of a smooth test object to `A` is the marked restriction of
exactly one morphism to the model. -/
theorem extension_existsUnique {Y : Over S} [Smooth Y.hom] (f : (Over.pullback j).obj Y ⟶ A) :
    ∃! g : Y ⟶ M.model, (Over.pullback j).map g ≫ M.genericIso.hom = f := by
  obtain ⟨g, hg, hg'⟩ := M.mapping.existsUnique (f ≫ M.genericIso.inv)
  refine ⟨g, by simp [hg], fun g' hg'' ↦ hg' g' ?_⟩
  simp [← hg'']

/-- An endomorphism of the model whose marked restriction is the marking is the identity. -/
theorem identity_unique {f : M.model ⟶ M.model}
    (hf : (Over.pullback j).map f ≫ M.genericIso.hom = M.genericIso.hom) : f = 𝟙 M.model :=
  M.hom_ext (by simpa using hf)

/-- The extension of a morphism `f` from the pullback of a smooth test object `Y` to `A`: the
unique `S`-morphism `Y ⟶ M.model` whose marked restriction is `f`
(Bosch–Lütkebohmert–Raynaud, §1.2, Proposition 2). -/
def extend (Y : Over S) [Smooth Y.hom] (f : (Over.pullback j).obj Y ⟶ A) : Y ⟶ M.model :=
  (Equiv.ofBijective _ (M.mapping.bijective Y)).symm (f ≫ M.genericIso.inv)

/-- Unfolding lemma for `NeronModel.extend`. -/
theorem extend_def (Y : Over S) [Smooth Y.hom] (f : (Over.pullback j).obj Y ⟶ A) :
    M.extend Y f = (Equiv.ofBijective _ (M.mapping.bijective Y)).symm (f ≫ M.genericIso.inv) :=
  (rfl)

/-- The marked restriction of `M.extend Y f` is `f`. -/
@[reassoc (attr := simp)]
theorem extend_restrict (Y : Over S) [Smooth Y.hom] (f : (Over.pullback j).obj Y ⟶ A) :
    (Over.pullback j).map (M.extend Y f) ≫ M.genericIso.hom = f := by
  have := (Equiv.ofBijective _ (M.mapping.bijective Y)).apply_symm_apply (f ≫ M.genericIso.inv)
  simp only [Equiv.ofBijective_apply] at this
  simp [extend, this]

/-- A morphism whose marked restriction is `f` is the extension of `f`. -/
theorem extend_unique {Y : Over S} [Smooth Y.hom] {f : (Over.pullback j).obj Y ⟶ A}
    (g : Y ⟶ M.model) (hg : (Over.pullback j).map g ≫ M.genericIso.hom = f) :
    g = M.extend Y f :=
  M.hom_ext (by simp [hg])

/-- Extending the marked restriction of an `S`-morphism returns that morphism. -/
@[simp]
theorem extend_map {Y : Over S} [Smooth Y.hom] (g : Y ⟶ M.model) :
    M.extend Y ((Over.pullback j).map g ≫ M.genericIso.hom) = g :=
  (M.extend_unique g rfl).symm

/-- Extending the marking of `M` from the model itself gives the identity. -/
@[simp]
theorem extend_identity : M.extend M.model M.genericIso.hom = 𝟙 M.model :=
  (M.extend_unique _ (by simp)).symm

/-- Extension commutes with precomposition by a morphism of smooth test objects. -/
theorem extend_precomp {Z Y : Over S} [Smooth Z.hom] [Smooth Y.hom] (g : Z ⟶ Y)
    (f : (Over.pullback j).obj Y ⟶ A) :
    M.extend Z ((Over.pullback j).map g ≫ f) = g ≫ M.extend Y f :=
  (M.extend_unique _ (by simp)).symm

/-- The extensions between three marked models of `A` compose: extending from `P` to `N` and
then from `N` to `M` is extending from `P` to `M`. -/
theorem extend_comp_model (P N : NeronModel j A) :
    N.extend P.model P.genericIso.hom ≫ M.extend N.model N.genericIso.hom =
      M.extend P.model P.genericIso.hom :=
  M.extend_unique _ (by simp)

/-- The extensions between two marked models of `A` are mutually inverse. -/
@[reassoc (attr := simp)]
theorem extend_inverse_model (N : NeronModel j A) :
    N.extend M.model M.genericIso.hom ≫ M.extend N.model N.genericIso.hom = 𝟙 M.model := by
  rw [M.extend_comp_model, extend_identity]

/-- The extension between two marked models of `A` is an isomorphism. -/
instance extend_isIso (N : NeronModel j A) : IsIso (N.extend M.model M.genericIso.hom) :=
  ⟨⟨M.extend N.model N.genericIso.hom, by simp, by simp⟩⟩

/-- Uniqueness of marked Néron models: between two marked models of `A` there is exactly one
isomorphism in `Over S` compatible with the markings
(Bosch–Lütkebohmert–Raynaud, §1.2, Proposition 2(a)). -/
theorem unique_iso (N : NeronModel j A) :
    ∃! e : M.model ≅ N.model,
      (Over.pullback j).map e.hom ≫ N.genericIso.hom = M.genericIso.hom := by
  refine ⟨⟨N.extend M.model M.genericIso.hom, M.extend N.model N.genericIso.hom, by simp,
    by simp⟩, by simp, fun e he ↦ Iso.ext (N.extend_unique e.hom he)⟩

end NeronModel

end TauCeti.AlgebraicGeometry
