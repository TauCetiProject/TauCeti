/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import TauCeti.AlgebraicGeometry.Neron.Model

/-!
# Weak Néron models

Let `j : η ⟶ S` be a morphism of schemes; in the arithmetic application `j` is the inclusion of
the generic point of a discrete valuation ring or Dedekind scheme. An object `X` of `Over S` has
the *weak Néron mapping property* relative to `j` when, for every `S`-scheme `Y` with *étale*
structure morphism, base change along `j` induces a bijection
`Hom_S(Y, X) → Hom_η(Y ×_S η, X ×_S η)`. Over a discrete valuation ring `R` this is the
étale-local form of the condition of Bosch–Lütkebohmert–Raynaud, §3.5, that points of the generic
fibre with values in the fraction field of the strict henselization `R^sh` extend to
`R^sh`-points.

A *weak Néron model* of `A` in `Over η` is a smooth, separated, quasi-compact `S`-scheme with a
marking of its base change along `j` by `A` and the weak Néron mapping property. Since étale
morphisms are smooth, every Néron model is a weak Néron model (`WeakNeronModel.ofNeronModel`),
with the same total space and marking. The converse fails: blowing up a closed point of the
special fibre of a good elliptic model and taking the smooth locus gives a weak Néron model that
is not a Néron model, and weak Néron models are not unique. They are the output of the
smoothening process, and a weak Néron model of an abelian variety is upgraded to a Néron model
using the group law.

Every generic morphism from an étale test object extends uniquely into a weak Néron model
(`WeakNeronModel.extend`), and composing with the canonical morphism from a weak Néron model to
a Néron model of the same generic fibre turns this extension into the extension of the Néron
model (`WeakNeronModel.extend_comp_extend`).

## Main definitions

* `TauCeti.AlgebraicGeometry.Neron.WeakNeronMappingProperty j X`: every étale `S`-scheme `Y`
  has bijective restriction map `(Y ⟶ X) → ((Over.pullback j).obj Y ⟶ (Over.pullback j).obj X)`.
* `TauCeti.AlgebraicGeometry.Neron.WeakNeronModel j A`: a marked finite-type weak Néron model
  of `A`.
* `WeakNeronModel.homEquiv`, `WeakNeronModel.extend`: marked restriction and its inverse, for
  étale test objects.
* `WeakNeronModel.ofNeronModel`: a Néron model, regarded as a weak Néron model.

## Main results

* `NeronMappingProperty.weakNeronMappingProperty`: the Néron mapping property implies the weak
  one.
* `weakNeronMappingProperty_iff_existsUnique`: the weak property is unique extension of generic
  morphisms from étale test objects.
* `WeakNeronMappingProperty.of_iso`: the weak property is invariant under isomorphism.
* `WeakNeronModel.extend_comp_extend`: extension into a weak Néron model followed by the
  canonical morphism to a Néron model is extension into the Néron model.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 21, Springer, 1990, §1.2, Definition 1, and §3.5, Definition 1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Neron

universe u

variable {η S : Scheme.{u}}

/-- An object `X` of `Over S` has the *weak Néron mapping property* relative to `j : η ⟶ S`
when, for every `S`-scheme `Y` with étale structure morphism, base change along `j` is a
bijection from the `S`-morphisms `Y ⟶ X` to the `η`-morphisms between the base changes of `Y`
and `X`. This is the Néron mapping property of Bosch–Lütkebohmert–Raynaud, *Néron Models*,
§1.2, Definition 1, with the smooth test objects replaced by étale ones. -/
structure WeakNeronMappingProperty (j : η ⟶ S) (X : Over S) : Prop where
  /-- Base change along `j` is bijective on morphisms from every étale test object. -/
  bijective (Y : Over S) [Etale Y.hom] :
    Function.Bijective ((Over.pullback j).map : (Y ⟶ X) → _)

namespace WeakNeronMappingProperty

variable {j : η ⟶ S} {X : Over S}

/-- Base change along `j` is injective on morphisms from an étale test object. -/
theorem injective (h : WeakNeronMappingProperty j X) (Y : Over S) [Etale Y.hom] :
    Function.Injective ((Over.pullback j).map : (Y ⟶ X) → _) :=
  (h.bijective Y).1

/-- Base change along `j` is surjective on morphisms from an étale test object. -/
theorem surjective (h : WeakNeronMappingProperty j X) (Y : Over S) [Etale Y.hom] :
    Function.Surjective ((Over.pullback j).map : (Y ⟶ X) → _) :=
  (h.bijective Y).2

/-- Every morphism from the base change of an étale test object `Y` to the base change of `X`
extends uniquely to an `S`-morphism `Y ⟶ X`. -/
theorem existsUnique (h : WeakNeronMappingProperty j X) (Y : Over S) [Etale Y.hom]
    (f : (Over.pullback j).obj Y ⟶ (Over.pullback j).obj X) :
    ∃! g : Y ⟶ X, (Over.pullback j).map g = f :=
  (h.bijective Y).existsUnique f

/-- Two `S`-morphisms from an étale test object into an object with the weak Néron mapping
property are equal as soon as their base changes along `j` are. -/
theorem hom_ext (h : WeakNeronMappingProperty j X) {Y : Over S} [Etale Y.hom] {f g : Y ⟶ X}
    (hfg : (Over.pullback j).map f = (Over.pullback j).map g) : f = g :=
  h.injective Y hfg

/-- The weak Néron mapping property is invariant under isomorphism in `Over S`. -/
theorem of_iso (h : WeakNeronMappingProperty j X) {X' : Over S} (e : X ≅ X') :
    WeakNeronMappingProperty j X' where
  bijective Y _ := by
    refine ⟨fun f g hfg ↦ (cancel_mono e.inv).1 (h.hom_ext ?_), fun f ↦ ?_⟩
    · simp only [Functor.map_comp, hfg]
    · obtain ⟨g, hg⟩ := h.surjective Y (f ≫ (Over.pullback j).map e.inv)
      refine ⟨g ≫ e.hom, ?_⟩
      rw [Functor.map_comp, hg, Category.assoc, ← Functor.map_comp]
      simp

/-- Isomorphic objects of `Over S` have the weak Néron mapping property simultaneously. -/
theorem iff_of_iso {X' : Over S} (e : X ≅ X') :
    WeakNeronMappingProperty j X ↔ WeakNeronMappingProperty j X' :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

end WeakNeronMappingProperty

/-- The weak Néron mapping property says exactly that every generic morphism from an étale test
object extends uniquely. -/
theorem weakNeronMappingProperty_iff_existsUnique {j : η ⟶ S} {X : Over S} :
    WeakNeronMappingProperty j X ↔ ∀ (Y : Over S) [Etale Y.hom]
      (f : (Over.pullback j).obj Y ⟶ (Over.pullback j).obj X),
      ∃! g : Y ⟶ X, (Over.pullback j).map g = f :=
  ⟨fun h Y _ f ↦ h.existsUnique Y f,
    fun h ↦ ⟨fun Y _ ↦ Function.bijective_iff_existsUnique _ |>.2 (h Y)⟩⟩

/-- The Néron mapping property implies the weak Néron mapping property: étale test objects are
smooth. -/
theorem NeronMappingProperty.weakNeronMappingProperty {j : η ⟶ S} {X : Over S}
    (h : NeronMappingProperty j X) : WeakNeronMappingProperty j X :=
  ⟨fun Y _ ↦ h.bijective Y⟩

/-- A marked finite-type *weak Néron model* of an object `A` of `Over η` relative to
`j : η ⟶ S`: an `S`-scheme with smooth, separated and quasi-compact structure morphism, an
isomorphism of its base change along `j` with `A`, and the weak Néron mapping property relative
to `j` (compare Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.5, Definition 1). Unlike a Néron
model, a weak Néron model is not unique. -/
structure WeakNeronModel (j : η ⟶ S) (A : Over η) where
  /-- The total space of the model, as an `S`-scheme. -/
  model : Over S
  /-- The marking: an identification of the base change of the model along `j` with `A`. -/
  genericIso : (Over.pullback j).obj model ≅ A
  /-- The structure morphism of the model is smooth. -/
  smooth : Smooth model.hom
  /-- The structure morphism of the model is separated. -/
  isSeparated : IsSeparated model.hom
  /-- The structure morphism of the model is quasi-compact. -/
  quasiCompact : QuasiCompact model.hom
  /-- The model has the weak Néron mapping property relative to `j`. -/
  weakMappingProperty : WeakNeronMappingProperty j model

namespace WeakNeronModel

attribute [instance] smooth isSeparated quasiCompact

variable {j : η ⟶ S} {A B : Over η} (W : WeakNeronModel j A)

/-- Two `S`-morphisms from an étale test object into a weak Néron model are equal as soon as
their marked restrictions to `A` are. -/
theorem hom_ext {Y : Over S} [Etale Y.hom] {f g : Y ⟶ W.model}
    (h : (Over.pullback j).map f ≫ W.genericIso.hom =
      (Over.pullback j).map g ≫ W.genericIso.hom) : f = g :=
  W.weakMappingProperty.hom_ext ((cancel_mono _).1 h)

/-- For an étale test object `Y`, marked restriction is a bijection from the `S`-morphisms
`Y ⟶ W.model` to the morphisms from the base change of `Y` to `A`. -/
def homEquiv (Y : Over S) [Etale Y.hom] :
    (Y ⟶ W.model) ≃ ((Over.pullback j).obj Y ⟶ A) :=
  (Equiv.ofBijective _ (W.weakMappingProperty.bijective Y)).trans
    ((Iso.refl _).homCongr W.genericIso)

/-- `WeakNeronModel.homEquiv` is marked restriction. -/
@[simp]
theorem homEquiv_apply {Y : Over S} [Etale Y.hom] (g : Y ⟶ W.model) :
    W.homEquiv Y g = (Over.pullback j).map g ≫ W.genericIso.hom := by
  simp [homEquiv]

/-- The extension of a morphism `f` from the base change of an étale test object `Y` to `A`:
the unique `S`-morphism `Y ⟶ W.model` whose marked restriction is `f`. -/
def extend (Y : Over S) [Etale Y.hom] (f : (Over.pullback j).obj Y ⟶ A) : Y ⟶ W.model :=
  (W.homEquiv Y).symm f

/-- The inverse of `WeakNeronModel.homEquiv` is extension. -/
@[simp]
theorem homEquiv_symm_apply {Y : Over S} [Etale Y.hom] (f : (Over.pullback j).obj Y ⟶ A) :
    (W.homEquiv Y).symm f = W.extend Y f :=
  (rfl)

/-- The marked restriction of the extension of `f` is `f`. -/
@[reassoc (attr := simp)]
theorem map_extend {Y : Over S} [Etale Y.hom] (f : (Over.pullback j).obj Y ⟶ A) :
    (Over.pullback j).map (W.extend Y f) ≫ W.genericIso.hom = f := by
  rw [← homEquiv_apply, extend, Equiv.apply_symm_apply]

/-- A morphism into a weak Néron model is the extension of `f` if and only if its marked
restriction is `f`. -/
theorem eq_extend_iff {Y : Over S} [Etale Y.hom] {f : (Over.pullback j).obj Y ⟶ A}
    {g : Y ⟶ W.model} :
    g = W.extend Y f ↔ (Over.pullback j).map g ≫ W.genericIso.hom = f := by
  rw [extend, Equiv.eq_symm_apply, homEquiv_apply]

/-- Uniqueness of the extension: a morphism whose marked restriction is `f` is the extension
of `f`. -/
theorem extend_unique {Y : Over S} [Etale Y.hom] {f : (Over.pullback j).obj Y ⟶ A}
    {g : Y ⟶ W.model} (hg : (Over.pullback j).map g ≫ W.genericIso.hom = f) :
    g = W.extend Y f :=
  W.eq_extend_iff.2 hg

/-- Extending the marked restriction of an `S`-morphism returns that morphism. -/
@[simp]
theorem extend_map {Y : Over S} [Etale Y.hom] (g : Y ⟶ W.model) :
    W.extend Y ((Over.pullback j).map g ≫ W.genericIso.hom) = g :=
  (W.extend_unique rfl).symm

/-- Extension commutes with precomposition by a morphism of étale test objects. -/
theorem extend_map_comp {Y Z : Over S} [Etale Y.hom] [Etale Z.hom] (g : Z ⟶ Y)
    (f : (Over.pullback j).obj Y ⟶ A) :
    W.extend Z ((Over.pullback j).map g ≫ f) = g ≫ W.extend Y f :=
  (W.extend_unique (by simp)).symm

/-- Extension into a weak Néron model `W` of `A`, followed by the extension `W.model ⟶ M.model`
of a morphism `φ : A ⟶ B` into a Néron model `M` of `B`, is the extension into `M` of the
composite with `φ`. For `φ = 𝟙 A` this says that extensions into a weak Néron model become
extensions into the Néron model under the canonical morphism between them. -/
@[reassoc (attr := simp)]
theorem extend_comp_extend (M : NeronModel j B) {Y : Over S} [Etale Y.hom]
    (f : (Over.pullback j).obj Y ⟶ A) (φ : A ⟶ B) :
    W.extend Y f ≫ M.extend W.model (W.genericIso.hom ≫ φ) = M.extend Y (f ≫ φ) :=
  M.extend_unique (by simp)

/-- A Néron model, regarded as a weak Néron model with the same total space and marking.

The body is exposed so that the total space of the converted model is definitionally `M.model`:
this is what makes `ofNeronModel_genericIso` and `ofNeronModel_extend` type-correct. -/
@[expose] def ofNeronModel (M : NeronModel j A) : WeakNeronModel j A where
  model := M.model
  genericIso := M.genericIso
  smooth := M.smooth
  isSeparated := M.isSeparated
  quasiCompact := M.quasiCompact
  weakMappingProperty := M.mappingProperty.weakNeronMappingProperty

@[simp]
theorem ofNeronModel_model (M : NeronModel j A) : (ofNeronModel M).model = M.model :=
  (rfl)

@[simp]
theorem ofNeronModel_genericIso (M : NeronModel j A) :
    (ofNeronModel M).genericIso = M.genericIso :=
  (rfl)

/-- Extension into a Néron model, regarded as a weak Néron model, is its extension as a Néron
model. -/
@[simp]
theorem ofNeronModel_extend (M : NeronModel j A) {Y : Over S} [Etale Y.hom]
    (f : (Over.pullback j).obj Y ⟶ A) : (ofNeronModel M).extend Y f = M.extend Y f :=
  M.extend_unique ((ofNeronModel M).map_extend f)

end WeakNeronModel

end TauCeti.AlgebraicGeometry.Neron
