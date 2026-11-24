/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import TauCeti.AlgebraicGeometry.Neron.MappingProperty

/-!
# Marked Néron models

Let `j : η ⟶ S` be a morphism of schemes and `A` an object of `Over η`. A *Néron model* of `A`
is a smooth, separated, quasi-compact `S`-scheme `X` together with an identification (the
*marking*) of its base change along `j` with `A`, such that `X` has the Néron mapping property
relative to `j`. Smoothness already gives local finite presentation, so quasi-compactness is
exactly what makes the model of finite type over `S`. A *weak Néron model* carries the same data
but only the weak Néron mapping property, tested against étale `S`-schemes. We define both at once
as `Model P j A` for a class `P` of test morphisms: `NeronModel j A` is `Model @Smooth j A` and
`WeakNeronModel j A` is `Model @Etale j A`.

The mapping property makes models canonical. Every morphism from the base change of a test object
`Y` to `A` extends uniquely to an `S`-morphism `Y ⟶ X` (`Model.extend`). A model for a class `Q` is
a model for every smaller class `P` (`Model.ofLE`); in particular every Néron model is a weak Néron
model (`WeakNeronModel.ofNeronModel`). For Néron models, every morphism `A ⟶ B` extends uniquely to
a morphism between Néron models of `A` and `B` (`NeronModel.extendHom`), compatibly with identities
and composition, and any two Néron models of the same `A` are related by exactly one isomorphism
compatible with the markings (`NeronModel.existsUnique_iso`). These are the formal consequences of
the mapping property on which the group law of a Néron model and the extension of homomorphisms
rest. Weak Néron models are not unique: blowing up a closed point of the special fibre of a good
elliptic model and taking the smooth locus gives a weak Néron model that is not a Néron model. They
are the output of the smoothening process, and a weak Néron model of an abelian variety is upgraded
to a Néron model using the group law.

## Main definitions

* `TauCeti.AlgebraicGeometry.Neron.Model P j A`: a marked finite-type model of `A` with the
  mapping property for test morphisms in `P`.
* `TauCeti.AlgebraicGeometry.Neron.NeronModel j A`: a marked finite-type Néron model of `A`.
* `TauCeti.AlgebraicGeometry.Neron.WeakNeronModel j A`: a marked finite-type weak Néron model
  of `A`.
* `Model.homEquiv`: the bijection between `S`-morphisms `Y ⟶ M.model` and morphisms
  `(Over.pullback j).obj Y ⟶ A`, for a test object `Y`.
* `Model.extend`: the unique extension of a generic morphism from a test object.
* `Model.ofLE`: a model for a class of test morphisms, regarded as a model for a smaller class.
* `WeakNeronModel.ofNeronModel`: a Néron model, regarded as a weak Néron model.
* `Model.ofIsTerminal`: the base `S` is the model of a terminal object of `Over η`.
* `NeronModel.extendHom`, `NeronModel.extendIso`: the extension of a generic morphism or
  isomorphism to Néron models.

## Main results

* `Model.hom_ext`: morphisms from a test object are determined by their marked restrictions.
* `Model.extend_comp_extend`: extension into one model followed by the extension of a morphism
  `φ : A ⟶ B` into a second model is extension into the second model; for a weak Néron model and
  a Néron model this compares extensions along the canonical morphism between them.
* `NeronModel.extendHom_id`, `NeronModel.extendHom_comp`: extension is functorial.
* `NeronModel.existsUnique_iso`: uniqueness of marked Néron models up to unique marked
  isomorphism.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 21, Springer, 1990, §1.2, Definition 1 and Proposition 2, and §3.5,
  Definition 1.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Neron

universe u

variable {η S : Scheme.{u}}

/-- A marked finite-type *model* of an object `A` of `Over η` relative to `j : η ⟶ S` for the
class `P` of test morphisms: an `S`-scheme with smooth, separated and quasi-compact structure
morphism, an isomorphism of its base change along `j` with `A`, and the mapping property relative
to `j` for test objects in `P`. -/
structure Model (P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop) (j : η ⟶ S) (A : Over η) where
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
  /-- The model has the mapping property relative to `j` for test objects in `P`. -/
  mappingProperty : MappingProperty P j model

/-- A marked finite-type *Néron model* of an object `A` of `Over η` relative to `j : η ⟶ S`: an
`S`-scheme with smooth, separated and quasi-compact structure morphism, an isomorphism of its
base change along `j` with `A`, and the Néron mapping property relative to `j`
(Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2, Definition 1). -/
abbrev NeronModel (j : η ⟶ S) (A : Over η) :=
  Model @Smooth j A

/-- A marked finite-type *weak Néron model* of an object `A` of `Over η` relative to
`j : η ⟶ S`: an `S`-scheme with smooth, separated and quasi-compact structure morphism, an
isomorphism of its base change along `j` with `A`, and the weak Néron mapping property relative
to `j` (compare Bosch–Lütkebohmert–Raynaud, *Néron Models*, §3.5, Definition 1). Unlike a Néron
model, a weak Néron model is not unique. -/
abbrev WeakNeronModel (j : η ⟶ S) (A : Over η) :=
  Model @Etale j A

namespace Model

attribute [instance] smooth isSeparated quasiCompact

variable {P Q : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop} {j : η ⟶ S} {A B : Over η} (M : Model P j A)

/-- Two `S`-morphisms from a test object into a model are equal as soon as their marked
restrictions to `A` are. -/
theorem hom_ext {Y : Over S} (hY : P Y.hom) {f g : Y ⟶ M.model}
    (h : (Over.pullback j).map f ≫ M.genericIso.hom =
      (Over.pullback j).map g ≫ M.genericIso.hom) : f = g :=
  M.mappingProperty.hom_ext hY ((cancel_mono _).1 h)

/-- For a test object `Y`, marked restriction is a bijection from the `S`-morphisms
`Y ⟶ M.model` to the morphisms from the base change of `Y` to `A`. -/
def homEquiv (Y : Over S) (hY : P Y.hom) :
    (Y ⟶ M.model) ≃ ((Over.pullback j).obj Y ⟶ A) :=
  (Equiv.ofBijective _ (M.mappingProperty.bijective Y hY)).trans
    ((Iso.refl _).homCongr M.genericIso)

/-- `Model.homEquiv` is marked restriction. -/
@[simp]
theorem homEquiv_apply {Y : Over S} (hY : P Y.hom) (g : Y ⟶ M.model) :
    M.homEquiv Y hY g = (Over.pullback j).map g ≫ M.genericIso.hom := by
  simp [homEquiv]

/-- The extension of a morphism `f` from the base change of a test object `Y` to `A`: the
unique `S`-morphism `Y ⟶ M.model` whose marked restriction is `f`. -/
def extend (Y : Over S) (hY : P Y.hom) (f : (Over.pullback j).obj Y ⟶ A) : Y ⟶ M.model :=
  (M.homEquiv Y hY).symm f

/-- The inverse of `Model.homEquiv` is extension. -/
@[simp]
theorem homEquiv_symm_apply {Y : Over S} (hY : P Y.hom) (f : (Over.pullback j).obj Y ⟶ A) :
    (M.homEquiv Y hY).symm f = M.extend Y hY f :=
  (rfl)

/-- The marked restriction of the extension of `f` is `f`. -/
@[reassoc (attr := simp)]
theorem map_extend {Y : Over S} (hY : P Y.hom) (f : (Over.pullback j).obj Y ⟶ A) :
    (Over.pullback j).map (M.extend Y hY f) ≫ M.genericIso.hom = f := by
  rw [← homEquiv_apply _ hY, extend, Equiv.apply_symm_apply]

/-- The base change of the extension of `f` is `f` followed by the inverse of the marking. -/
theorem map_extend_eq_comp_inv {Y : Over S} (hY : P Y.hom) (f : (Over.pullback j).obj Y ⟶ A) :
    (Over.pullback j).map (M.extend Y hY f) = f ≫ M.genericIso.inv := by
  simp [← cancel_mono M.genericIso.hom]

/-- A morphism into a model is the extension of `f` if and only if its marked restriction is
`f`. -/
theorem eq_extend_iff {Y : Over S} {hY : P Y.hom} {f : (Over.pullback j).obj Y ⟶ A}
    {g : Y ⟶ M.model} :
    g = M.extend Y hY f ↔ (Over.pullback j).map g ≫ M.genericIso.hom = f := by
  rw [extend, Equiv.eq_symm_apply, homEquiv_apply]

/-- Uniqueness of the extension: a morphism whose marked restriction is `f` is the extension
of `f`. -/
theorem extend_unique {Y : Over S} {hY : P Y.hom} {f : (Over.pullback j).obj Y ⟶ A}
    {g : Y ⟶ M.model} (hg : (Over.pullback j).map g ≫ M.genericIso.hom = f) :
    g = M.extend Y hY f :=
  M.eq_extend_iff.2 hg

/-- Extending the marked restriction of an `S`-morphism returns that morphism. -/
@[simp]
theorem extend_map {Y : Over S} (hY : P Y.hom) (g : Y ⟶ M.model) :
    M.extend Y hY ((Over.pullback j).map g ≫ M.genericIso.hom) = g :=
  (M.extend_unique (hY := hY) rfl).symm

/-- Extending the marking of `M` from `M.model` itself gives the identity. -/
@[simp]
theorem extend_genericIso_hom (hM : P M.model.hom) :
    M.extend M.model hM M.genericIso.hom = 𝟙 M.model :=
  (M.extend_unique (by simp)).symm

/-- Extension commutes with precomposition by a morphism of test objects. -/
theorem extend_map_comp {Y Z : Over S} (hY : P Y.hom) (hZ : P Z.hom) (g : Z ⟶ Y)
    (f : (Over.pullback j).obj Y ⟶ A) :
    M.extend Z hZ ((Over.pullback j).map g ≫ f) = g ≫ M.extend Y hY f :=
  (M.extend_unique (by simp)).symm

/-- The identity is the only endomorphism of a model that is a test object and is compatible
with the marking. -/
theorem eq_id_of_map_comp_genericIso_hom (hM : P M.model.hom) {f : M.model ⟶ M.model}
    (hf : (Over.pullback j).map f ≫ M.genericIso.hom = M.genericIso.hom) : f = 𝟙 M.model :=
  (M.extend_unique (hY := hM) hf).trans (M.extend_genericIso_hom hM)

/-- Extension into a model `M` of `A` for the class `P`, followed by the extension
`M.model ⟶ N.model` of a morphism `φ : A ⟶ B` into a model `N` of `B` for the class `Q`, is the
extension into `N` of the composite with `φ`. For a weak Néron model `M`, a Néron model `N` and
`φ = 𝟙 A` this says that extensions into a weak Néron model become extensions into the Néron
model under the canonical morphism between them (`extend_comp_extend_genericIso_hom`). -/
@[reassoc (attr := simp)]
theorem extend_comp_extend (N : Model Q j B) {Y : Over S} (hY : P Y.hom) (hY' : Q Y.hom)
    (hM : Q M.model.hom) (f : (Over.pullback j).obj Y ⟶ A) (φ : A ⟶ B) :
    M.extend Y hY f ≫ N.extend M.model hM (M.genericIso.hom ≫ φ) = N.extend Y hY' (f ≫ φ) :=
  N.extend_unique (by simp)

/-- Extension into a model `M` of `A` for the class `P`, followed by the canonical morphism
`M.model ⟶ N.model` into a model `N` of `A` for the class `Q`, is extension into `N`. -/
@[reassoc (attr := simp)]
theorem extend_comp_extend_genericIso_hom (N : Model Q j A) {Y : Over S} (hY : P Y.hom)
    (hY' : Q Y.hom) (hM : Q M.model.hom) (f : (Over.pullback j).obj Y ⟶ A) :
    M.extend Y hY f ≫ N.extend M.model hM M.genericIso.hom = N.extend Y hY' f := by
  simpa using M.extend_comp_extend N hY hY' hM f (𝟙 A)

-- Exposed so that importing modules see `(M.ofLE hPQ).model` as definitionally `M.model`, for
-- instance to compose morphisms into the converted model with morphisms out of `M.model`.
/-- A model for the class `Q` of test morphisms, regarded as a model for a smaller class `P`
with the same total space and marking. -/
@[expose] def ofLE (M : Model Q j A) (hPQ : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), P f → Q f) :
    Model P j A where
  model := M.model
  genericIso := M.genericIso
  smooth := M.smooth
  isSeparated := M.isSeparated
  quasiCompact := M.quasiCompact
  mappingProperty := M.mappingProperty.of_le hPQ

@[simp]
theorem ofLE_model (M : Model Q j A) (hPQ : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), P f → Q f) :
    (M.ofLE hPQ).model = M.model :=
  (rfl)

@[simp]
theorem ofLE_genericIso (M : Model Q j A) (hPQ : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), P f → Q f) :
    (M.ofLE hPQ).genericIso = M.genericIso :=
  (rfl)

/-- Extension into a model, regarded as a model for a smaller class of test morphisms, is its
original extension. -/
@[simp]
theorem ofLE_extend (M : Model Q j A) (hPQ : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), P f → Q f)
    {Y : Over S} (hY : P Y.hom) (f : (Over.pullback j).obj Y ⟶ A) :
    (M.ofLE hPQ).extend Y hY f = M.extend Y (hPQ _ hY) f :=
  M.extend_unique ((M.ofLE hPQ).map_extend hY f)

/-- The base `S`, as the terminal object of `Over S`, is the model of any terminal object of
`Over η`, that is, of the trivial group over `η`. -/
def ofIsTerminal (P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop) (j : η ⟶ S) {A : Over η}
    (hA : IsTerminal A) : Model P j A where
  model := Over.mk (𝟙 S)
  genericIso := (Over.mkIdTerminal.isTerminalObj (Over.pullback j) _).uniqueUpToIso hA
  smooth := by dsimp; infer_instance
  isSeparated := by dsimp; infer_instance
  quasiCompact := by dsimp; infer_instance
  mappingProperty := .of_isTerminal Over.mkIdTerminal

@[simp]
theorem ofIsTerminal_model (P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop) (j : η ⟶ S) {A : Over η}
    (hA : IsTerminal A) : (ofIsTerminal P j hA).model = Over.mk (𝟙 S) :=
  (rfl)

end Model

/-- A Néron model, regarded as a weak Néron model with the same total space and marking: étale
test objects are smooth. -/
abbrev WeakNeronModel.ofNeronModel {j : η ⟶ S} {A : Over η} (M : NeronModel j A) :
    WeakNeronModel j A :=
  M.ofLE fun _ _ _ (_ : Etale _) ↦ inferInstance

namespace NeronModel

variable {j : η ⟶ S} {A B C : Over η} (M : NeronModel j A)

/-- The extension of a morphism `φ : A ⟶ B` to Néron models of `A` and `B`: the unique
`S`-morphism of models whose marked restriction is `φ`. -/
def extendHom (N : NeronModel j B) (φ : A ⟶ B) : M.model ⟶ N.model :=
  N.extend M.model M.smooth (M.genericIso.hom ≫ φ)

/-- The extension of `φ` restricts to `φ` along the markings. -/
@[reassoc (attr := simp)]
theorem map_extendHom (N : NeronModel j B) (φ : A ⟶ B) :
    (Over.pullback j).map (M.extendHom N φ) ≫ N.genericIso.hom = M.genericIso.hom ≫ φ :=
  N.map_extend _ _

/-- A morphism of Néron models is the extension of `φ` if and only if it restricts to `φ` along
the markings. -/
theorem eq_extendHom_iff {N : NeronModel j B} {φ : A ⟶ B} {g : M.model ⟶ N.model} :
    g = M.extendHom N φ ↔
      (Over.pullback j).map g ≫ N.genericIso.hom = M.genericIso.hom ≫ φ :=
  N.eq_extend_iff

/-- Extending a generic morphism and then a morphism `φ : A ⟶ B` to models is the extension of
the composite. -/
@[reassoc (attr := simp)]
theorem extend_comp_extendHom (N : NeronModel j B) {Y : Over S} (hY : Smooth Y.hom)
    (f : (Over.pullback j).obj Y ⟶ A) (φ : A ⟶ B) :
    M.extend Y hY f ≫ M.extendHom N φ = N.extend Y hY (f ≫ φ) :=
  M.extend_comp_extend N hY hY _ f φ

/-- The extension of the identity of `A` is the identity of the model. -/
@[simp]
theorem extendHom_id : M.extendHom M (𝟙 A) = 𝟙 M.model := by
  simp [extendHom]

/-- Extension of morphisms to Néron models is compatible with composition. -/
@[reassoc (attr := simp)]
theorem extendHom_comp (N : NeronModel j B) (P : NeronModel j C) (φ : A ⟶ B) (ψ : B ⟶ C) :
    M.extendHom N φ ≫ N.extendHom P ψ = M.extendHom P (φ ≫ ψ) :=
  M.eq_extendHom_iff.2 (by simp)

/-- The isomorphism of Néron models extending an isomorphism `e : A ≅ B`. -/
def extendIso (N : NeronModel j B) (e : A ≅ B) : M.model ≅ N.model where
  hom := M.extendHom N e.hom
  inv := N.extendHom M e.inv

@[simp]
theorem extendIso_hom (N : NeronModel j B) (e : A ≅ B) :
    (M.extendIso N e).hom = M.extendHom N e.hom :=
  (rfl)

@[simp]
theorem extendIso_inv (N : NeronModel j B) (e : A ≅ B) :
    (M.extendIso N e).inv = N.extendHom M e.inv :=
  (rfl)

instance isIso_extendHom (N : NeronModel j B) (φ : A ⟶ B) [IsIso φ] :
    IsIso (M.extendHom N φ) :=
  (M.extendIso N (asIso φ)).isIso_hom

/-- Uniqueness of marked Néron models: two Néron models of the same `A` are related by exactly
one isomorphism compatible with the markings (Bosch–Lütkebohmert–Raynaud, *Néron Models*,
§1.2, Proposition 2). -/
theorem existsUnique_iso (N : NeronModel j A) :
    ∃! e : M.model ≅ N.model,
      (Over.pullback j).map e.hom ≫ N.genericIso.hom = M.genericIso.hom :=
  ⟨M.extendIso N (Iso.refl A), by simp, fun e he ↦
    Iso.ext (M.eq_extendHom_iff.2 (by simpa using he))⟩

end NeronModel

end TauCeti.AlgebraicGeometry.Neron
