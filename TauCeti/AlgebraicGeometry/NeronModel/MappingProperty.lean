/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The Néron mapping property

For a morphism of schemes `j : η ⟶ S` and an object `X` of `Over S`, the predicate
`NeronMappingProperty j X` says that for every `Y` in `Over S` with smooth structure morphism,
restriction along `j`,

`Hom_S(Y, X) → Hom_η(Y ×_S η, X ×_S η)`, `f ↦ (Over.pullback j).map f`,

is bijective (Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2, Definition 1, p. 12).
The test objects are all smooth `S`-schemes, not only sections of `S` or étale `S`-schemes.
For `j = 𝟙 S` every object has the property (`NeronMappingProperty.of_id`). The intended classical
application is `j` the inclusion of the generic point of a Dedekind base, where the property
characterizes Néron models.

## Main declarations

* `TauCeti.AlgebraicGeometry.NeronMappingProperty`: the Néron mapping property.
* `NeronMappingProperty.iff_existsUnique`: the property as unique extension of every generic
  morphism from a smooth test object.
* `NeronMappingProperty.hom_ext`: two morphisms from a smooth test object with equal generic
  restrictions are equal.
* `NeronMappingProperty.of_iso`: transport along an isomorphism in `Over S`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

variable {η S : Scheme.{u}} (j : η ⟶ S)

/-- The Néron mapping property of `X` in `Over S` relative to `j : η ⟶ S`: for every `Y` in
`Over S` whose structure morphism is smooth, restriction of `S`-morphisms `Y ⟶ X` along `j` is
a bijection onto the `η`-morphisms between the pullbacks along `j`
(Bosch–Lütkebohmert–Raynaud, §1.2, Definition 1). -/
def NeronMappingProperty (X : Over S) : Prop :=
  ∀ Y : Over S, Smooth Y.hom →
    Function.Bijective (fun f : Y ⟶ X ↦ (Over.pullback j).map f)

/-- Unfolding lemma for `NeronMappingProperty`. -/
theorem neronMappingProperty_iff (X : Over S) :
    NeronMappingProperty j X ↔ ∀ Y : Over S, Smooth Y.hom →
      Function.Bijective (fun f : Y ⟶ X ↦ (Over.pullback j).map f) :=
  Iff.rfl

namespace NeronMappingProperty

variable {j} {X : Over S}

/-- Restriction along `j` from a smooth test object is bijective. -/
theorem bijective (h : NeronMappingProperty j X) (Y : Over S) [hY : Smooth Y.hom] :
    Function.Bijective (fun f : Y ⟶ X ↦ (Over.pullback j).map f) :=
  h Y hY

/-- Restriction along `j` from a smooth test object is injective. -/
theorem injective (h : NeronMappingProperty j X) (Y : Over S) [Smooth Y.hom] :
    Function.Injective (fun f : Y ⟶ X ↦ (Over.pullback j).map f) :=
  (h.bijective Y).1

/-- Restriction along `j` from a smooth test object is surjective. -/
theorem surjective (h : NeronMappingProperty j X) (Y : Over S) [Smooth Y.hom] :
    Function.Surjective (fun f : Y ⟶ X ↦ (Over.pullback j).map f) :=
  (h.bijective Y).2

/-- Every generic morphism from a smooth test object has exactly one extension. -/
theorem existsUnique (h : NeronMappingProperty j X) {Y : Over S} [Smooth Y.hom]
    (f : (Over.pullback j).obj Y ⟶ (Over.pullback j).obj X) :
    ∃! g : Y ⟶ X, (Over.pullback j).map g = f :=
  (h.bijective Y).existsUnique f

/-- Two morphisms from a smooth test object with equal restrictions along `j` are equal. -/
theorem hom_ext (h : NeronMappingProperty j X) {Y : Over S} [Smooth Y.hom] {f g : Y ⟶ X}
    (hfg : (Over.pullback j).map f = (Over.pullback j).map g) : f = g :=
  h.injective Y hfg

/-- The Néron mapping property is unique extension of every generic morphism from every smooth
test object. -/
theorem iff_existsUnique :
    NeronMappingProperty j X ↔ ∀ Y : Over S, Smooth Y.hom →
      ∀ f : (Over.pullback j).obj Y ⟶ (Over.pullback j).obj X,
        ∃! g : Y ⟶ X, (Over.pullback j).map g = f :=
  forall₂_congr fun _ _ ↦ Function.bijective_iff_existsUnique _

/-- The Néron mapping property is invariant under isomorphism in `Over S`. -/
theorem of_iso {X' : Over S} (e : X ≅ X') (h : NeronMappingProperty j X) :
    NeronMappingProperty j X' := by
  intro Y hY
  have : (fun f : Y ⟶ X' ↦ (Over.pullback j).map f) =
      (fun g ↦ g ≫ ((Over.pullback j).mapIso e).hom) ∘
        (fun f : Y ⟶ X ↦ (Over.pullback j).map f) ∘ (fun f ↦ f ≫ e.inv) := by
    ext f : 1
    simp [← Functor.map_comp]
  rw [this]
  exact ((Iso.homCongr (Iso.refl _) ((Over.pullback j).mapIso e)).bijective.comp
    (h Y hY)).comp (Iso.homCongr (Iso.refl Y) e.symm).bijective

/-- For a smooth `X` with the Néron mapping property, an endomorphism of `X` whose restriction
along `j` is the identity is the identity. -/
theorem eq_id_of_map_eq_id (h : NeronMappingProperty j X) [Smooth X.hom] {f : X ⟶ X}
    (hf : (Over.pullback j).map f = 𝟙 _) : f = 𝟙 X :=
  h.hom_ext (hf.trans ((Over.pullback j).map_id X).symm)

/-- A single smooth test object whose restriction map is not injective refutes the Néron
mapping property. -/
theorem not_of_restriction_not_injective (Y : Over S) [Smooth Y.hom]
    (hY : ¬ Function.Injective (fun f : Y ⟶ X ↦ (Over.pullback j).map f)) :
    ¬ NeronMappingProperty j X :=
  fun h ↦ hY (h.injective Y)

/-- A single smooth test object whose restriction map is not surjective refutes the Néron
mapping property. -/
theorem not_of_restriction_not_surjective (Y : Over S) [Smooth Y.hom]
    (hY : ¬ Function.Surjective (fun f : Y ⟶ X ↦ (Over.pullback j).map f)) :
    ¬ NeronMappingProperty j X :=
  fun h ↦ hY (h.surjective Y)

/-- Relative to the identity of `S`, every object of `Over S` has the Néron mapping property:
relative to the identity the predicate carries no arithmetic content. -/
theorem of_id (X : Over S) : NeronMappingProperty (𝟙 S) X :=
  fun Y _ ↦ ((Functor.FullyFaithful.id _).ofIso Over.pullbackId.symm).map_bijective Y X

end NeronMappingProperty

end TauCeti.AlgebraicGeometry
