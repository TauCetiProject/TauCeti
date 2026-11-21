/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Comma.Over.Pullback

/-!
# The Néron mapping property

Let `j : η ⟶ S` be a morphism of schemes. In the arithmetic application `S` is a Dedekind
scheme, for instance the spectrum of a discrete valuation ring, and `j` is the inclusion of its
generic point. An object `X` of `Over S` has the *Néron mapping property* relative to `j` when,
for every `S`-scheme `Y` with smooth structure morphism, base change along `j` induces a bijection
`Hom_S(Y, X) → Hom_η(Y ×_S η, X ×_S η)`.

This is the universal property defining Néron models. The test objects are *all* smooth
`S`-schemes: testing only sections `S ⟶ X`, or only étale `S`-schemes, gives strictly weaker
conditions (the latter is the condition defining weak Néron models). Base change along `j` is
Mathlib's functor `CategoryTheory.Over.pullback j : Over S ⥤ Over η`.

## Main definitions

* `TauCeti.AlgebraicGeometry.Neron.NeronMappingProperty j X`: every smooth `S`-scheme `Y`
  has bijective restriction map `(Y ⟶ X) → ((Over.pullback j).obj Y ⟶ (Over.pullback j).obj X)`.

## Main results

* `NeronMappingProperty.existsUnique`, `NeronMappingProperty.hom_ext`: each generic morphism from a
  smooth test object extends uniquely, and two morphisms from a smooth test object agreeing
  generically are equal.
* `neronMappingProperty_iff_existsUnique`: the property is unique extension of generic morphisms.
* `NeronMappingProperty.of_iso`: the property is invariant under isomorphism in `Over S`.
* `NeronMappingProperty.of_isTerminal`: the base `S` itself, the Néron model of the trivial
  group, has the property for every `j`.
* `NeronMappingProperty.of_isIso`: when `j` is an isomorphism every object has the property, so
  the predicate carries arithmetic content only for a genuine generic inclusion `j`.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 21, Springer, 1990, §1.2, Definition 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Neron

universe u

variable {η S : Scheme.{u}}

/-- An object `X` of `Over S` has the *Néron mapping property* relative to `j : η ⟶ S` when, for
every `S`-scheme `Y` with smooth structure morphism, base change along `j` is a bijection from the
`S`-morphisms `Y ⟶ X` to the `η`-morphisms between the base changes of `Y` and `X`
(Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2, Definition 1). -/
structure NeronMappingProperty (j : η ⟶ S) (X : Over S) : Prop where
  /-- Base change along `j` is bijective on morphisms from every smooth test object. -/
  bijective (Y : Over S) [Smooth Y.hom] :
    Function.Bijective ((Over.pullback j).map : (Y ⟶ X) → _)

namespace NeronMappingProperty

variable {j : η ⟶ S} {X : Over S}

/-- Base change along `j` is injective on morphisms from a smooth test object. -/
theorem injective (h : NeronMappingProperty j X) (Y : Over S) [Smooth Y.hom] :
    Function.Injective ((Over.pullback j).map : (Y ⟶ X) → _) :=
  (h.bijective Y).1

/-- Base change along `j` is surjective on morphisms from a smooth test object. -/
theorem surjective (h : NeronMappingProperty j X) (Y : Over S) [Smooth Y.hom] :
    Function.Surjective ((Over.pullback j).map : (Y ⟶ X) → _) :=
  (h.bijective Y).2

/-- Every morphism from the base change of a smooth test object `Y` to the base change of `X`
extends uniquely to an `S`-morphism `Y ⟶ X`. -/
theorem existsUnique (h : NeronMappingProperty j X) (Y : Over S) [Smooth Y.hom]
    (f : (Over.pullback j).obj Y ⟶ (Over.pullback j).obj X) :
    ∃! g : Y ⟶ X, (Over.pullback j).map g = f :=
  (h.bijective Y).existsUnique f

/-- Two `S`-morphisms from a smooth test object into an object with the Néron mapping property
are equal as soon as their base changes along `j` are. -/
theorem hom_ext (h : NeronMappingProperty j X) {Y : Over S} [Smooth Y.hom] {f g : Y ⟶ X}
    (hfg : (Over.pullback j).map f = (Over.pullback j).map g) : f = g :=
  h.injective Y hfg

/-- For smooth `X` with the Néron mapping property, the identity is the only endomorphism whose
base change along `j` is the identity. -/
theorem eq_id_of_map_eq_id (h : NeronMappingProperty j X) [Smooth X.hom] {f : X ⟶ X}
    (hf : (Over.pullback j).map f = 𝟙 _) : f = 𝟙 X :=
  h.hom_ext (by simp [hf])

/-- A single smooth test object whose restriction map is not injective refutes the Néron mapping
property. -/
theorem not_of_not_injective (Y : Over S) [Smooth Y.hom]
    (hY : ¬ Function.Injective ((Over.pullback j).map : (Y ⟶ X) → _)) :
    ¬ NeronMappingProperty j X :=
  fun h ↦ hY (h.injective Y)

/-- A single smooth test object whose restriction map is not surjective refutes the Néron mapping
property. -/
theorem not_of_not_surjective (Y : Over S) [Smooth Y.hom]
    (hY : ¬ Function.Surjective ((Over.pullback j).map : (Y ⟶ X) → _)) :
    ¬ NeronMappingProperty j X :=
  fun h ↦ hY (h.surjective Y)

/-- The Néron mapping property is invariant under isomorphism in `Over S`. -/
theorem of_iso (h : NeronMappingProperty j X) {X' : Over S} (e : X ≅ X') :
    NeronMappingProperty j X' where
  bijective Y _ := by
    refine ⟨fun f g hfg ↦ (cancel_mono e.inv).1 (h.hom_ext ?_), fun f ↦ ?_⟩
    · simp only [Functor.map_comp, hfg]
    · obtain ⟨g, hg⟩ := h.surjective Y (f ≫ (Over.pullback j).map e.inv)
      refine ⟨g ≫ e.hom, ?_⟩
      rw [Functor.map_comp, hg, Category.assoc, ← Functor.map_comp]
      simp

/-- Isomorphic objects of `Over S` have the Néron mapping property simultaneously. -/
theorem iff_of_iso {X' : Over S} (e : X ≅ X') :
    NeronMappingProperty j X ↔ NeronMappingProperty j X' :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- A terminal object of `Over S`, such as `S` itself, has the Néron mapping property relative to
every `j`: it is the Néron model of the trivial group over `η`. -/
theorem of_isTerminal (hX : IsTerminal X) : NeronMappingProperty j X where
  bijective Y _ := by
    have hX' : IsTerminal ((Over.pullback j).obj X) := hX.isTerminalObj _ _
    exact ⟨fun f g _ ↦ hX.hom_ext f g, fun f ↦ ⟨hX.from Y, hX'.hom_ext _ _⟩⟩

/-- When `j` is an isomorphism, every object of `Over S` has the Néron mapping property: base
change along `j` is then an equivalence of categories. Thus the predicate has arithmetic content
only for a genuine generic inclusion `j`. -/
theorem of_isIso [IsIso j] (X : Over S) : NeronMappingProperty j X where
  bijective Y _ := by
    have : (Over.map j).IsEquivalence := (Over.mapIso (asIso j)).isEquivalence_functor
    have := (Over.mapPullbackAdj j).isEquivalence_right_of_isEquivalence_left
    exact ⟨(Over.pullback j).map_injective, (Over.pullback j).map_surjective⟩

end NeronMappingProperty

/-- The Néron mapping property says exactly that every generic morphism from a smooth test object
extends uniquely. -/
theorem neronMappingProperty_iff_existsUnique {j : η ⟶ S} {X : Over S} :
    NeronMappingProperty j X ↔ ∀ (Y : Over S) [Smooth Y.hom]
      (f : (Over.pullback j).obj Y ⟶ (Over.pullback j).obj X),
      ∃! g : Y ⟶ X, (Over.pullback j).map g = f :=
  ⟨fun h Y _ f ↦ h.existsUnique Y f,
    fun h ↦ ⟨fun Y _ ↦ Function.bijective_iff_existsUnique _ |>.2 (h Y)⟩⟩

end TauCeti.AlgebraicGeometry.Neron
