/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
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
conditions (the latter is the condition defining weak Néron models). We therefore state the
property once for an arbitrary class `P` of test morphisms (`MappingProperty P j X`), and obtain
the Néron and weak Néron mapping properties as its instances at `@Smooth` and `@Etale`. Base
change along `j` is Mathlib's functor `CategoryTheory.Over.pullback j : Over S ⥤ Over η`.

## Main definitions

* `TauCeti.AlgebraicGeometry.Neron.MappingProperty P j X`: every `S`-scheme `Y` whose structure
  morphism satisfies `P` has bijective restriction map
  `(Y ⟶ X) → ((Over.pullback j).obj Y ⟶ (Over.pullback j).obj X)`.
* `TauCeti.AlgebraicGeometry.Neron.NeronMappingProperty j X`: the property for smooth test
  objects.
* `TauCeti.AlgebraicGeometry.Neron.WeakNeronMappingProperty j X`: the property for étale test
  objects.

## Main results

* `MappingProperty.existsUnique`, `MappingProperty.hom_ext`: each generic morphism from a test
  object extends uniquely, and two morphisms from a test object agreeing generically are equal.
* `mappingProperty_iff_existsUnique`: the property is unique extension of generic morphisms.
* `mappingProperty_iff_bijective_counit_comp`: the property is bijectivity of precomposition
  with the projection `Y ×_S η ⟶ Y`, viewed in `Over S`.
* `MappingProperty.of_le`: the property for a class of test morphisms implies it for every
  smaller class; in particular `NeronMappingProperty.weakNeronMappingProperty`.
* `MappingProperty.of_iso`: the property is invariant under isomorphism in `Over S`.
* `MappingProperty.of_isTerminal`: the base `S` itself, the Néron model of the trivial
  group, has the property for every `j`.
* `MappingProperty.of_isIso`: when `j` is an isomorphism every object has the property, so
  the predicate carries arithmetic content only for a genuine generic inclusion `j`.

## Implementation notes

The class of test morphisms is a predicate `P : ∀ ⦃X Y : Scheme⦄, (X ⟶ Y) → Prop`, the unfolding
of `MorphismProperty Scheme`, so a `MorphismProperty Scheme` can be passed for it. Classes such as
`@Smooth` and `@Etale` have this unfolded type, and since `MorphismProperty` is a semireducible
definition, `simp` and `rw` could not instantiate a parameter of type `MorphismProperty Scheme`
with them, so general lemmas would not apply to Néron models.

## References

* S. Bosch, W. Lütkebohmert, M. Raynaud, *Néron Models*, Ergebnisse der Mathematik und ihrer
  Grenzgebiete (3) 21, Springer, 1990, §1.2, Definition 1, and §3.5, Definition 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.Neron

universe u

variable {η S : Scheme.{u}}

/-- An object `X` of `Over S` has the *mapping property* relative to `j : η ⟶ S` for the class
`P` of test morphisms when, for every `S`-scheme `Y` whose structure morphism satisfies `P`, base
change along `j` is a bijection from the `S`-morphisms `Y ⟶ X` to the `η`-morphisms between the
base changes of `Y` and `X`. For `P = @Smooth` this is the Néron mapping property of
Bosch–Lütkebohmert–Raynaud, *Néron Models*, §1.2, Definition 1. -/
structure MappingProperty (P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop) (j : η ⟶ S)
    (X : Over S) : Prop where
  /-- Base change along `j` is bijective on morphisms from every test object. -/
  bijective (Y : Over S) (hY : P Y.hom) :
    Function.Bijective ((Over.pullback j).map : (Y ⟶ X) → _)

/-- The *Néron mapping property* relative to `j : η ⟶ S`: base change along `j` is bijective on
`S`-morphisms from every `S`-scheme with smooth structure morphism (Bosch–Lütkebohmert–Raynaud,
*Néron Models*, §1.2, Definition 1). -/
abbrev NeronMappingProperty (j : η ⟶ S) (X : Over S) : Prop :=
  MappingProperty @Smooth j X

/-- The *weak Néron mapping property* relative to `j : η ⟶ S`: base change along `j` is
bijective on `S`-morphisms from every `S`-scheme with étale structure morphism. -/
abbrev WeakNeronMappingProperty (j : η ⟶ S) (X : Over S) : Prop :=
  MappingProperty @Etale j X

namespace MappingProperty

variable {P Q : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop} {j : η ⟶ S} {X : Over S}

/-- Base change along `j` is injective on morphisms from a test object. -/
theorem injective (h : MappingProperty P j X) (Y : Over S) (hY : P Y.hom) :
    Function.Injective ((Over.pullback j).map : (Y ⟶ X) → _) :=
  (h.bijective Y hY).1

/-- Base change along `j` is surjective on morphisms from a test object. -/
theorem surjective (h : MappingProperty P j X) (Y : Over S) (hY : P Y.hom) :
    Function.Surjective ((Over.pullback j).map : (Y ⟶ X) → _) :=
  (h.bijective Y hY).2

/-- Every morphism from the base change of a test object `Y` to the base change of `X` extends
uniquely to an `S`-morphism `Y ⟶ X`. -/
theorem existsUnique (h : MappingProperty P j X) (Y : Over S) (hY : P Y.hom)
    (f : (Over.pullback j).obj Y ⟶ (Over.pullback j).obj X) :
    ∃! g : Y ⟶ X, (Over.pullback j).map g = f :=
  (h.bijective Y hY).existsUnique f

/-- Two `S`-morphisms from a test object into an object with the mapping property are equal as
soon as their base changes along `j` are. -/
theorem hom_ext (h : MappingProperty P j X) {Y : Over S} (hY : P Y.hom) {f g : Y ⟶ X}
    (hfg : (Over.pullback j).map f = (Over.pullback j).map g) : f = g :=
  h.injective Y hY hfg

/-- If `X` is itself a test object with the mapping property, the identity is the only
endomorphism whose base change along `j` is the identity. -/
theorem eq_id_of_map_eq_id (h : MappingProperty P j X) (hX : P X.hom) {f : X ⟶ X}
    (hf : (Over.pullback j).map f = 𝟙 _) : f = 𝟙 X :=
  h.hom_ext hX (by simp [hf])

/-- A single test object whose restriction map is not injective refutes the mapping property. -/
theorem not_of_not_injective (Y : Over S) (hY : P Y.hom)
    (hY' : ¬ Function.Injective ((Over.pullback j).map : (Y ⟶ X) → _)) :
    ¬ MappingProperty P j X :=
  fun h ↦ hY' (h.injective Y hY)

/-- A single test object whose restriction map is not surjective refutes the mapping property. -/
theorem not_of_not_surjective (Y : Over S) (hY : P Y.hom)
    (hY' : ¬ Function.Surjective ((Over.pullback j).map : (Y ⟶ X) → _)) :
    ¬ MappingProperty P j X :=
  fun h ↦ hY' (h.surjective Y hY)

/-- The mapping property for a class `Q` of test morphisms implies the mapping property for
every smaller class `P`. -/
theorem of_le (h : MappingProperty Q j X)
    (hPQ : ∀ ⦃X Y : Scheme.{u}⦄ (f : X ⟶ Y), P f → Q f) : MappingProperty P j X :=
  ⟨fun Y hY ↦ h.bijective Y (hPQ _ hY)⟩

/-- The mapping property is invariant under isomorphism in `Over S`. -/
theorem of_iso (h : MappingProperty P j X) {X' : Over S} (e : X ≅ X') :
    MappingProperty P j X' where
  bijective Y hY := by
    refine ⟨fun f g hfg ↦ (cancel_mono e.inv).1 (h.hom_ext hY ?_), fun f ↦ ?_⟩
    · simp only [Functor.map_comp, hfg]
    · obtain ⟨g, hg⟩ := h.surjective Y hY (f ≫ (Over.pullback j).map e.inv)
      refine ⟨g ≫ e.hom, ?_⟩
      rw [Functor.map_comp, hg, Category.assoc, ← Functor.map_comp]
      simp

/-- Isomorphic objects of `Over S` have the mapping property simultaneously. -/
theorem iff_of_iso {X' : Over S} (e : X ≅ X') :
    MappingProperty P j X ↔ MappingProperty P j X' :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- A terminal object of `Over S`, such as `S` itself, has the mapping property relative to
every `j`: it is the Néron model of the trivial group over `η`. -/
theorem of_isTerminal (hX : IsTerminal X) : MappingProperty P j X where
  bijective Y _ := by
    have hX' : IsTerminal ((Over.pullback j).obj X) := hX.isTerminalObj _ _
    exact ⟨fun f g _ ↦ hX.hom_ext f g, fun f ↦ ⟨hX.from Y, hX'.hom_ext _ _⟩⟩

/-- When `j` is an isomorphism, every object of `Over S` has the mapping property: base change
along `j` is then an equivalence of categories. Thus the predicate has arithmetic content only for
a genuine generic inclusion `j`. -/
theorem of_isIso [IsIso j] (X : Over S) : MappingProperty P j X where
  bijective Y _ := by
    have : (Over.map j).IsEquivalence := (Over.mapIso (asIso j)).isEquivalence_functor
    have := (Over.mapPullbackAdj j).isEquivalence_right_of_isEquivalence_left
    exact ⟨(Over.pullback j).map_injective, (Over.pullback j).map_surjective⟩

end MappingProperty

/-- The mapping property says exactly that every generic morphism from a test object extends
uniquely. -/
theorem mappingProperty_iff_existsUnique {P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop}
    {j : η ⟶ S} {X : Over S} :
    MappingProperty P j X ↔ ∀ (Y : Over S), P Y.hom →
      ∀ f : (Over.pullback j).obj Y ⟶ (Over.pullback j).obj X,
        ∃! g : Y ⟶ X, (Over.pullback j).map g = f :=
  ⟨fun h Y hY f ↦ h.existsUnique Y hY f,
    fun h ↦ ⟨fun Y hY ↦ Function.bijective_iff_existsUnique _ |>.2 (h Y hY)⟩⟩

/-- The mapping property through the adjunction `Over.map j ⊣ Over.pullback j`: `X` has the
property exactly when, for every test object `Y`, precomposition with the counit
`(Over.map j).obj ((Over.pullback j).obj Y) ⟶ Y`, the projection `Y ×_S η ⟶ Y` regarded as an
`S`-morphism, is a bijection onto the `S`-morphisms `Y ×_S η ⟶ X`. -/
theorem mappingProperty_iff_bijective_counit_comp {P : ∀ ⦃X Y : Scheme.{u}⦄, (X ⟶ Y) → Prop}
    {j : η ⟶ S} {X : Over S} :
    MappingProperty P j X ↔ ∀ (Y : Over S), P Y.hom →
      Function.Bijective fun f : Y ⟶ X ↦ (Over.mapPullbackAdj j).counit.app Y ≫ f := by
  -- Precomposition with the counit is base change followed by the adjunction bijection.
  have key (Y : Over S) : (fun f : Y ⟶ X ↦ (Over.mapPullbackAdj j).counit.app Y ≫ f) =
      ((Over.mapPullbackAdj j).homEquiv _ _).symm ∘ (Over.pullback j).map := by
    ext1 f
    rw [Function.comp_apply, Adjunction.homEquiv_counit]
    exact ((Over.mapPullbackAdj j).counit.naturality f).symm
  refine ⟨fun h Y hY ↦ ?_, fun h ↦ ⟨fun Y hY ↦ ?_⟩⟩
  · rw [key]
    exact (Equiv.bijective _).comp (h.bijective Y hY)
  · rw [← (Equiv.bijective ((Over.mapPullbackAdj j).homEquiv _ _).symm).of_comp_iff', ← key]
    exact h Y hY

/-- The Néron mapping property implies the weak Néron mapping property: étale test objects are
smooth. -/
theorem NeronMappingProperty.weakNeronMappingProperty {j : η ⟶ S} {X : Over S}
    (h : NeronMappingProperty j X) : WeakNeronMappingProperty j X :=
  h.of_le fun _ _ _ (_ : Etale _) ↦ inferInstance

end TauCeti.AlgebraicGeometry.Neron
