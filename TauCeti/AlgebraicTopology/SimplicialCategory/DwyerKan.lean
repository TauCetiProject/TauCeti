/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialCategory.HomotopyCategory
public import TauCeti.AlgebraicTopology.SimplicialSet.RealizationPiZero

/-!
# Dwyer–Kan equivalences of simplicially enriched categories

An enriched functor `F : EnrichedFunctor SSet C D` between categories enriched over simplicial
sets is a *Dwyer–Kan equivalence* when every map of mapping simplicial sets
`(X ⟶[SSet] Y) ⟶ (F.obj X ⟶[SSet] F.obj Y)` is a weak equivalence (in the Kan–Quillen sense,
`SSet.modelCategoryQuillen`) and the induced functor of homotopy categories
`F.mapHomotopyCategory` is essentially surjective. These are the weak
equivalences of the Bergner model structure on simplicial categories, and the categorical
equivalences of simplicial sets are the maps whose rigidifications are Dwyer–Kan equivalences.

Since weak equivalences of simplicial sets are bijective on connected components
(`SSet.bijective_mapπ₀_of_weakEquivalence`), a Dwyer–Kan equivalence induces an equivalence of
homotopy categories (`CategoryTheory.EnrichedFunctor.IsDwyerKanEquivalence.isEquivalence`).
Identities and composites of Dwyer–Kan equivalences are Dwyer–Kan equivalences, and if `G` and
the composite of `F` and `G` are Dwyer–Kan equivalences then so is `F`.

## Main definitions

* `CategoryTheory.EnrichedFunctor.IsDwyerKanEquivalence`: Dwyer–Kan equivalences.

## Main results

* `CategoryTheory.EnrichedFunctor.IsDwyerKanEquivalence.isEquivalence`: a Dwyer–Kan equivalence
  induces an equivalence of homotopy categories.
* `CategoryTheory.EnrichedFunctor.IsDwyerKanEquivalence.id`,
  `CategoryTheory.EnrichedFunctor.IsDwyerKanEquivalence.comp` and
  `CategoryTheory.EnrichedFunctor.IsDwyerKanEquivalence.of_comp`: identities, composition and
  cancellation of a Dwyer–Kan equivalence applied second.

## References

* W. G. Dwyer and D. M. Kan, *Function complexes in homotopical algebra*, Topology 19 (1980).
* J. E. Bergner, *A model category structure on the category of simplicial categories*,
  Trans. Amer. Math. Soc. 359 (2007), the weak equivalences of Theorem 1.1.
* J. Lurie, *Higher Topos Theory*, Definition 1.1.4.4 and Definition 1.1.5.14.
-/

public section

open CategoryTheory HomotopicalAlgebra Opposite Simplicial TauCeti SimplicialHomotopyCategory

open scoped SSet.modelCategoryQuillen

universe v u u' u''

namespace CategoryTheory.EnrichedFunctor

variable {C : Type u} {D : Type u'} {E : Type u''} [EnrichedCategory SSet.{v} C]
  [EnrichedCategory SSet.{v} D] [EnrichedCategory SSet.{v} E]

/-- A functor of simplicially enriched categories is a *Dwyer–Kan equivalence* when it is a weak
equivalence on every mapping simplicial set and essentially surjective on homotopy categories. -/
class IsDwyerKanEquivalence (F : EnrichedFunctor SSet.{v} C D) : Prop where
  /-- Every map of mapping simplicial sets is a weak equivalence. -/
  weakEquivalence_map (X Y : C) : WeakEquivalence (F.map X Y)
  /-- The induced functor of homotopy categories is essentially surjective. -/
  essSurj : F.mapHomotopyCategory.EssSurj

attribute [instance] IsDwyerKanEquivalence.weakEquivalence_map IsDwyerKanEquivalence.essSurj

variable (F : EnrichedFunctor SSet.{v} C D)

namespace IsDwyerKanEquivalence

section

variable [F.IsDwyerKanEquivalence]

/-- A Dwyer–Kan equivalence is faithful on homotopy categories. -/
instance faithful : F.mapHomotopyCategory.Faithful :=
  F.faithful_mapHomotopyCategory fun _ _ ↦ (SSet.bijective_mapπ₀_of_weakEquivalence _).1

/-- A Dwyer–Kan equivalence is full on homotopy categories. -/
instance full : F.mapHomotopyCategory.Full :=
  F.full_mapHomotopyCategory fun _ _ ↦ (SSet.bijective_mapπ₀_of_weakEquivalence _).2

/-- A Dwyer–Kan equivalence induces an equivalence of homotopy categories. -/
instance isEquivalence : F.mapHomotopyCategory.IsEquivalence where

end

/-- The identity is a Dwyer–Kan equivalence. -/
instance id : (EnrichedFunctor.id SSet.{v} C).IsDwyerKanEquivalence where
  weakEquivalence_map _ _ := (weakEquivalence_iff _).2 ((weakEquivalences SSet).id_mem _)
  essSurj := Functor.essSurj_of_iso (mapHomotopyCategoryId (C := C)).symm

variable (G : EnrichedFunctor SSet.{v} D E)

/-- A composite of Dwyer–Kan equivalences is a Dwyer–Kan equivalence. -/
instance comp [F.IsDwyerKanEquivalence] [G.IsDwyerKanEquivalence] :
    (EnrichedFunctor.comp SSet.{v} F G).IsDwyerKanEquivalence where
  weakEquivalence_map X Y := inferInstanceAs (WeakEquivalence (F.map X Y ≫ G.map _ _))
  essSurj := Functor.essSurj_of_iso (mapHomotopyCategoryComp F G).symm

/-- If `G` and the composite of `F` and `G` are Dwyer–Kan equivalences, then so is `F`. -/
lemma of_comp [G.IsDwyerKanEquivalence]
    [(EnrichedFunctor.comp SSet.{v} F G).IsDwyerKanEquivalence] : F.IsDwyerKanEquivalence where
  weakEquivalence_map X Y :=
    have : WeakEquivalence (F.map X Y ≫ G.map _ _) :=
      inferInstanceAs (WeakEquivalence ((EnrichedFunctor.comp SSet.{v} F G).map X Y))
    weakEquivalence_of_postcomp _ (G.map _ _)
  essSurj :=
    have := Functor.essSurj_of_iso (mapHomotopyCategoryComp F G)
    Functor.essSurj_of_comp_fully_faithful F.mapHomotopyCategory G.mapHomotopyCategory

end IsDwyerKanEquivalence

end CategoryTheory.EnrichedFunctor
