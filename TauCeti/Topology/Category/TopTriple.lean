/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.Topology.Category.TopPair

/-!
# Triples of topological spaces

A *triple* `(X, A, B)` of topological spaces consists of subspaces `B ⊆ A ⊆ X`, recorded here as
a pair of composable embeddings `B ⟶ A ⟶ X` in `TopCat`.  Triples carry the long exact sequence
of a triple in relative homology, exactly as pairs carry the long exact sequence of a pair; this
file supplies that carrier together with the three pairs `(A, B)`, `(X, B)` and `(X, A)` it
determines and the two maps of pairs relating them.

Like `TopPair`, `TauCeti.TopTriple` is a full subcategory of a category of diagrams in `TopCat`,
so a morphism of triples is a triple of continuous maps commuting with the two embeddings.  All
three pair constructions are therefore functorial, and the two maps of pairs between them are
natural.
-/

@[expose] public section

open CategoryTheory Topology

universe u

namespace TauCeti

/-- A triple of topological spaces `B ⊆ A ⊆ X`, recorded as a pair of composable embeddings
`B ⟶ A ⟶ X` in `TopCat`. -/
abbrev TopTriple : Type _ :=
  ObjectProperty.FullSubcategory (fun F : ComposableArrows TopCat.{u} 2 ↦
    IsEmbedding (F.map' 0 1) ∧ IsEmbedding (F.map' 1 2))

namespace TopTriple

variable (T : TopTriple.{u})

/-- The ambient space `X` of a triple `(X, A, B)`. -/
abbrev fst : TopCat.{u} := T.obj.obj 2

/-- The middle space `A` of a triple `(X, A, B)`. -/
abbrev snd : TopCat.{u} := T.obj.obj 1

/-- The smallest space `B` of a triple `(X, A, B)`. -/
abbrev thd : TopCat.{u} := T.obj.obj 0

/-- The embedding `B ⟶ A` of a triple `(X, A, B)`. -/
abbrev innerMap : T.thd ⟶ T.snd := T.obj.map' 0 1

/-- The embedding `A ⟶ X` of a triple `(X, A, B)`. -/
abbrev outerMap : T.snd ⟶ T.fst := T.obj.map' 1 2

/-- The embedding `B ⟶ X` of a triple `(X, A, B)`. -/
abbrev totalMap : T.thd ⟶ T.fst := T.obj.map' 0 2

@[reassoc, elementwise]
lemma innerMap_comp_outerMap : T.innerMap ≫ T.outerMap = T.totalMap :=
  (T.obj.map'_comp 0 1 2).symm

lemma isEmbedding_innerMap : IsEmbedding T.innerMap := T.property.1

lemma isEmbedding_outerMap : IsEmbedding T.outerMap := T.property.2

lemma isEmbedding_totalMap : IsEmbedding T.totalMap := by
  rw [← T.innerMap_comp_outerMap]
  exact T.property.2.comp T.property.1

/-- Construct a triple of topological spaces from two composable embeddings. -/
abbrev of {B A X : TopCat.{u}} (i : B ⟶ A) (j : A ⟶ X) (hi : IsEmbedding i)
    (hj : IsEmbedding j) : TopTriple.{u} := ⟨.mk₂ i j, hi, hj⟩

section

variable {B A X : TopCat.{u}} (i : B ⟶ A) (j : A ⟶ X) (hi : IsEmbedding i) (hj : IsEmbedding j)

@[simp] lemma of_innerMap : (of i j hi hj).innerMap = i := rfl

@[simp] lemma of_outerMap : (of i j hi hj).outerMap = j := rfl

@[simp] lemma of_totalMap : (of i j hi hj).totalMap = i ≫ j := rfl

end

variable {T} {T' : TopTriple.{u}}

-- The three pair functors are `abbrev`s rather than `def`s so that the two spaces of each pair
-- stay visible to unification; the maps of pairs below are built from identity morphisms whose
-- source and target are the same space of two different pairs.

/-- The pair `(A, B)` of a triple `(X, A, B)`. -/
abbrev innerPair : TopTriple.{u} ⥤ TopPair.{u} where
  obj T := { left := T.thd, right := T.snd, hom := T.innerMap, prop := T.property.1 }
  map φ := TopPair.ofHom (φ.hom.app 1) (φ.hom.app 0) (φ.hom.naturality _).symm

/-- The pair `(X, B)` of a triple `(X, A, B)`. -/
abbrev totalPair : TopTriple.{u} ⥤ TopPair.{u} where
  obj T := { left := T.thd, right := T.fst, hom := T.totalMap, prop := T.isEmbedding_totalMap }
  map φ := TopPair.ofHom (φ.hom.app 2) (φ.hom.app 0) (φ.hom.naturality _).symm

/-- The pair `(X, A)` of a triple `(X, A, B)`. -/
abbrev outerPair : TopTriple.{u} ⥤ TopPair.{u} where
  obj T := { left := T.snd, right := T.fst, hom := T.outerMap, prop := T.property.2 }
  map φ := TopPair.ofHom (φ.hom.app 2) (φ.hom.app 1) (φ.hom.naturality _).symm

@[simp] lemma innerPair_obj_map : (innerPair.obj T).map = T.innerMap := rfl

@[simp] lemma totalPair_obj_map : (totalPair.obj T).map = T.totalMap := rfl

@[simp] lemma outerPair_obj_map : (outerPair.obj T).map = T.outerMap := rfl

@[simp] lemma innerPair_map_fst (φ : T ⟶ T') :
    TopPair.Hom.fst (innerPair.map φ) = φ.hom.app 1 := rfl

@[simp] lemma innerPair_map_snd (φ : T ⟶ T') :
    TopPair.Hom.snd (innerPair.map φ) = φ.hom.app 0 := rfl

@[simp] lemma totalPair_map_fst (φ : T ⟶ T') :
    TopPair.Hom.fst (totalPair.map φ) = φ.hom.app 2 := rfl

@[simp] lemma totalPair_map_snd (φ : T ⟶ T') :
    TopPair.Hom.snd (totalPair.map φ) = φ.hom.app 0 := rfl

@[simp] lemma outerPair_map_fst (φ : T ⟶ T') :
    TopPair.Hom.fst (outerPair.map φ) = φ.hom.app 2 := rfl

@[simp] lemma outerPair_map_snd (φ : T ⟶ T') :
    TopPair.Hom.snd (outerPair.map φ) = φ.hom.app 1 := rfl

/-- The map of pairs `(A, B) ⟶ (X, B)` determined by a triple `(X, A, B)`. -/
def innerToTotal : innerPair.{u} ⟶ totalPair.{u} where
  app T := TopPair.ofHom T.outerMap (𝟙 _)
    ((Category.id_comp _).trans T.innerMap_comp_outerMap.symm)
  naturality _ _ φ := MorphismProperty.Arrow.Hom.ext
    ((Category.comp_id _).trans (Category.id_comp _).symm) (φ.hom.naturality _).symm

/-- The map of pairs `(X, B) ⟶ (X, A)` determined by a triple `(X, A, B)`. -/
def totalToOuter : totalPair.{u} ⟶ outerPair.{u} where
  app T := TopPair.ofHom (𝟙 _) T.innerMap
    (T.innerMap_comp_outerMap.trans (Category.comp_id _).symm)
  naturality _ _ φ := MorphismProperty.Arrow.Hom.ext (φ.hom.naturality _).symm
    ((Category.comp_id _).trans (Category.id_comp _).symm)

@[simp] lemma innerToTotal_app_fst : TopPair.Hom.fst (innerToTotal.app T) = T.outerMap := rfl

@[simp] lemma innerToTotal_app_snd : TopPair.Hom.snd (innerToTotal.app T) = 𝟙 T.thd := rfl

@[simp] lemma totalToOuter_app_fst : TopPair.Hom.fst (totalToOuter.app T) = 𝟙 T.fst := rfl

@[simp] lemma totalToOuter_app_snd : TopPair.Hom.snd (totalToOuter.app T) = T.innerMap := rfl

end TopTriple

end TauCeti
