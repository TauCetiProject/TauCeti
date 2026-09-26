/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopPair

/-!
# Topological pairs of nested subsets, and maps between pairs of subsets

A continuous map `g : X ⟶ Y` carrying a subset `B ⊆ X` into a subset `B' ⊆ Y` induces a map of
topological pairs `TopPair.ofSubsetMap g hB : (X, B) ⟶ (Y, B')`, where the pairs are
`TopPair.ofSubset B` and `TopPair.ofSubset B'`.

Nested subsets `s ⊆ t` of a topological space form the topological pair
`TopPair.ofInclusion : (t, s)`, whose embedding is `Set.inclusion`.  `TopPair.ofSubset` is the
special case `t = X`; the general form is the one a filtration of a space, such as the skeletal
filtration of a CW complex, produces.
-/

public section

open CategoryTheory

universe u

namespace TopPair

/-- The topological pair `(t, s)` determined by nested subsets `s ⊆ t` of a topological space,
with the inclusion of `s` into `t` as its embedding. -/
abbrev ofInclusion {X : TopCat.{u}} {s t : Set X} (h : s ⊆ t) : TopPair.{u} :=
  TopPair.of (A := TopCat.of s) (X := TopCat.of t)
    (TopCat.ofHom (ContinuousMap.inclusion h)) (Topology.IsEmbedding.inclusion h)

variable {X Y Z : TopCat.{u}} (g : X ⟶ Y) (g' : Y ⟶ Z) {B : Set X} {B' : Set Y} {B'' : Set Z}
  (hB : Set.MapsTo g B B') (hB' : Set.MapsTo g' B' B'')

/-- A continuous map `g : X ⟶ Y` carrying `B` into `B'` induces a map of pairs
`(X, B) ⟶ (Y, B')`. -/
def ofSubsetMap : ofSubset B ⟶ ofSubset B' :=
  TopPair.ofHom g (TopCat.ofHom ⟨hB.restrict, g.hom.continuous.restrict hB⟩)

@[simp]
lemma ofSubsetMap_fst_apply (x : (ofSubset B).fst) : Hom.fst (ofSubsetMap g hB) x = g x := (rfl)

@[simp]
lemma ofSubsetMap_snd_apply (x : (ofSubset B).snd) :
    (Hom.snd (ofSubsetMap g hB) x).1 = g x.1 := (rfl)

@[simp]
lemma ofSubsetMap_id (h : Set.MapsTo (𝟙 X) B B) : ofSubsetMap (𝟙 X) h = 𝟙 (ofSubset B) := by
  ext : 2 <;> rfl

@[reassoc]
lemma ofSubsetMap_comp (h : Set.MapsTo (g ≫ g') B B'') :
    ofSubsetMap (g ≫ g') h = ofSubsetMap g hB ≫ ofSubsetMap g' hB' := by
  ext : 2 <;> rfl

end TopPair
