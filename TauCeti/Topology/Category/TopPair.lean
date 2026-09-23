/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopPair

/-!
# Maps of topological pairs of the form `(X, B) ⟶ (Y, B')`

A continuous map `g : X ⟶ Y` carrying a subset `B ⊆ X` into a subset `B' ⊆ Y` induces a map of
topological pairs `TopPair.ofSubsetMap g hB : (X, B) ⟶ (Y, B')`, where the pairs are
`TopPair.ofSubset B` and `TopPair.ofSubset B'`.  This file defines that map and records how it acts
on points and how it respects identities and composition.
-/

public section

open CategoryTheory

universe u

namespace TopPair

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
