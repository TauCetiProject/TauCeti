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
filtration of a CW complex, produces.  A continuous map `t → t'` carrying `s` into `s'` induces a
map of such pairs `TopPair.ofInclusionMap`, and a homotopy that keeps `s` inside `s'` at every
time induces a homotopy of maps of pairs `TopPair.ofInclusionHomotopy`.
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

section ofInclusion

variable {X Y Z : TopCat.{u}} {s t : Set X} {s' t' : Set Y} {s'' t'' : Set Z}
  (hst : s ⊆ t) (hst' : s' ⊆ t') (hst'' : s'' ⊆ t'')

/-- A continuous map `g : t → t'` carrying `s` into `s'` induces a map of pairs
`(t, s) ⟶ (t', s')`. -/
def ofInclusionMap (g : C(t, t')) (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s') :
    ofInclusion hst ⟶ ofInclusion hst' :=
  TopPair.ofHom (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun x ↦ ⟨g ⟨x, hst x.2⟩, hg _ x.2⟩, by fun_prop⟩)

variable {hst hst'}

@[simp]
lemma ofInclusionMap_fst_apply (g : C(t, t')) (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s')
    (x : t) : Hom.fst (ofInclusionMap hst hst' g hg) x = g x := (rfl)

@[simp]
lemma ofInclusionMap_snd_apply (g : C(t, t')) (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s')
    (x : s) : (Hom.snd (ofInclusionMap hst hst' g hg) x).1 = (g ⟨x.1, hst x.2⟩).1 := (rfl)

@[simp]
lemma ofInclusionMap_id :
    ofInclusionMap hst hst (ContinuousMap.id t) (fun _ hx ↦ hx) = 𝟙 (ofInclusion hst) := by
  ext : 2 <;> rfl

@[reassoc]
lemma ofInclusionMap_comp (g : C(t, t')) (g' : C(t', t''))
    (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s')
    (hg' : ∀ x : t', (x : Y) ∈ s' → (g' x : Z) ∈ s'') :
    ofInclusionMap hst hst'' (g'.comp g) (fun x hx ↦ hg' (g x) (hg x hx)) =
      ofInclusionMap hst hst' g hg ≫ ofInclusionMap hst' hst'' g' hg' := by
  ext : 2 <;> rfl

/-- A homotopy between maps `t → t'` which keeps `s` inside `s'` at every time induces a homotopy
between the induced maps of pairs `(t, s) ⟶ (t', s')`. -/
def ofInclusionHomotopy {g₀ g₁ : C(t, t')} (F : g₀.Homotopy g₁)
    (hF : ∀ (τ : unitInterval) (x : t), (x : X) ∈ s → (F (τ, x) : Y) ∈ s') :
    Homotopy (ofInclusionMap hst hst' g₀ fun x hx ↦ F.apply_zero x ▸ hF 0 x hx)
      (ofInclusionMap hst hst' g₁ fun x hx ↦ F.apply_one x ▸ hF 1 x hx) where
  fst := F
  snd :=
    { toFun (p : unitInterval × s) := ⟨F (p.1, ⟨p.2.1, hst p.2.2⟩), hF p.1 _ p.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left x := Subtype.ext (congrArg Subtype.val (F.apply_zero ⟨x.1, hst x.2⟩) :)
      map_one_left x := Subtype.ext (congrArg Subtype.val (F.apply_one ⟨x.1, hst x.2⟩) :) }

end ofInclusion

end TopPair
