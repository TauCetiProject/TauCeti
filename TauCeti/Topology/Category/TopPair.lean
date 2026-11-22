/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Products
public import TauCeti.Topology.Category.TopCat.Monoidal
public import Mathlib.Topology.Category.TopPair
public import TauCeti.Topology.Category.TopCat.Fiber

/-!
# Topological pairs of nested subsets, and maps between pairs of subsets

A continuous map `g : X ⟶ Y` carrying a subset `B ⊆ X` into a subset `B' ⊆ Y` induces a map of
topological pairs `TopPair.ofSubsetMap g hB : (X, B) ⟶ (Y, B')`, where the pairs are
`TopPair.ofSubset B` and `TopPair.ofSubset B'`, and a homotopy that keeps `B` inside `B'` at every
time induces a homotopy of maps of pairs `TopPair.ofSubsetHomotopy`.

Nested subsets `s ⊆ t` of a topological space form the topological pair
`TopPair.ofInclusion : (t, s)`, whose embedding is `Set.inclusion`.  `TopPair.ofSubset` is the
special case `t = X`; the general form is the one a filtration of a space, such as the skeletal
filtration of a CW complex, produces.  A continuous map `t → t'` carrying `s` into `s'` induces a
map of such pairs `TopPair.ofInclusionMap`, and a homotopy that keeps `s` inside `s'` at every
time induces a homotopy of maps of pairs `TopPair.ofInclusionHomotopy`.  The pair `(t, s)` is
isomorphic to the pair `TopPair.ofSubset` of `t` and the preimage of `s` in `t`
(`TopPair.ofSubsetPreimageValIso`). When `t` contains every point of `X`, the pair `(t, s)` is the
pair `(X, s)` (`TopPair.ofInclusionIsoOfSubset`).

A map of pairs which is an isomorphism of the ambient spaces and is surjective on the subspaces is
an isomorphism of pairs (`TopPair.isIso_of_isIso_fst_of_surjective_snd`): the inverse on the
subspaces is continuous because subspaces are embedded. Every pair `P = (X, A)` is isomorphic, by
the identity of `X`, to the pair of `X` and the range of its embedding (`TopPair.isoOfSubsetRange`),
and a map of pairs `P ⟶ (Y, B)` factors through this isomorphism as the map of pairs induced by its
ambient map (`TopPair.isoOfSubsetRange_hom_comp_ofSubsetMap`).

The disjoint union `TopPair.sigma P = (Σ i, Xᵢ, Σ i, Aᵢ)` of a family of pairs `P i = (Xᵢ, Aᵢ)`,
with the inclusions `TopPair.sigmaι P i` of the summands, is the coproduct of the family in
`TopPair` (`TopPair.sigmaCofanIsColimit`), and the ambient map out of it induced by maps of pairs
is `ContinuousMap.sigma` of their ambient maps (`TopPair.sigmaCofanIsColimit_desc_fst`).  Relative
singular homology is additive along it.
Maps `Pᵢ ⟶ X` exhibit `X` as such a coproduct when they induce a homeomorphism `Σ i, Xᵢ ≃ X` and
every point of the subspace of `X` comes from a subspace `Aᵢ`
(`TopPair.isColimitCofanOfIsHomeomorph`).

A continuous map into the ambient space of a pair with values in the subspace corestricts to a
continuous map into the subspace, `TopPair.liftSnd`, because the subspace is embedded.

For `S ⊆ T`, the identity of `X` carries `X ∖ T` into `X ∖ S` (`TopCat.mapsTo_id_compl`), so it
is a map of pairs `(X, X ∖ T) ⟶ (X, X ∖ S)`.

The product `TopPair.prodRight P Y = (X × Y, A × Y)` of a pair `P = (X, A)` with a space `Y` has
the embedding `P.map ▷ Y`. For the pair of a subset `A ⊆ X` it is the pair of the preimage of `A`
under the first projection (`TopPair.ofSubsetProdRightIso`).

For pairs `P = (X, A)` and `Q = (Y, B)`, `TopPair.prodSubspace P Q` is the subspace
`A × Y ∪ X × B` of `X × Y`, with the inclusions `TopPair.prodSubspaceInl` of `A × Y` and
`TopPair.prodSubspaceInr` of `X × B`. The inclusions form the excision map of pairs
`TopPair.prodExcisionMap : (A × Y, A × B) ⟶ (A × Y ∪ X × B, X × B)`, and the identity of `X × Y`
is a map of pairs `TopPair.prodLeftToProdSubspace : (X × Y, X × B) ⟶ (X × Y, A × Y ∪ X × B)`.

For subsets `A ⊆ X` and `B ⊆ Y`, the preimages `A × Y` and `X × B` of `A` and `B` under the
projections of `X × Y` form the pair `(X × Y, A × Y ∪ X × B)` of a product of pairs. Each is open
in the union when `A`, respectively `B`, is open
(`TopCat.isOpen_subtypeVal_preimage_preimage_fst_union`), and a product of maps of pairs carries
them, and so their union, into each other (`TopCat.mapsTo_tensorHom_preimage_fst`,
`TopCat.mapsTo_tensorHom_preimage_union`). The pair `(X × Y, X × B)` of `TopPair.prodLeft`
includes into this pair (`TopPair.prodLeftToPreimageUnion`). The product `A × Y` of the subspace
`A` with `Y` is homeomorphic to the preimage of `A` under the first projection
(`TopCat.prodPreimageFstIso`).

For a map `π : X → Y`, a subset `Z ⊆ X` and a subset `S ⊆ Y`, the pair `(π⁻¹ S, π⁻¹ S ∩ Z)` over
`S` includes into `(X, Z)` (`TopCat.restrictPreimagePairMap`), isomorphically when `S` contains
the image of `π` (`TopCat.isIso_restrictPreimagePairMap`). For subsets `U` and `V` of `Y`, the
union and the intersection of the pairs over `U` and over `V` are the pairs over `U ∪ V`
(`TopCat.restrictPreimagePairUnionIso`) and over `U ∩ V` (`TopCat.restrictPreimagePairInterIso`).
For `S ⊆ W`, restricting over `W` and then over `S` is restricting over `S`
(`TopCat.restrictPreimagePairRestrictPreimageIso`).

A map `f` over `B`, that is with `f ≫ p' = p`, induces maps of pairs
`(p⁻¹(T), p⁻¹(S)) ⟶ (p'⁻¹(T), p'⁻¹(S))` for nested subsets `S ⊆ T` of `B`
(`TopCat.Hom.preimagePairMap`), whose components are the restrictions `TopCat.Hom.preimageMap`.
-/

public section

open CategoryTheory

universe u

namespace TopPair

/-- The ambient component of the identity map of a topological pair is the identity. -/
@[simp]
lemma Hom.fst_id (P : TopPair.{u}) : Hom.fst (𝟙 P) = 𝟙 P.fst := (rfl)

/-- The ambient component of a composite map of topological pairs is the composite of the
ambient components. -/
@[simp]
lemma Hom.fst_comp {P Q S : TopPair.{u}} (f : P ⟶ Q) (g : Q ⟶ S) :
    Hom.fst (f ≫ g) = Hom.fst f ≫ Hom.fst g := (rfl)

/-- The topological pair `(t, s)` determined by nested subsets `s ⊆ t` of a topological space,
with the inclusion of `s` into `t` as its embedding. -/
abbrev ofInclusion {X : TopCat.{u}} {s t : Set X} (h : s ⊆ t) : TopPair.{u} :=
  TopPair.of (A := TopCat.of s) (X := TopCat.of t)
    (TopCat.ofHom (ContinuousMap.inclusion h)) (Topology.IsEmbedding.inclusion h)

/-- The pairs of nested subsets `s ⊆ t` and `s' ⊆ t'` agree when the subsets do. -/
lemma ofInclusion_congr {X : TopCat.{u}} {s t s' t' : Set X} (h : s ⊆ t) (h' : s' ⊆ t')
    (hs : s = s') (ht : t = t') : ofInclusion h = ofInclusion h' := by
  subst hs ht
  rfl

/-- The embedding of the pair `(t, s)` of nested subsets has range the preimage of `s` in `t`. -/
lemma range_ofInclusion_map {X : TopCat.{u}} {s t : Set X} (h : s ⊆ t) :
    Set.range (ofInclusion h).map = Subtype.val ⁻¹' s :=
  Set.range_inclusion h

variable {X Y Z : TopCat.{u}} (g : X ⟶ Y) (g' : Y ⟶ Z) {B : Set X} {B' : Set Y} {B'' : Set Z}
  (hB : Set.MapsTo g B B') (hB' : Set.MapsTo g' B' B'')

/-- The embedding of the pair `(X, B)` is `ContinuousMap.subtypeVal B`. -/
lemma ofSubset_map (B : Set X) :
    (ofSubset B).map = TopCat.ofHom (ContinuousMap.subtypeVal B) := by
  ext
  rfl

/-- The embedding of the pair `(X, B)` has range `B`. -/
lemma range_ofSubset_map : Set.range (ofSubset B).map = B :=
  Subtype.range_coe

/-- The ambient space of the pair `(T, B)` is `T`, so it is compact when `T` is. It is stated
for `TopCat.of T`, so that instance search finds it for a concrete space `T`. -/
instance compactSpace_ofSubset_fst {T : Type u} [TopologicalSpace T] [CompactSpace T]
    (A : Set (TopCat.of T)) : CompactSpace (ofSubset A).fst :=
  ‹CompactSpace T›

/-- The embedding of the pair `(X, B)` is an isomorphism when `B` is all of `X`. -/
lemma isIso_ofSubset_map_of_eq_univ (h : B = Set.univ) : IsIso (ofSubset B).map := by
  refine TopCat.isIso_of_bijective_of_isOpenMap _ ⟨Subtype.val_injective, fun y ↦ ?_⟩
    (h ▸ isOpen_univ : IsOpen B).isOpenEmbedding_subtypeVal.isOpenMap
  exact ⟨⟨y, h ▸ Set.mem_univ y⟩, rfl⟩

/-- The subspace of a pair is the range of its embedding, so a map of pairs `f : P ⟶ (X, B)`
sends it into `B`. -/
lemma mapsTo_range_map_of_hom {P : TopPair.{u}} (f : P ⟶ ofSubset B) :
    Set.MapsTo (Hom.fst f) (Set.range P.map) B := by
  rintro _ ⟨s, rfl⟩
  rw [← Hom.w_apply f s]
  exact (Hom.snd f s).property

/-- A continuous map `g : X ⟶ Y` carrying `B` into `B'` induces a map of pairs
`(X, B) ⟶ (Y, B')`. -/
def ofSubsetMap : ofSubset B ⟶ ofSubset B' :=
  TopPair.ofHom g (TopCat.ofHom ⟨hB.restrict, g.hom.continuous.restrict hB⟩)

@[simp]
lemma ofSubsetMap_fst_apply (x : (ofSubset B).fst) : Hom.fst (ofSubsetMap g hB) x = g x := (rfl)

lemma ofSubsetMap_fst : Hom.fst (ofSubsetMap g hB) = g := (rfl)

@[simp]
lemma ofSubsetMap_snd_apply (x : (ofSubset B).snd) :
    (Hom.snd (ofSubsetMap g hB) x).val = g x.val := (rfl)

@[simp]
lemma ofSubsetMap_id (h : Set.MapsTo (𝟙 X) B B) : ofSubsetMap (𝟙 X) h = 𝟙 (ofSubset B) := by
  ext : 2 <;> rfl

@[reassoc]
lemma ofSubsetMap_comp (h : Set.MapsTo (g ≫ g') B B'') :
    ofSubsetMap (g ≫ g') h = ofSubsetMap g hB ≫ ofSubsetMap g' hB' := by
  ext : 2 <;> rfl

variable {g g'} in
/-- Two maps of pairs induced by continuous maps compose to the map induced by any continuous map
equal to their composite. -/
lemma ofSubsetMap_comp_ofSubsetMap_of_comp_eq {g'' : X ⟶ Z} (h : Set.MapsTo g'' B B'')
    (hg : g ≫ g' = g'') : ofSubsetMap g hB ≫ ofSubsetMap g' hB' = ofSubsetMap g'' h := by
  subst hg
  exact (ofSubsetMap_comp _ _ _ _ _).symm

variable {g g'} in
/-- Two composites of maps of pairs induced by continuous maps agree when the composites of the
underlying continuous maps agree. -/
lemma ofSubsetMap_comp_ofSubsetMap_eq {Y' : TopCat.{u}} {S' : Set Y'} {a' : X ⟶ Y'}
    {b' : Y' ⟶ Z} (ha' : Set.MapsTo a' B S') (hb' : Set.MapsTo b' S' B'')
    (h : g ≫ g' = a' ≫ b') :
    ofSubsetMap g hB ≫ ofSubsetMap g' hB' = ofSubsetMap a' ha' ≫ ofSubsetMap b' hb' := by
  rw [ofSubsetMap_comp_ofSubsetMap_of_comp_eq hB hB' (hB'.comp hB) rfl,
    ofSubsetMap_comp_ofSubsetMap_of_comp_eq ha' hb' (hB'.comp hB) h.symm]

/-- A homeomorphism `e : X ≃ₜ Y` carrying `B` onto `B'` induces an isomorphism of pairs
`(X, B) ≅ (Y, B')`. -/
def ofSubsetIso (e : X ≃ₜ Y) (h : ∀ x, x ∈ B ↔ e x ∈ B') : ofSubset B ≅ ofSubset B' where
  hom := ofSubsetMap (TopCat.ofHom e) fun x ↦ (h x).1
  inv := ofSubsetMap (TopCat.ofHom e.symm) fun y hy ↦ (h _).2 (by simpa using hy)
  hom_inv_id := by
    ext a : 2
    · exact Subtype.ext (e.symm_apply_apply a.val)
    · exact e.symm_apply_apply a
  inv_hom_id := by
    ext a : 2
    · exact Subtype.ext (e.apply_symm_apply a.val)
    · exact e.apply_symm_apply a

@[simp]
lemma ofSubsetIso_hom (e : X ≃ₜ Y) (h : ∀ x, x ∈ B ↔ e x ∈ B') :
    (ofSubsetIso e h).hom = ofSubsetMap (TopCat.ofHom e) fun x ↦ (h x).1 := (rfl)

@[simp]
lemma ofSubsetIso_inv (e : X ≃ₜ Y) (h : ∀ x, x ∈ B ↔ e x ∈ B') :
    (ofSubsetIso e h).inv =
      ofSubsetMap (TopCat.ofHom e.symm) fun y hy ↦ (h _).2 (by simpa using hy) := (rfl)

/-- A homotopy between maps `X ⟶ Y` which keeps `B` inside `B'` at every time induces a homotopy
between the induced maps of pairs `(X, B) ⟶ (Y, B')`. -/
def ofSubsetHomotopy {g₀ g₁ : X ⟶ Y} (F : g₀.hom.Homotopy g₁.hom)
    (hF : ∀ (τ : unitInterval) (x : X), x ∈ B → F (τ, x) ∈ B') :
    Homotopy (ofSubsetMap g₀ fun x hx ↦ F.apply_zero x ▸ hF 0 x hx)
      (ofSubsetMap g₁ fun x hx ↦ F.apply_one x ▸ hF 1 x hx) where
  fst := F
  snd :=
    { toFun (p : unitInterval × B) := ⟨F (p.1, p.2), hF p.1 _ p.2.property⟩
      continuous_toFun := by fun_prop
      map_zero_left x := Subtype.ext (F.apply_zero x.val)
      map_one_left x := Subtype.ext (F.apply_one x.val) }

section ofInclusion

variable {X Y Z : TopCat.{u}} {s t : Set X} {s' t' : Set Y} {s'' t'' : Set Z}
  (hst : s ⊆ t) (hst' : s' ⊆ t') (hst'' : s'' ⊆ t'')

/-- A continuous map `g : t → t'` carrying `s` into `s'` induces a map of pairs
`(t, s) ⟶ (t', s')`. -/
def ofInclusionMap (g : C(t, t')) (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s') :
    ofInclusion hst ⟶ ofInclusion hst' :=
  TopPair.ofHom (TopCat.ofHom g)
    (TopCat.ofHom ⟨fun x ↦ ⟨g ⟨x, hst x.property⟩, hg _ x.property⟩, by fun_prop⟩)

variable {hst hst'}

@[simp]
lemma ofInclusionMap_fst_apply (g : C(t, t')) (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s')
    (x : t) : Hom.fst (ofInclusionMap hst hst' g hg) x = g x := (rfl)

/-- The map of ambient spaces of `ofInclusionMap hst hst' g hg` is `g`. -/
lemma ofInclusionMap_fst (g : C(t, t')) (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s') :
    Hom.fst (ofInclusionMap hst hst' g hg) = TopCat.ofHom g := (rfl)

@[simp]
lemma ofInclusionMap_snd_apply (g : C(t, t')) (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s')
    (x : s) : (Hom.snd (ofInclusionMap hst hst' g hg) x).val = (g ⟨x.val, hst x.property⟩).val :=
        (rfl)

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

variable {hst''} in
/-- Two composites `(t, s) ⟶ (t', s') ⟶ (t'', s'')` and `(t, s) ⟶ (t₀, s₀) ⟶ (t'', s'')` of maps
of pairs induced by continuous maps of subspaces agree whenever the composites of the continuous
maps agree. -/
lemma ofInclusionMap_comp_ofInclusionMap_eq {W : TopCat.{u}} {s₀ t₀ : Set W} {hst₀ : s₀ ⊆ t₀}
    (g : C(t, t')) (hg : ∀ x : t, (x : X) ∈ s → (g x : Y) ∈ s')
    (g' : C(t', t'')) (hg' : ∀ x : t', (x : Y) ∈ s' → (g' x : Z) ∈ s'')
    (k : C(t, t₀)) (hk : ∀ x : t, (x : X) ∈ s → (k x : W) ∈ s₀)
    (k' : C(t₀, t'')) (hk' : ∀ x : t₀, (x : W) ∈ s₀ → (k' x : Z) ∈ s'')
    (h : ∀ x, (g' (g x) : Z) = k' (k x)) :
    ofInclusionMap hst hst' g hg ≫ ofInclusionMap hst' hst'' g' hg' =
      ofInclusionMap hst hst₀ k hk ≫ ofInclusionMap hst₀ hst'' k' hk' := by
  rw [← ofInclusionMap_comp, ← ofInclusionMap_comp]
  congr 1
  ext x
  exact h x

/-- A homotopy between maps `t → t'` which keeps `s` inside `s'` at every time induces a homotopy
between the induced maps of pairs `(t, s) ⟶ (t', s')`. -/
def ofInclusionHomotopy {g₀ g₁ : C(t, t')} (F : g₀.Homotopy g₁)
    (hF : ∀ (τ : unitInterval) (x : t), (x : X) ∈ s → (F (τ, x) : Y) ∈ s') :
    Homotopy (ofInclusionMap hst hst' g₀ fun x hx ↦ F.apply_zero x ▸ hF 0 x hx)
      (ofInclusionMap hst hst' g₁ fun x hx ↦ F.apply_one x ▸ hF 1 x hx) where
  fst := F
  snd :=
    { toFun (p : unitInterval × s) := ⟨F (p.1, ⟨p.2.val, hst p.2.property⟩), hF p.1 _ p.2.property⟩
      continuous_toFun := by fun_prop
      map_zero_left x := Subtype.ext (congrArg Subtype.val (F.apply_zero ⟨x.val, hst x.property⟩) :)
      map_one_left x := Subtype.ext (congrArg Subtype.val (F.apply_one ⟨x.val, hst x.property⟩) :) }

variable (hst) in
/-- The pair of `t` and the preimage of `s` in `t` is isomorphic to the pair `(t, s)`: the two
pairs have the same ambient space, and their subspaces are identified by the coercion to `X`. -/
def ofSubsetPreimageValIso :
    ofSubset (X := TopCat.of t) (Subtype.val ⁻¹' s) ≅ ofInclusion hst where
  hom := TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun x ↦ ⟨x.val.val, x.property⟩, by fun_prop⟩)
  inv := TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun x ↦ ⟨⟨x.val, hst x.property⟩, x.property⟩,
      by fun_prop⟩)
  hom_inv_id := by ext : 2 <;> rfl
  inv_hom_id := by ext : 2 <;> rfl

@[simp]
lemma ofSubsetPreimageValIso_hom_fst_apply (x : t) :
    Hom.fst (ofSubsetPreimageValIso hst).hom x = x := (rfl)

lemma ofSubsetPreimageValIso_hom_fst : Hom.fst (ofSubsetPreimageValIso hst).hom = 𝟙 _ := (rfl)

@[simp]
lemma ofSubsetPreimageValIso_hom_snd_apply (x : (Subtype.val ⁻¹' s : Set t)) :
    (Hom.snd (ofSubsetPreimageValIso hst).hom x).val = x.val.val := (rfl)

@[simp]
lemma ofSubsetPreimageValIso_inv_fst_apply (x : t) :
    Hom.fst (ofSubsetPreimageValIso hst).inv x = x := (rfl)

lemma ofSubsetPreimageValIso_inv_fst : Hom.fst (ofSubsetPreimageValIso hst).inv = 𝟙 _ := (rfl)

@[simp]
lemma ofSubsetPreimageValIso_inv_snd_apply (x : s) :
    (Hom.snd (ofSubsetPreimageValIso hst).inv x).val = ⟨x.val, hst x.property⟩ := (rfl)

variable (hst) in
/-- When `t` contains every point of `X`, the pair `(t, s)` is the pair `(X, s')` for any `s'` with
the same points as `s`. -/
def ofInclusionIsoOfSubset (ht : ∀ x, x ∈ t) {s₀ : Set X} (hs : ∀ x, x ∈ s ↔ x ∈ s₀) :
    ofInclusion hst ≅ ofSubset s₀ where
  hom := TopPair.ofHom (TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩)
    (TopCat.ofHom ⟨fun x ↦ ⟨x.val, (hs _).1 x.property⟩, by fun_prop⟩)
  inv := TopPair.ofHom (TopCat.ofHom ⟨fun x ↦ ⟨x, ht x⟩, by fun_prop⟩)
    (TopCat.ofHom ⟨fun x ↦ ⟨x.val, (hs _).2 x.property⟩, by fun_prop⟩)
  hom_inv_id := by ext : 2 <;> rfl
  inv_hom_id := by ext : 2 <;> rfl

@[simp]
lemma ofInclusionIsoOfSubset_hom_fst_apply (ht : ∀ x, x ∈ t) {s₀ : Set X}
    (hs : ∀ x, x ∈ s ↔ x ∈ s₀) (x : t) :
    Hom.fst (ofInclusionIsoOfSubset hst ht hs).hom x = x.val := (rfl)

@[simp]
lemma ofInclusionIsoOfSubset_hom_snd_apply (ht : ∀ x, x ∈ t) {s₀ : Set X}
    (hs : ∀ x, x ∈ s ↔ x ∈ s₀) (x : s) :
    (Hom.snd (ofInclusionIsoOfSubset hst ht hs).hom x).val = x.val := (rfl)

/-- Under `TopPair.ofInclusionIsoOfSubset`, the map of pairs induced by an inclusion `t ⊆ t'` is
the map of pairs induced by the identity of `X`. -/
@[reassoc]
lemma ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom {s₀ s₀' : Set X} {s' t' : Set X}
    {hst' : s' ⊆ t'} (ht : ∀ x, x ∈ t) (ht' : ∀ x, x ∈ t') (hs : ∀ x, x ∈ s ↔ x ∈ s₀)
    (hs' : ∀ x, x ∈ s' ↔ x ∈ s₀') (htt' : t ⊆ t')
    (hss' : ∀ x : t, (x : X) ∈ s → (ContinuousMap.inclusion htt' x : X) ∈ s')
    (h : Set.MapsTo (𝟙 X) s₀ s₀') :
    ofInclusionMap hst hst' (ContinuousMap.inclusion htt') hss' ≫
        (ofInclusionIsoOfSubset hst' ht' hs').hom =
      (ofInclusionIsoOfSubset hst ht hs).hom ≫ ofSubsetMap (𝟙 X) h := by
  ext : 2 <;> rfl

end ofInclusion

section isIso

variable {P Q : TopPair.{u}} (f : P ⟶ Q)

/-- A map of topological pairs is determined by its map of ambient spaces, because the subspace
of the target is embedded. -/
lemma hom_ext_of_fst {g : P ⟶ Q} (h : Hom.fst f = Hom.fst g) : f = g := by
  ext a : 2
  · exact Q.isEmbedding_map.injective (by rw [Hom.w_apply, Hom.w_apply, h])
  · exact ConcreteCategory.congr_hom h a

/-- A map of topological pairs which is an embedding of the ambient spaces is an embedding of the
subspaces, because the subspaces are embedded in the ambient spaces. -/
lemma isEmbedding_snd_of_isEmbedding_fst (h : Topology.IsEmbedding (Hom.fst f)) :
    Topology.IsEmbedding (Hom.snd f) := by
  have hw : ⇑Q.map ∘ ⇑(Hom.snd f) = ⇑(Hom.fst f) ∘ ⇑P.map := funext (Hom.w_apply f)
  rw [← Q.isEmbedding_map.of_comp_iff, hw]
  exact h.comp P.isEmbedding_map

/-- A map of topological pairs which is an isomorphism of the ambient spaces and is surjective
on the subspaces is an isomorphism of pairs.  The inverse on the subspaces is continuous because
the subspace of the source is embedded in its ambient space. -/
lemma isIso_of_isIso_fst_of_surjective_snd [IsIso (Hom.fst f)]
    (hf : Function.Surjective (Hom.snd f)) : IsIso f := by
  let e := TopCat.homeoOfIso (asIso (Hom.fst f))
  let g : Q.snd → P.snd := Function.surjInv hf
  have hmap (b : Q.snd) : P.map (g b) = e.symm (Q.map b) :=
    (e.symm_apply_eq.2 ((congrArg Q.map (Function.surjInv_eq hf b)).symm.trans
      (Hom.w_apply f (g b)))).symm
  have hgc : Continuous g := by
    rw [P.isEmbedding_map.isInducing.continuous_iff, show P.map ∘ g = e.symm ∘ Q.map from
      funext hmap]
    fun_prop
  exact ⟨TopPair.ofHom (inv (Hom.fst f)) (TopCat.ofHom ⟨g, hgc⟩) (by ext b; exact hmap b),
    hom_ext_of_fst _ (IsIso.hom_inv_id _), hom_ext_of_fst _ (IsIso.inv_hom_id _)⟩

/-- A pair `(X, A)` is isomorphic, by the identity of `X`, to the pair of `X` and the range of the
embedding of `A`. -/
noncomputable def isoOfSubsetRange (P : TopPair.{u}) : P ≅ ofSubset (Set.range P.map) where
  hom := TopPair.ofHom (𝟙 P.fst) (TopCat.ofHom ⟨_, P.isEmbedding_map.toHomeomorph.continuous⟩)
    (by ext; rfl)
  inv := TopPair.ofHom (𝟙 P.fst)
    (TopCat.ofHom ⟨_, P.isEmbedding_map.toHomeomorph.symm.continuous⟩)
    (by ext y; exact congrArg Subtype.val (P.isEmbedding_map.toHomeomorph.apply_symm_apply y))
  -- `TopPair.ofHom` and `TopPair.Hom.fst` are abbreviations in Mathlib, so the ambient component
  -- of each composite below is `𝟙 P.fst ≫ 𝟙 P.fst` by unfolding.
  hom_inv_id := hom_ext_of_fst _ (Category.id_comp _)
  inv_hom_id := hom_ext_of_fst _ (Category.id_comp _)

@[simp]
lemma isoOfSubsetRange_hom_fst_apply (P : TopPair.{u}) (x : P.fst) :
    Hom.fst (isoOfSubsetRange P).hom x = x := (rfl)

lemma isoOfSubsetRange_hom_fst (P : TopPair.{u}) : Hom.fst (isoOfSubsetRange P).hom = 𝟙 P.fst :=
  (rfl)

@[simp]
lemma isoOfSubsetRange_hom_snd_apply (P : TopPair.{u}) (x : P.snd) :
    (Hom.snd (isoOfSubsetRange P).hom x).val = P.map x := (rfl)

@[simp]
lemma isoOfSubsetRange_inv_fst_apply (P : TopPair.{u}) (x : P.fst) :
    Hom.fst (isoOfSubsetRange P).inv x = x := (rfl)

lemma isoOfSubsetRange_inv_fst (P : TopPair.{u}) : Hom.fst (isoOfSubsetRange P).inv = 𝟙 P.fst :=
  (rfl)

@[simp]
lemma isoOfSubsetRange_inv_snd_apply (P : TopPair.{u}) (y : (ofSubset (Set.range P.map)).snd) :
    P.map (Hom.snd (isoOfSubsetRange P).inv y) = y.val :=
  congrArg Subtype.val (P.isEmbedding_map.toHomeomorph.apply_symm_apply y)

/-- A map of pairs `f : P ⟶ (X, B)` factors through the isomorphism of `P` with the pair of its
ambient space and the range of its embedding, as the map of pairs induced by its ambient map. -/
lemma isoOfSubsetRange_hom_comp_ofSubsetMap (φ : P ⟶ ofSubset B) :
    (isoOfSubsetRange P).hom ≫ ofSubsetMap (Hom.fst φ) (mapsTo_range_map_of_hom φ) = φ :=
  hom_ext_of_fst _ <| by
    ext x
    rw [Hom.fst_comp, TopCat.comp_app, isoOfSubsetRange_hom_fst_apply]
    -- Not a `rw`: the statement types `Hom.fst φ` as a map into `(ofSubset B).fst`, which is `X`
    -- only after unfolding the abbreviation `TopPair.ofSubset`.
    exact ofSubsetMap_fst_apply _ _ x

end isIso

section sigma

open Limits

variable {ι : Type u}

/-- The disjoint union `∐ᵢ (Xᵢ, Aᵢ) = (Σ i, Xᵢ, Σ i, Aᵢ)` of a family of topological pairs, the
coproduct of the family in `TopPair` (`TopPair.sigmaCofanIsColimit`). -/
abbrev sigma (P : ι → TopPair.{u}) : TopPair.{u} :=
  TopPair.of (A := TopCat.of (Σ i, (P i).snd)) (X := TopCat.of (Σ i, (P i).fst))
    (TopCat.ofHom ⟨Sigma.map id fun i ↦ (P i).map,
      continuous_sigma_map.2 fun i ↦ (P i).map.hom.continuous⟩)
    ((Topology.isEmbedding_sigmaMap Function.injective_id).2 fun i ↦ (P i).isEmbedding_map :
      Topology.IsEmbedding (Sigma.map id fun i ↦ ⇑(P i).map : (Σ i, (P i).snd) → Σ i, (P i).fst))

variable (P : ι → TopPair.{u})

/-- The inclusion `(Xᵢ, Aᵢ) ⟶ ∐ᵢ (Xᵢ, Aᵢ)` of a summand into the disjoint union of a family of
topological pairs. -/
abbrev sigmaι (i : ι) : P i ⟶ sigma P :=
  TopPair.ofHom (TopCat.sigmaι (fun i ↦ (P i).fst) i) (TopCat.sigmaι (fun i ↦ (P i).snd) i)

/-- The cofan of a family of topological pairs given by their disjoint union. -/
abbrev sigmaCofan : Cofan P :=
  Cofan.mk (sigma P) (sigmaι P)

/-- A point of the disjoint union of a family of pairs lies in its subspace exactly when its
component lies in the subspace of its summand. -/
lemma mem_range_sigma_map {x : (sigma P).fst} :
    x ∈ Set.range (sigma P).map ↔ x.2 ∈ Set.range (P x.1).map := by
  constructor
  · rintro ⟨⟨i, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨⟨x.1, a⟩, Sigma.ext rfl (heq_of_eq ha)⟩

/-- The disjoint union of a family of topological pairs is their coproduct in `TopPair`. -/
def sigmaCofanIsColimit : IsColimit (sigmaCofan P) :=
  Cofan.IsColimit.mk _
    (fun s ↦ TopPair.ofHom
      (TopCat.ofHom ⟨fun x ↦ Hom.fst (s.inj x.1) x.2,
        continuous_sigma fun i ↦ (Hom.fst (s.inj i)).hom.continuous⟩)
      (TopCat.ofHom ⟨fun x ↦ Hom.snd (s.inj x.1) x.2,
        continuous_sigma fun i ↦ (Hom.snd (s.inj i)).hom.continuous⟩)
      (by
        ext ⟨i, x⟩
        exact Hom.w_apply (s.inj i) x))
    (fun s i ↦ by ext : 2 <;> rfl)
    (fun s m hm ↦ by
      ext ⟨i, x⟩ : 2
      · exact ConcreteCategory.congr_hom (congrArg Hom.snd (hm i)) x
      · exact ConcreteCategory.congr_hom (congrArg Hom.fst (hm i)) x)

/-- The ambient map out of the disjoint union of a family of pairs induced by maps of pairs
`g i : P i ⟶ Q` is the map `ContinuousMap.sigma` which is `g i` on the summand of `i`. -/
lemma sigmaCofanIsColimit_desc_fst {Q : TopPair.{u}} (g : ∀ i, P i ⟶ Q) :
    Hom.fst (Cofan.IsColimit.desc (sigmaCofanIsColimit P) g) =
      TopCat.ofHom (ContinuousMap.sigma fun i ↦ (Hom.fst (g i)).hom) :=
  (rfl)

lemma sigmaCofanIsColimit_desc_fst_apply {Q : TopPair.{u}} (g : ∀ i, P i ⟶ Q)
    (x : (sigma P).fst) :
    Hom.fst (Cofan.IsColimit.desc (sigmaCofanIsColimit P) g) x = Hom.fst (g x.1) x.2 :=
  (rfl)

variable {P} in
/-- **A recognition principle for coproducts of pairs.** Maps of pairs `f i : Pᵢ ⟶ X` exhibit `X`
as the coproduct of the `Pᵢ` in `TopPair` when the induced map `Σ i, Xᵢ → X` of ambient spaces is
a homeomorphism and every point of the subspace of `X` comes from the subspace of some `Pᵢ`. -/
noncomputable def isColimitCofanOfIsHomeomorph {X : TopPair.{u}} (f : ∀ i, P i ⟶ X)
    (hf : IsHomeomorph fun x : Σ i, (P i).fst ↦ Hom.fst (f x.1) x.2)
    (hsnd : ∀ y : X.snd, ∃ (i : ι) (a : (P i).snd), Hom.fst (f i) ((P i).map a) = X.map y) :
    IsColimit (Cofan.mk X f) :=
  let hσ := sigmaCofanIsColimit P
  let φ := hσ.desc (Cofan.mk X f)
  -- On the summand of `i`, `φ` is `f i`.
  have hφ (x : Σ i, (P i).fst) : Hom.fst φ x = Hom.fst (f x.1) x.2 :=
    ConcreteCategory.congr_hom (congrArg Hom.fst (hσ.fac _ ⟨x.1⟩)) x.2
  have : IsIso (Hom.fst φ) := by
    rw [TopCat.isIso_iff_isHomeomorph, (funext hφ : ⇑(Hom.fst φ) = _)]
    exact hf
  have : IsIso φ := isIso_of_isIso_fst_of_surjective_snd φ fun y ↦ by
    obtain ⟨i, a, ha⟩ := hsnd y
    exact ⟨⟨i, a⟩, X.isEmbedding_map.injective ((Hom.w_apply φ _).trans ((hφ _).trans ha))⟩
  IsColimit.ofIsoColimit hσ (Cofan.ext (asIso φ) fun i ↦ hσ.fac _ ⟨i⟩)

end sigma

section prodLeft

open MonoidalCategory

/-- The product `X × (Y, B) = (X × Y, X × B)` of a topological space `X`, on the left, with a
topological pair `P = (Y, B)`. -/
abbrev prodLeft (P : TopPair.{u}) (X : TopCat.{u}) : TopPair.{u} :=
  TopPair.of (X ◁ P.map) (Topology.IsEmbedding.id.prodMap P.isEmbedding_map)

/-- The map of products `X × (Y, B) ⟶ X' × (Y', B')` induced by a map of spaces `g : X ⟶ X'` and a
map of pairs `f : (Y, B) ⟶ (Y', B')`. -/
abbrev prodLeftMap {P P' : TopPair.{u}} {X X' : TopCat.{u}} (f : P ⟶ P') (g : X ⟶ X') :
    P.prodLeft X ⟶ P'.prodLeft X' :=
  TopPair.ofHom (g ⊗ₘ Hom.fst f) (g ⊗ₘ Hom.snd f) (by
    ext x
    exact Prod.ext rfl (Hom.w_apply f x.2))

/-- The map of ambient spaces underlying `prodLeftMap f g` is the product `g × f` of the maps. -/
@[simp]
lemma prodLeftMap_fst {P P' : TopPair.{u}} {X X' : TopCat.{u}} (f : P ⟶ P') (g : X ⟶ X') :
    Hom.fst (prodLeftMap f g) = g ⊗ₘ Hom.fst f :=
  (rfl)

@[simp]
lemma prodLeftMap_id (P : TopPair.{u}) (X : TopCat.{u}) :
    prodLeftMap (𝟙 P) (𝟙 X) = 𝟙 (P.prodLeft X) :=
  hom_ext_of_fst _ (by ext; rfl)

@[simp]
lemma prodLeftMap_comp {P P' P'' : TopPair.{u}} {X X' X'' : TopCat.{u}} (f : P ⟶ P')
    (f' : P' ⟶ P'') (g : X ⟶ X') (g' : X' ⟶ X'') :
    prodLeftMap (f ≫ f') (g ≫ g') = prodLeftMap f g ≫ prodLeftMap f' g' :=
  hom_ext_of_fst _ (by ext; rfl)

variable {X Y : TopCat.{u}} (A : Set X) (B : Set Y)

/-- The inclusion of pairs `(X × Y, X × B) ⟶ (X × Y, A × Y ∪ X × B)`, with `X × B` the product of
`X` with the subspace `B` and `A × Y ∪ X × B` the union of the preimages of `A` and `B` under the
projections. -/
def prodLeftToPreimageUnion :
    (ofSubset B).prodLeft (ofSubset A).fst ⟶ ofSubset
      (CartesianMonoidalCategory.fst X Y ⁻¹' A ∪ CartesianMonoidalCategory.snd X Y ⁻¹' B) :=
  TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun x ↦ ⟨(x.1, x.2.val), Or.inr x.2.property⟩, by fun_prop⟩)
    (by ext; rfl)

/-- The inclusion `(X × Y, X × B) ⟶ (X × Y, A × Y ∪ X × B)` is the identity of `X × Y`. -/
@[simp]
theorem prodLeftToPreimageUnion_fst :
    Hom.fst (prodLeftToPreimageUnion A B) = 𝟙 (X ⊗ Y) :=
  (rfl)

end prodLeft

section liftSnd

variable (X : TopPair.{u}) {Z : Type*} [TopologicalSpace Z]

/-- A continuous map into the ambient space of a pair that takes values in the subspace, viewed
as a continuous map into the subspace. It is continuous because `X.map` is an embedding. -/
noncomputable def liftSnd (g : C(Z, X.fst)) (hg : ∀ z, g z ∈ Set.range X.map) : C(Z, X.snd) :=
  (X.isEmbedding_map.toHomeomorph.symm : C(Set.range X.map, X.snd)).comp
    ⟨fun z => ⟨g z, hg z⟩, by fun_prop⟩

variable {X}

@[simp]
theorem map_liftSnd (g : C(Z, X.fst)) (hg : ∀ z, g z ∈ Set.range X.map) (z : Z) :
    X.map (X.liftSnd g hg z) = g z :=
  congrArg Subtype.val (X.isEmbedding_map.toHomeomorph.apply_symm_apply ⟨g z, hg z⟩)

theorem liftSnd_apply_eq_iff (g : C(Z, X.fst)) (hg : ∀ z, g z ∈ Set.range X.map) (z : Z)
    (a : X.snd) : X.liftSnd g hg z = a ↔ g z = X.map a := by
  rw [← X.isEmbedding_map.injective.eq_iff, map_liftSnd]

end liftSnd

section prodRight

open MonoidalCategory

/-- The product `(X × Y, A × Y)` of a topological pair `P = (X, A)` with a space `Y`: its
embedding is `P.map ▷ Y`, the product of the embedding of `P` with the identity of `Y`. -/
abbrev prodRight (P : TopPair.{u}) (Y : TopCat.{u}) : TopPair.{u} :=
  TopPair.of (P.map ▷ Y) (P.isEmbedding_map.prodMap Topology.IsEmbedding.id)

/-- For the pair of a subset `A ⊆ X`, the product pair `(X × Y, A × Y)` is the pair of the
preimage of `A` under the first projection of `X × Y`. -/
def ofSubsetProdRightIso {X : TopCat.{u}} (A : Set X) (Y : TopCat.{u}) :
    (ofSubset A).prodRight Y ≅ ofSubset (X := TopCat.of (X × Y)) (Prod.fst ⁻¹' A) where
  hom := TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun x ↦ ⟨(x.1.val, x.2), x.1.property⟩, by fun_prop⟩)
  inv := TopPair.ofHom (𝟙 _) (TopCat.ofHom ⟨fun x ↦ (⟨x.val.1, x.property⟩, x.val.2), by fun_prop⟩)
  hom_inv_id := by ext : 2 <;> rfl
  inv_hom_id := by ext : 2 <;> rfl

@[simp]
lemma ofSubsetProdRightIso_hom_fst_apply {X : TopCat.{u}} (A : Set X) (Y : TopCat.{u})
    (x : X × Y) : Hom.fst (ofSubsetProdRightIso A Y).hom x = x := (rfl)

@[simp]
lemma ofSubsetProdRightIso_inv_fst_apply {X : TopCat.{u}} (A : Set X) (Y : TopCat.{u})
    (x : X × Y) : Hom.fst (ofSubsetProdRightIso A Y).inv x = x := (rfl)

end prodRight

section prodSubspace

open MonoidalCategory Topology

variable (P Q : TopPair.{u})

/-- The subspace `A × Y ∪ X × B` of the product `X × Y` of the ambient spaces of two pairs
`P = (X, A)` and `Q = (Y, B)`: the union of the preimages of `A` and of `B` under the two
projections. -/
abbrev prodSubspace : Set ↑(P.fst ⊗ Q.fst : TopCat.{u}) :=
  CartesianMonoidalCategory.fst P.fst Q.fst ⁻¹' Set.range P.map ∪
    CartesianMonoidalCategory.snd P.fst Q.fst ⁻¹' Set.range Q.map

/-- The inclusion `A × Y ⟶ A × Y ∪ X × B`. -/
def prodSubspaceInl : P.snd ⊗ Q.fst ⟶ TopCat.of (P.prodSubspace Q) :=
  TopCat.ofHom ⟨fun x ↦ ⟨(P.map x.1, x.2), Or.inl ⟨x.1, rfl⟩⟩, by fun_prop⟩

/-- The inclusion `X × B ⟶ A × Y ∪ X × B`. -/
def prodSubspaceInr : P.fst ⊗ Q.snd ⟶ TopCat.of (P.prodSubspace Q) :=
  TopCat.ofHom ⟨fun x ↦ ⟨(x.1, Q.map x.2), Or.inr ⟨x.2, rfl⟩⟩, by fun_prop⟩

@[simp]
theorem coe_prodSubspaceInl_apply (x : ↑(P.snd ⊗ Q.fst : TopCat.{u})) :
    (P.prodSubspaceInl Q x : ↑(P.fst ⊗ Q.fst : TopCat.{u})) = (P.map x.1, x.2) :=
  (rfl)

@[simp]
theorem coe_prodSubspaceInr_apply (x : ↑(P.fst ⊗ Q.snd : TopCat.{u})) :
    (P.prodSubspaceInr Q x : ↑(P.fst ⊗ Q.fst : TopCat.{u})) = (x.1, Q.map x.2) :=
  (rfl)

/-- The inclusion of `A × Y` into `A × Y ∪ X × B`, followed by the inclusion into `X × Y`, is the
product of the inclusion `A ⟶ X` with `Y`. -/
@[reassoc]
lemma prodSubspaceInl_comp_map :
    P.prodSubspaceInl Q ≫ (ofSubset (P.prodSubspace Q)).map = P.map ▷ Q.fst := by
  ext; rfl

/-- The inclusion of `X × B` into `A × Y ∪ X × B`, followed by the inclusion into `X × Y`, is the
product of `X` with the inclusion `B ⟶ Y`. -/
@[reassoc]
lemma prodSubspaceInr_comp_map :
    P.prodSubspaceInr Q ≫ (ofSubset (P.prodSubspace Q)).map = P.fst ◁ Q.map := by
  ext; rfl

theorem isEmbedding_prodSubspaceInl : IsEmbedding (P.prodSubspaceInl Q) :=
  IsEmbedding.subtypeVal.of_comp_iff.1 (P.isEmbedding_map.prodMap (IsEmbedding.id (X := Q.fst)))

theorem isEmbedding_prodSubspaceInr : IsEmbedding (P.prodSubspaceInr Q) :=
  IsEmbedding.subtypeVal.of_comp_iff.1 ((IsEmbedding.id (X := P.fst)).prodMap Q.isEmbedding_map)

/-- The pair `(A × Y ∪ X × B, X × B)`, the target of the excision map of the product pair. -/
abbrev prodExcisionPair : TopPair.{u} :=
  TopPair.of (P.prodSubspaceInr Q) (P.isEmbedding_prodSubspaceInr Q)

/-- The **excision map** `(A × Y, A × B) ⟶ (A × Y ∪ X × B, X × B)` of the product pair, given by
the inclusions. -/
def prodExcisionMap : Q.prodLeft P.snd ⟶ P.prodExcisionPair Q :=
  TopPair.ofHom (P.prodSubspaceInl Q) (P.map ▷ Q.snd) (by ext; rfl)

lemma prodExcisionMap_fst : Hom.fst (P.prodExcisionMap Q) = P.prodSubspaceInl Q := (rfl)

@[simp]
lemma prodExcisionMap_fst_apply (x : ↑(P.snd ⊗ Q.fst : TopCat.{u})) :
    Hom.fst (P.prodExcisionMap Q) x = P.prodSubspaceInl Q x := (rfl)

lemma prodExcisionMap_snd : Hom.snd (P.prodExcisionMap Q) = P.map ▷ Q.snd := (rfl)

@[simp]
lemma prodExcisionMap_snd_apply (x : ↑(P.snd ⊗ Q.snd : TopCat.{u})) :
    Hom.snd (P.prodExcisionMap Q) x = (P.map x.1, x.2) := (rfl)

/-- The map of pairs `(X × Y, X × B) ⟶ (X × Y, A × Y ∪ X × B)` given by the identity of `X × Y`. -/
def prodLeftToProdSubspace : Q.prodLeft P.fst ⟶ ofSubset (P.prodSubspace Q) :=
  TopPair.ofHom (𝟙 _) (P.prodSubspaceInr Q) (by ext; rfl)

lemma prodLeftToProdSubspace_fst : Hom.fst (P.prodLeftToProdSubspace Q) = 𝟙 _ := (rfl)

@[simp]
lemma prodLeftToProdSubspace_fst_apply (x : ↑(P.fst ⊗ Q.fst : TopCat.{u})) :
    Hom.fst (P.prodLeftToProdSubspace Q) x = x := (rfl)

lemma prodLeftToProdSubspace_snd : Hom.snd (P.prodLeftToProdSubspace Q) = P.prodSubspaceInr Q :=
  (rfl)

@[simp]
lemma prodLeftToProdSubspace_snd_apply (x : ↑(P.fst ⊗ Q.snd : TopCat.{u})) :
    Hom.snd (P.prodLeftToProdSubspace Q) x = P.prodSubspaceInr Q x := (rfl)

/-- The map of pairs `(A × Y ∪ X × B, X × B) ⟶ (X × Y, X × B)` given by the inclusion. -/
def prodExcisionPairToProdLeft : P.prodExcisionPair Q ⟶ Q.prodLeft P.fst :=
  TopPair.ofHom (ofSubset (P.prodSubspace Q)).map (𝟙 _) (by ext; rfl)

lemma prodExcisionPairToProdLeft_fst :
    Hom.fst (P.prodExcisionPairToProdLeft Q) = (ofSubset (P.prodSubspace Q)).map := (rfl)

@[simp]
lemma prodExcisionPairToProdLeft_fst_apply (x : P.prodSubspace Q) :
    Hom.fst (P.prodExcisionPairToProdLeft Q) x = x.val := (rfl)

lemma prodExcisionPairToProdLeft_snd : Hom.snd (P.prodExcisionPairToProdLeft Q) = 𝟙 _ := (rfl)

@[simp]
lemma prodExcisionPairToProdLeft_snd_apply (x : ↑(P.fst ⊗ Q.snd : TopCat.{u})) :
    Hom.snd (P.prodExcisionPairToProdLeft Q) x = x := (rfl)

/-- The excision map followed by the inclusion is the inclusion of pairs
`(A × Y, A × B) ⟶ (X × Y, X × B)`. -/
@[reassoc]
theorem prodExcisionMap_comp_prodExcisionPairToProdLeft :
    P.prodExcisionMap Q ≫ P.prodExcisionPairToProdLeft Q = prodLeftMap (𝟙 Q) P.map :=
  hom_ext_of_fst _ (by ext; rfl)

end prodSubspace

end TopPair

namespace IsCompact

/-- The complement of the subspace of the pair `(X, X \ A)` is compact when `A` is. -/
lemma compl_range_ofSubset_compl_map {X : TopCat.{u}} {A : Set X} (hA : IsCompact A) :
    IsCompact (Set.range (TopPair.ofSubset Aᶜ).map)ᶜ := by
  rw [TopPair.range_ofSubset_map]
  exact (compl_compl A).symm ▸ hA

end IsCompact

namespace TopCat

open MonoidalCategory CartesianMonoidalCategory

/-- For `S ⊆ T`, the identity of `X` carries `X ∖ T` into `X ∖ S`. -/
lemma mapsTo_id_compl {X : TopCat.{u}} {S T : Set X} (h : S ⊆ T) : Set.MapsTo (𝟙 X) Tᶜ Sᶜ :=
  fun _ hx hS ↦ hx (h hS)

section Preimage

variable {X Y X' Y' : TopCat.{u}} {A : Set X} {B : Set Y}

/-- The preimage of an open subset `A` of `X` under the first projection of `X × Y` is open in its
union with the preimage of any subset `B` of `Y` under the second projection. -/
lemma isOpen_subtypeVal_preimage_preimage_fst_union (hA : IsOpen A) :
    IsOpen ((↑) ⁻¹' (fst X Y ⁻¹' A) : Set ↥(fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)) :=
  (hA.preimage (fst X Y).hom.continuous).preimage continuous_subtypeVal

/-- The preimage of an open subset `B` of `Y` under the second projection of `X × Y` is open in its
union with the preimage of any subset `A` of `X` under the first projection. -/
lemma isOpen_subtypeVal_preimage_preimage_snd_union (hB : IsOpen B) :
    IsOpen ((↑) ⁻¹' (snd X Y ⁻¹' B) : Set ↥(fst X Y ⁻¹' A ∪ snd X Y ⁻¹' B)) :=
  (hB.preimage (snd X Y).hom.continuous).preimage continuous_subtypeVal

variable (X Y A) in
/-- The homeomorphism `A × Y ≅ fst⁻¹(A)` between the product of the subspace `A ⊆ X` with `Y`
and the preimage of `A` under the first projection `X × Y ⟶ X`. -/
noncomputable def prodPreimageFstIso :
    (TopPair.ofSubset A).snd ⊗ Y ≅ (TopPair.ofSubset (fst X Y ⁻¹' A)).snd where
  hom := ofHom ⟨fun x ↦ ⟨((TopPair.ofSubset A).map ⊗ₘ 𝟙 Y) x, (fst
      (TopPair.ofSubset A).snd Y x).property⟩,
    ((TopPair.ofSubset A).map ⊗ₘ 𝟙 Y).hom.continuous.subtype_mk _⟩
  inv := lift (ofHom ⟨fun x ↦ ⟨fst X Y x.val, x.property⟩, by fun_prop⟩)
    ((TopPair.ofSubset (fst X Y ⁻¹' A)).map ≫ snd X Y)

variable (X Y A) in
/-- Followed by the inclusion of `fst⁻¹(A)` into `X × Y`, the homeomorphism `A × Y ≅ fst⁻¹(A)` is
the product of the inclusion of `A` with the identity of `Y`. -/
@[reassoc]
lemma prodPreimageFstIso_hom_comp_map :
    (prodPreimageFstIso X Y A).hom ≫ (TopPair.ofSubset (fst X Y ⁻¹' A)).map =
      (TopPair.ofSubset A).map ▷ Y :=
  (rfl)

variable (X Y A) in
/-- Followed by the product of the inclusion of `A` with the identity of `Y`, the inverse of the
homeomorphism `A × Y ≅ fst⁻¹(A)` is the inclusion of `fst⁻¹(A)` into `X × Y`. -/
@[reassoc]
lemma prodPreimageFstIso_inv_comp_whiskerRight :
    (prodPreimageFstIso X Y A).inv ≫ (TopPair.ofSubset A).map ▷ Y =
      (TopPair.ofSubset (fst X Y ⁻¹' A)).map :=
  (Iso.inv_comp_eq _).2 (prodPreimageFstIso_hom_comp_map X Y A).symm

variable (X Y A) in
/-- The homeomorphism `A × Y ≅ fst⁻¹(A)` followed by the first projection of the pair
`(X × Y, fst⁻¹(A)) ⟶ (X, A)` is the first projection of `A × Y`. -/
@[reassoc]
lemma prodPreimageFstIso_hom_comp_ofSubsetMap_fst_snd :
    (prodPreimageFstIso X Y A).hom ≫
        TopPair.Hom.snd (TopPair.ofSubsetMap (fst X Y) (Set.mapsTo_preimage _ _) :
          TopPair.ofSubset (fst X Y ⁻¹' A) ⟶ TopPair.ofSubset A) =
      fst (TopPair.ofSubset A).snd Y :=
  (rfl)

variable (X Y A) in
/-- The homeomorphism `A × Y ≅ fst⁻¹(A)` followed by the inclusion into `X × Y` and the second
projection is the second projection of `A × Y`. -/
@[reassoc]
lemma prodPreimageFstIso_hom_comp_map_snd :
    (prodPreimageFstIso X Y A).hom ≫ (TopPair.ofSubset (fst X Y ⁻¹' A)).map ≫
        (snd X Y : (TopPair.ofSubset (fst X Y ⁻¹' A)).fst ⟶ Y) =
      snd (TopPair.ofSubset A).snd Y :=
  (rfl)

end Preimage

section RestrictPreimage

variable {X : TopCat.{u}} {Y : Type*} (π : X → Y) (Z : Set X)

/-- The inclusion `(π⁻¹ S, π⁻¹ S ∩ Z) ⟶ (X, Z)` of the restriction of the pair `(X, Z)` over a
subset `S` of the base of a map `π : X → Y`. -/
def restrictPreimagePairMap (S : Set Y) :
    TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S) ⟶ TopPair.ofSubset Z :=
  TopPair.ofHom (ofHom (ContinuousMap.subtypeVal _)) (ofHom ⟨fun x ↦ ⟨x.val, x.property.2⟩,
      by fun_prop⟩)
    (by ext; rfl)

@[simp]
lemma restrictPreimagePairMap_fst_apply (S : Set Y) (x : ↥(π ⁻¹' S)) :
    TopPair.Hom.fst (restrictPreimagePairMap π Z S) x = x.val :=
  (rfl)

lemma restrictPreimagePairMap_fst (S : Set Y) :
    TopPair.Hom.fst (restrictPreimagePairMap π Z S) = ofHom (ContinuousMap.subtypeVal _) :=
  (rfl)

@[simp]
lemma restrictPreimagePairMap_snd_apply (S : Set Y) (x : ↥(π ⁻¹' S ∩ Z)) :
    TopPair.Hom.snd (restrictPreimagePairMap π Z S) x = ⟨x.val, x.property.2⟩ :=
  (rfl)

/-- For `S ⊆ T`, the inclusion of the pair over `S` into the pair over `T`, followed by the
inclusion of the pair over `T` into `(X, Z)`, is the inclusion of the pair over `S`. -/
@[reassoc (attr := simp)]
lemma ofInclusionMap_inclusion_comp_restrictPreimagePairMap {S T : Set Y} (h : S ⊆ T) :
    TopPair.ofInclusionMap (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S)
        Set.inter_subset_left (ContinuousMap.inclusion (Set.preimage_mono h))
        (fun _ hx ↦ ⟨h hx.1, hx.2⟩) ≫ restrictPreimagePairMap π Z T =
      restrictPreimagePairMap π Z S :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)

/-- Over a set `S` containing the image of `π`, the pair over `S` is `(X, Z)`. -/
lemma isIso_restrictPreimagePairMap {S : Set Y} (hS : ∀ x, π x ∈ S) :
    IsIso (restrictPreimagePairMap π Z S) := by
  have : IsIso (TopPair.Hom.fst (restrictPreimagePairMap π Z S)) := by
    have he : TopPair.Hom.fst (restrictPreimagePairMap π Z S) = (isoOfHomeo (X := of ↥(π ⁻¹' S))
        (Y := X) ((Homeomorph.setCongr (Set.eq_univ_of_forall hS)).trans
          (Homeomorph.Set.univ X))).hom :=
      TopCat.ext fun _ ↦ rfl
    rw [he]
    exact Iso.isIso_hom _
  exact TopPair.isIso_of_isIso_fst_of_surjective_snd _ fun z ↦ ⟨⟨z.val, hS z.val, z.property⟩, rfl⟩

/-- For subsets `U` and `V` of the base, the union `(π⁻¹ U ∪ π⁻¹ V, π⁻¹ U ∩ Z ∪ π⁻¹ V ∩ Z)` of
the pairs over `U` and over `V` is the pair over `U ∪ V`. -/
def restrictPreimagePairUnionIso (U V : Set Y) :
    TopPair.ofInclusion (Set.union_subset_union
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V)) ≅
      TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' (U ∪ V) ∩ Z ⊆ π ⁻¹' (U ∪ V)) where
  hom := TopPair.ofHom (ofHom (ContinuousMap.inclusion fun _ h ↦ h))
    (ofHom (ContinuousMap.inclusion fun _ h ↦
      h.elim (fun h ↦ ⟨Or.inl h.1, h.2⟩) fun h ↦ ⟨Or.inr h.1, h.2⟩)) (by ext; rfl)
  inv := TopPair.ofHom (ofHom (ContinuousMap.inclusion fun _ h ↦ h))
    (ofHom (ContinuousMap.inclusion fun _ h ↦
      h.1.elim (fun h' ↦ Or.inl ⟨h', h.2⟩) fun h' ↦ Or.inr ⟨h', h.2⟩)) (by ext; rfl)
  hom_inv_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)
  inv_hom_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)

@[simp]
lemma restrictPreimagePairUnionIso_hom_fst_apply (U V : Set Y) (x : ↥(π ⁻¹' U ∪ π ⁻¹' V)) :
    (TopPair.Hom.fst (restrictPreimagePairUnionIso π Z U V).hom x).val = x.val :=
  (rfl)

@[simp]
lemma restrictPreimagePairUnionIso_inv_fst_apply (U V : Set Y) (x : ↥(π ⁻¹' (U ∪ V))) :
    (TopPair.Hom.fst (restrictPreimagePairUnionIso π Z U V).inv x).val = x.val :=
  (rfl)

lemma restrictPreimagePairUnionIso_hom_fst (U V : Set Y) :
    TopPair.Hom.fst (restrictPreimagePairUnionIso π Z U V).hom =
      ofHom (ContinuousMap.inclusion fun _ h ↦ h) :=
  (rfl)

lemma restrictPreimagePairUnionIso_inv_fst (U V : Set Y) :
    TopPair.Hom.fst (restrictPreimagePairUnionIso π Z U V).inv =
      ofHom (ContinuousMap.inclusion fun _ h ↦ h) :=
  (rfl)

/-- For subsets `U` and `V` of the base, the intersection
`(π⁻¹ U ∩ π⁻¹ V, (π⁻¹ U ∩ Z) ∩ (π⁻¹ V ∩ Z))` of the pairs over `U` and over `V` is the pair over
`U ∩ V`. -/
def restrictPreimagePairInterIso (U V : Set Y) :
    TopPair.ofInclusion (Set.inter_subset_inter
      (Set.inter_subset_left : π ⁻¹' U ∩ Z ⊆ π ⁻¹' U)
      (Set.inter_subset_left : π ⁻¹' V ∩ Z ⊆ π ⁻¹' V)) ≅
      TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' (U ∩ V) ∩ Z ⊆ π ⁻¹' (U ∩ V)) where
  hom := TopPair.ofHom (ofHom (ContinuousMap.inclusion fun _ h ↦ h))
    (ofHom (ContinuousMap.inclusion fun _ h ↦ ⟨⟨h.1.1, h.2.1⟩, h.1.2⟩)) (by ext; rfl)
  inv := TopPair.ofHom (ofHom (ContinuousMap.inclusion fun _ h ↦ h))
    (ofHom (ContinuousMap.inclusion fun _ h ↦ ⟨⟨h.1.1, h.2⟩, h.1.2, h.2⟩)) (by ext; rfl)
  hom_inv_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)
  inv_hom_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)

@[simp]
lemma restrictPreimagePairInterIso_hom_fst_apply (U V : Set Y) (x : ↥(π ⁻¹' U ∩ π ⁻¹' V)) :
    (TopPair.Hom.fst (restrictPreimagePairInterIso π Z U V).hom x).val = x.val :=
  (rfl)

@[simp]
lemma restrictPreimagePairInterIso_inv_fst_apply (U V : Set Y) (x : ↥(π ⁻¹' (U ∩ V))) :
    (TopPair.Hom.fst (restrictPreimagePairInterIso π Z U V).inv x).val = x.val :=
  (rfl)

lemma restrictPreimagePairInterIso_hom_fst (U V : Set Y) :
    TopPair.Hom.fst (restrictPreimagePairInterIso π Z U V).hom =
      ofHom (ContinuousMap.inclusion fun _ h ↦ h) :=
  (rfl)

lemma restrictPreimagePairInterIso_inv_fst (U V : Set Y) :
    TopPair.Hom.fst (restrictPreimagePairInterIso π Z U V).inv =
      ofHom (ContinuousMap.inclusion fun _ h ↦ h) :=
  (rfl)

variable {S W : Set Y}

/-- For `S ⊆ W`, restricting the pair `(X, Z)` over `W` along `π`, and then the resulting pair over
the preimage of `S` in `W` along the restriction `π⁻¹ W → W` of `π`, is restricting `(X, Z)` over
`S`. -/
def restrictPreimagePairRestrictPreimageIso (hSW : S ⊆ W) :
    TopPair.ofInclusion (X := of ↥(π ⁻¹' W)) (Set.inter_subset_left :
      W.restrictPreimage π ⁻¹' ((↑) ⁻¹' S) ∩ ((↑) ⁻¹' (π ⁻¹' W ∩ Z)) ⊆
        W.restrictPreimage π ⁻¹' ((↑) ⁻¹' S)) ≅
      TopPair.ofInclusion (Set.inter_subset_left : π ⁻¹' S ∩ Z ⊆ π ⁻¹' S) where
  hom := TopPair.ofHom (ofHom ⟨fun x ↦ ⟨x.val.val, x.property⟩, by fun_prop⟩)
    (ofHom ⟨fun x ↦ ⟨x.val.val, x.property.1, x.property.2.2⟩, by fun_prop⟩) (by ext; rfl)
  inv := TopPair.ofHom (ofHom ⟨fun x ↦ ⟨⟨x.val, hSW x.property⟩, x.property⟩, by fun_prop⟩)
    (ofHom ⟨fun x ↦ ⟨⟨x.val, hSW x.property.1⟩, x.property.1, hSW x.property.1, x.property.2⟩,
        by fun_prop⟩) (by ext; rfl)
  hom_inv_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)
  inv_hom_id := TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)

@[simp]
lemma restrictPreimagePairRestrictPreimageIso_hom_fst_apply (hSW : S ⊆ W)
    (x : ↥(W.restrictPreimage π ⁻¹' (((↑) : W → Y) ⁻¹' S))) :
    (TopPair.Hom.fst (restrictPreimagePairRestrictPreimageIso π Z hSW).hom x).val = x.val.val :=
  (rfl)

@[simp]
lemma restrictPreimagePairRestrictPreimageIso_inv_fst_apply (hSW : S ⊆ W) (x : ↥(π ⁻¹' S)) :
    ((TopPair.Hom.fst (restrictPreimagePairRestrictPreimageIso π Z hSW).inv x).val).val = x.val :=
  (rfl)

lemma restrictPreimagePairRestrictPreimageIso_hom_fst (hSW : S ⊆ W) :
    TopPair.Hom.fst (restrictPreimagePairRestrictPreimageIso π Z hSW).hom =
      ofHom ⟨fun x ↦ ⟨x.val.val, x.property⟩, by fun_prop⟩ :=
  (rfl)

lemma restrictPreimagePairRestrictPreimageIso_inv_fst (hSW : S ⊆ W) :
    TopPair.Hom.fst (restrictPreimagePairRestrictPreimageIso π Z hSW).inv =
      ofHom ⟨fun x ↦ ⟨⟨x.val, hSW x.property⟩, x.property⟩, by fun_prop⟩ :=
  (rfl)

end RestrictPreimage

end TopCat

namespace TopCat.Hom

variable {E E' B : TopCat.{u}} {p : E ⟶ B} {p' : E' ⟶ B}

/-- The map of pairs `(p⁻¹(T), p⁻¹(S)) ⟶ (p'⁻¹(T), p'⁻¹(S))` induced by a map `f` over `B`, that is
with `f ≫ p' = p`, for nested subsets `S ⊆ T` of `B`. -/
def preimagePairMap (f : E ⟶ E') (hf : f ≫ p' = p) {S T : Set B} (hST : S ⊆ T) :
    TopPair.ofInclusion (X := E) (Set.preimage_mono (f := p) hST) ⟶
      TopPair.ofInclusion (X := E') (Set.preimage_mono (f := p') hST) :=
  TopPair.ofHom (f.preimageMap hf T) (f.preimageMap hf S) (by
    ext x
    -- Both sides send a point `x` of `p⁻¹(S)` to `f x`.
    exact Subtype.ext ((f.coe_preimageMap_apply hf S x).trans
      (f.coe_preimageMap_apply hf T (Set.inclusion (Set.preimage_mono hST) x)).symm))

@[simp]
lemma preimagePairMap_fst (f : E ⟶ E') (hf : f ≫ p' = p) {S T : Set B} (hST : S ⊆ T) :
    TopPair.Hom.fst (preimagePairMap f hf hST) = f.preimageMap hf T :=
  (rfl)

@[simp]
lemma preimagePairMap_snd (f : E ⟶ E') (hf : f ≫ p' = p) {S T : Set B} (hST : S ⊆ T) :
    TopPair.Hom.snd (preimagePairMap f hf hST) = f.preimageMap hf S :=
  (rfl)

@[simp]
lemma preimagePairMap_id (hf : 𝟙 E ≫ p = p) {S T : Set B} (hST : S ⊆ T) :
    preimagePairMap (𝟙 E) hf hST = 𝟙 _ :=
  TopPair.hom_ext_of_fst _ (preimageMap_id hf T)

/-- The maps of pairs induced by maps over `B` compose. It is stated in this direction so that
`simp` can use it: the middle map `p'` cannot be recovered from the composite. -/
@[reassoc (attr := simp)]
lemma preimagePairMap_comp_preimagePairMap {E'' : TopCat.{u}} {p'' : E'' ⟶ B} (f : E ⟶ E')
    (f' : E' ⟶ E'') (hf : f ≫ p' = p) (hf' : f' ≫ p'' = p') {S T : Set B} (hST : S ⊆ T) :
    preimagePairMap f hf hST ≫ preimagePairMap f' hf' hST =
      preimagePairMap (f ≫ f') (by rw [Category.assoc, hf', hf]) hST :=
  TopPair.hom_ext_of_fst _ (preimageMap_comp_preimageMap f f' hf hf' T)

end TopCat.Hom
