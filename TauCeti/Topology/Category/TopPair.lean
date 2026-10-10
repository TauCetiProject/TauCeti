/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Category.TopCat.Limits.Products
public import Mathlib.Topology.Category.TopPair

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
time induces a homotopy of maps of pairs `TopPair.ofInclusionHomotopy`.

A map of pairs which is an isomorphism of the ambient spaces and is surjective on the subspaces is
an isomorphism of pairs (`TopPair.isIso_of_isIso_fst_of_surjective_snd`): the inverse on the
subspaces is continuous because subspaces are embedded.

The disjoint union `TopPair.sigma P = (Σ i, Xᵢ, Σ i, Aᵢ)` of a family of pairs `P i = (Xᵢ, Aᵢ)`,
with the inclusions `TopPair.sigmaι P i` of the summands, is the coproduct of the family in
`TopPair` (`TopPair.sigmaCofanIsColimit`).  Relative singular homology is additive along it.

A continuous map into the ambient space of a pair with values in the subspace corestricts to a
continuous map into the subspace, `TopPair.liftSnd`, because the subspace is embedded.
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

lemma ofSubsetMap_fst : Hom.fst (ofSubsetMap g hB) = g := (rfl)

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

/-- A homeomorphism `e : X ≃ₜ Y` carrying `B` onto `B'` induces an isomorphism of pairs
`(X, B) ≅ (Y, B')`. -/
def ofSubsetIso (e : X ≃ₜ Y) (h : ∀ x, x ∈ B ↔ e x ∈ B') : ofSubset B ≅ ofSubset B' where
  hom := ofSubsetMap (TopCat.ofHom e) fun x ↦ (h x).1
  inv := ofSubsetMap (TopCat.ofHom e.symm) fun y hy ↦ (h _).2 (by simpa using hy)
  hom_inv_id := by
    ext a : 2
    · exact Subtype.ext (e.symm_apply_apply a.1)
    · exact e.symm_apply_apply a
  inv_hom_id := by
    ext a : 2
    · exact Subtype.ext (e.apply_symm_apply a.1)
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
    { toFun (p : unitInterval × B) := ⟨F (p.1, p.2), hF p.1 _ p.2.2⟩
      continuous_toFun := by fun_prop
      map_zero_left x := Subtype.ext (F.apply_zero x.1)
      map_one_left x := Subtype.ext (F.apply_one x.1) }

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

section isIso

variable {P Q : TopPair.{u}} (f : P ⟶ Q)

/-- A map of topological pairs which is an isomorphism of the ambient spaces and is surjective
on the subspaces is an isomorphism of pairs.  The inverse on the subspaces is continuous because
the subspace of the source is embedded in its ambient space. -/
lemma isIso_of_isIso_fst_of_surjective_snd [IsIso (Hom.fst f)]
    (hf : Function.Surjective (Hom.snd f)) : IsIso f := by
  let e := TopCat.homeoOfIso (asIso (Hom.fst f))
  let g : Q.snd → P.snd := Function.surjInv hf
  have hg (b : Q.snd) : Hom.snd f (g b) = b := Function.surjInv_eq hf b
  have hmap (b : Q.snd) : P.map (g b) = e.symm (Q.map b) :=
    (e.symm_apply_eq.2 ((congrArg Q.map (hg b)).symm.trans (Hom.w_apply f (g b)))).symm
  have hgc : Continuous g := by
    rw [P.isEmbedding_map.isInducing.continuous_iff, show P.map ∘ g = e.symm ∘ Q.map from
      funext hmap]
    fun_prop
  refine ⟨TopPair.ofHom (inv (Hom.fst f)) (TopCat.ofHom ⟨g, hgc⟩)
    (by ext b; exact hmap b), ?_, ?_⟩
  · ext a : 2
    · refine P.isEmbedding_map.injective ?_
      -- The subspace component of the composite sends `a` to `g (Hom.snd f a)`.
      change P.map (g (Hom.snd f a)) = P.map a
      rw [hmap, Hom.w_apply]
      exact e.symm_apply_apply _
    · exact e.symm_apply_apply a
  · ext b : 2
    · exact hg b
    · exact e.apply_symm_apply b

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

end sigma

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

end TopPair
