/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.AlgebraicTopology.Singular.Triple
public import TauCeti.Topology.VectorBundle.Attachment
import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Attaching finitely many disc bundles

Let `E a → B a` be finitely many real vector bundles whose fibre norms are continuous on the
total spaces, with unit disc bundles `D(E a)` and unit sphere bundles `S(E a)`. Say that a space
`Z` is obtained from a closed subset `X` by attaching the `D(E a)` along the `S(E a)` through maps
of pairs `f a : (D(E a), S(E a)) ⟶ (Z, X)` when each `f a` is a closed embedding sending a point
into `X` only if it lies in `S(E a)`, two of the images meet only inside `X`, and `X` together with
the images is all of `Z`. Then the maps `f a` exhibit the relative homology `Hₙ(Z, X)` as the
coproduct of the relative homologies `Hₙ(D(E a), S(E a))`, with coefficients in any abelian
category with coproducts, in every degree
(`TauCeti.isColimitCofanSingularHomologyOfAttachDiscBundles`).

For a single bundle this is `TauCeti.isIso_singularHomologyMap_of_attach_discBundle`. Several
bundles occur together when a critical level of a Morse–Bott function carries several critical
submanifolds, of possibly different dimensions and indices: crossing the level attaches the
negative disc bundle of each of them, and the relative homology across the level is the sum of
the contributions of the critical submanifolds. The bundles may have different model fibres,
whereas a Mathlib `FiberBundle F E` has a single model fibre `F`, so the theorem for one bundle
does not apply to them at once.

## The proof

For a finite set `s` of indices write `Zₛ` for `X` together with the images of the `D(E a)`,
`a ∈ s`. Each `Zₛ` is closed, and for `c ∈ s` it is obtained from the closed subset
`Z_{s ∖ {c}}` by attaching `D(E c)` alone, so `f c` induces an isomorphism
`Hₙ(D(E c), S(E c)) ≅ Hₙ(Zₛ, Z_{s ∖ {c}})` by the theorem for one bundle. Composing its inverse
with the map `Hₙ(Z, X) ⟶ Hₙ(Z, Z_{ι ∖ {c}})` gives a projection
`π c : Hₙ(Z, X) ⟶ Hₙ(D(E c), S(E c))`. The maps induced by the `f a` and the `π c` satisfy the
biproduct relations: `f a ≫ π a` is the identity, and `f a ≫ π c` vanishes for `a ≠ c`, since
`f a` lands in the subspace `Z_{ι ∖ {c}}` of the pair `(Z, Z_{ι ∖ {c}})`. It remains to see that
the `π c` are jointly monomorphic, which is proved for every `Zₛ` by induction on `s`: a morphism
into `Hₙ(Z_{s ∪ {a}}, X)` killed by the map to `Hₙ(Z_{s ∪ {a}}, Zₛ)` comes, up to an epimorphism,
from `Hₙ(Zₛ, X)` by the long exact sequence of the triple `(Z_{s ∪ {a}}, Zₛ, X)`, and the maps
`Hₙ(Zₛ, Z_{s ∖ {c}}) ⟶ Hₙ(Z_{s ∪ {a}}, Z_{(s ∪ {a}) ∖ {c}})` are isomorphisms, both sides being
`Hₙ(D(E c), S(E c))`.

## Main results

* `TauCeti.isColimitCofanSingularHomologyOfAttachDiscBundles`: attaching finitely many disc bundles
  along their sphere bundles, `Hₙ(Z, X)` is the coproduct of the `Hₙ(D(E a), S(E a))`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.1, Proposition 2.22 (good pairs and excision) and the long exact sequence of a triple.
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261, the
  attachment of the negative disc bundles of the critical submanifolds on one level.
-/

public section

noncomputable section

open Bundle (TotalSpace)
open CategoryTheory Limits Set Topology

universe w v u

namespace TauCeti

variable {ι : Type*} {B : ι → Type w} {F : ι → Type*} {E : ∀ a, B a → Type w}
  [∀ a b, NormedAddCommGroup (E a b)] [∀ a, TopologicalSpace (TotalSpace (F a) (E a))]
  {Z : TopCat.{w}} {X : Set Z} (f : ∀ a, discSpherePair (F a) (E a) ⟶ TopPair.ofSubset X)

/-! ### The partial unions -/

/-- `X` together with the images of the discs `D(E a)` for `a ∈ s`. -/
private def attachUnion (s : Finset ι) : Set Z :=
  X ∪ ⋃ a ∈ s, range (TopPair.Hom.fst (f a))

private lemma subset_attachUnion (s : Finset ι) : X ⊆ attachUnion f s :=
  subset_union_left

private lemma attachUnion_mono {s t : Finset ι} (h : s ⊆ t) : attachUnion f s ⊆ attachUnion f t :=
  union_subset_union_right _ (biUnion_subset_biUnion_left (Finset.coe_subset.2 h))

private lemma range_subset_attachUnion {s : Finset ι} {a : ι} (ha : a ∈ s) :
    range (TopPair.Hom.fst (f a)) ⊆ attachUnion (Z := Z) f s :=
  fun _ hx ↦ Or.inr (mem_biUnion (Finset.mem_coe.2 ha) hx)

private lemma attachUnion_empty : attachUnion f ∅ = X := by
  simp [attachUnion]

private lemma attachUnion_insert [DecidableEq ι] (s : Finset ι) (a : ι) :
    attachUnion f (insert a s) = attachUnion f s ∪ range (TopPair.Hom.fst (f a)) := by
  rw [attachUnion, attachUnion, Finset.set_biUnion_insert, union_left_comm]
  exact union_comm _ _

private lemma isClosed_attachUnion (hX : IsClosed X)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a))) (s : Finset ι) :
    IsClosed (attachUnion f s) :=
  hX.union (isClosed_biUnion_finset fun a _ ↦ (hf a).isClosed_range)

/-- A point of the disc `D(E c)` lands in the union of `X` with the other discs only if it lies
in the sphere `S(E c)`. -/
private lemma mem_sphereBundle_of_mem_attachUnion_erase [DecidableEq ι]
    (hfX : ∀ a (v : discBundle (F a) (E a)),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ sphereBundle (F a) (E a))
    (hinter : Pairwise fun a b ↦
      range (TopPair.Hom.fst (f a)) ∩ range (TopPair.Hom.fst (f b)) ⊆ X)
    {s : Finset ι} {c : ι} {v : discBundle (F c) (E c)}
    (hv : TopPair.Hom.fst (f c) v ∈ attachUnion (Z := Z) f (s.erase c)) :
    (v : TotalSpace (F c) (E c)) ∈ sphereBundle (F c) (E c) := by
  refine hfX c v (hv.elim id fun hv ↦ ?_)
  obtain ⟨b, hb, hvb⟩ := mem_iUnion₂.1 hv
  exact hinter (Finset.ne_of_mem_erase hb) ⟨hvb, v, rfl⟩

/-! ### The maps of pairs -/

/-- The disc `D(E c)` as a map of pairs `(D(E c), S(E c)) ⟶ (T, A)`, for `X ⊆ A ⊆ T` with `T`
containing the image of `f c`. -/
private abbrev discMap (c : ι) {A T : Set Z} (hAT : A ⊆ T) (hXA : X ⊆ A)
    (hT : range (TopPair.Hom.fst (f c)) ⊆ T) :
    discSpherePair (F c) (E c) ⟶ TopPair.ofInclusion hAT :=
  TopPair.ofInclusionMap _ hAT
    (⟨fun v ↦ ⟨TopPair.Hom.fst (f c) v, hT ⟨v, rfl⟩⟩,
      (TopPair.Hom.fst (f c)).hom.continuous.subtype_mk _⟩ : C(discBundle (F c) (E c), T))
    fun v hv ↦ hXA (mem_of_eq_of_mem (TopPair.Hom.w_apply (f c) ⟨v.1, hv⟩).symm
      (TopPair.Hom.snd (f c) ⟨v.1, hv⟩).2)

/-- Following the disc `D(E c)` by a map of pairs which fixes the points of `Z` gives the disc
again. -/
private lemma discMap_comp_ofInclusionMap (c : ι) {A T A' T' : Set Z} (hAT : A ⊆ T)
    (hA'T' : A' ⊆ T') (hXA : X ⊆ A) (hXA' : X ⊆ A') (hT : range (TopPair.Hom.fst (f c)) ⊆ T)
    (hT' : range (TopPair.Hom.fst (f c)) ⊆ T') (g : C(T, T'))
    (hg : ∀ x : T, (x : Z) ∈ A → (g x : Z) ∈ A') (hgx : ∀ x, (g x : Z) = x) :
    discMap f c hAT hXA hT ≫ TopPair.ofInclusionMap hAT hA'T' g hg =
      discMap f c hA'T' hXA' hT' := by
  rw [← TopPair.ofInclusionMap_comp]
  congr 1
  exact ContinuousMap.ext fun _ ↦ Subtype.ext (hgx _)

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)

/-- The identity of `T` as a map of pairs `(T, X) ⟶ (T, A)`, for `X ⊆ A ⊆ T`. This is the map of
pairs of the triple `(T, A, X)` (`TauCeti.TopTriple.totalToOuter_app_ofInclusions`). -/
private abbrev quotMap {A T : Set Z} (hXA : X ⊆ A) (hAT : A ⊆ T) :
    TopPair.ofInclusion (hXA.trans hAT) ⟶ TopPair.ofInclusion hAT :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.id _) fun _ hx ↦ by simpa using hXA hx

/-- The disc of `a` lands in `A`, so it induces zero into `Hₙ(T, A)`. -/
private lemma singularHomologyMap_discMap_comp_quotMap_eq_zero (a : ι) {A T : Set Z}
    (hXA : X ⊆ A) (hAT : A ⊆ T) (hT : range (TopPair.Hom.fst (f a)) ⊆ T)
    (hA : range (TopPair.Hom.fst (f a)) ⊆ A) :
    TopPair.singularHomologyMap (discMap f a (hXA.trans hAT) subset_rfl hT) R n ≫
      TopPair.singularHomologyMap (quotMap hXA hAT) R n = 0 := by
  rw [← TopPair.singularHomologyMap_comp]
  refine TopPair.singularHomologyMap_eq_zero_of_fac _ R
    (TopCat.ofHom (⟨fun v ↦ ⟨TopPair.Hom.fst (f a) v, hA ⟨v, rfl⟩⟩,
      (TopPair.Hom.fst (f a)).hom.continuous.subtype_mk _⟩ : C(discBundle (F a) (E a), A))) ?_ n
  rw [← TopPair.ofInclusionMap_comp, TopPair.ofInclusionMap_fst]
  exact TopCat.ext fun _ ↦ rfl

variable [∀ a, TopologicalSpace (B a)] [∀ a, NormedAddCommGroup (F a)] [∀ a, NormedSpace ℝ (F a)]
  [∀ a b, NormedSpace ℝ (E a b)] [∀ a, FiberBundle (F a) (E a)] [∀ a, VectorBundle ℝ (F a) (E a)]

/-- **Attaching one of the discs.** If `T` is obtained from its closed subset `A ⊇ X` by
attaching `D(E c)` along `S(E c)`, then `f c` induces an isomorphism
`Hₙ(D(E c), S(E c)) ≅ Hₙ(T, A)`. This is `TauCeti.isIso_singularHomologyMap_of_attach_discBundle`
for the space `T` and its subset `A`. -/
private lemma isIso_singularHomologyMap_discMap (c : ι)
    (hnorm : Continuous fun v : TotalSpace (F c) (E c) ↦ ‖v.2‖)
    (hf : IsClosedEmbedding (TopPair.Hom.fst (f c))) {A T : Set Z} (hAT : A ⊆ T) (hXA : X ⊆ A)
    (hT : range (TopPair.Hom.fst (f c)) ⊆ T) (hA : IsClosed A)
    (hAc : ∀ v : discBundle (F c) (E c),
      TopPair.Hom.fst (f c) v ∈ A → (v : TotalSpace (F c) (E c)) ∈ sphereBundle (F c) (E c))
    (hcover : A ∪ range (TopPair.Hom.fst (f c)) = T) :
    IsIso (TopPair.singularHomologyMap (discMap f c hAT hXA hT) R n) := by
  let e := TopPair.ofSubsetPreimageValIso hAT
  have hfst : TopPair.Hom.fst (discMap f c hAT hXA hT ≫ e.inv) =
      TopPair.Hom.fst (discMap f c hAT hXA hT) := by
    rw [TopPair.Hom.fst_comp, TopPair.ofSubsetPreimageValIso_inv_fst]
    exact Category.comp_id _
  have h : IsIso (TopPair.singularHomologyMap (discMap f c hAT hXA hT ≫ e.inv) R n) := by
    refine isIso_singularHomologyMap_of_attach_discBundle hnorm
      (hA.preimage continuous_subtype_val) R n ?_ (fun v hv ↦ hAc v ?_) ?_
    · rw [hfst, TopPair.ofInclusionMap_fst]
      exact IsClosedEmbedding.of_comp IsEmbedding.subtypeVal hf
    · rw [hfst, TopPair.ofInclusionMap_fst] at hv
      exact hv
    · rw [hfst, TopPair.ofInclusionMap_fst]
      refine eq_univ_of_forall fun ⟨x, hx⟩ ↦ ?_
      rcases hcover.symm ▸ hx with hx | ⟨v, rfl⟩
      · exact Or.inl hx
      · exact Or.inr ⟨v, rfl⟩
  rw [show discMap f c hAT hXA hT = (discMap f c hAT hXA hT ≫ e.inv) ≫ e.hom by simp,
    TopPair.singularHomologyMap_comp]
  infer_instance

/-- The disc `D(E c)` attached to `Z_{s ∖ {c}}` gives `Zₛ`, for `c ∈ s`, so `f c` induces an
isomorphism `Hₙ(D(E c), S(E c)) ≅ Hₙ(Zₛ, Z_{s ∖ {c}})`. -/
private lemma isIso_singularHomologyMap_discMap_erase [DecidableEq ι]
    (hnorm : ∀ a, Continuous fun v : TotalSpace (F a) (E a) ↦ ‖v.2‖) (hX : IsClosed X)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a (v : discBundle (F a) (E a)),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ sphereBundle (F a) (E a))
    (hinter : Pairwise fun a b ↦
      range (TopPair.Hom.fst (f a)) ∩ range (TopPair.Hom.fst (f b)) ⊆ X)
    {s : Finset ι} {c : ι} (hc : c ∈ s) :
    IsIso (TopPair.singularHomologyMap (discMap f c (attachUnion_mono f (s.erase_subset c))
      (subset_attachUnion f _) (range_subset_attachUnion f hc)) R n) := by
  refine isIso_singularHomologyMap_discMap f R n c (hnorm c) (hf c) _ _ _
    (isClosed_attachUnion f hX hf _)
    (fun v hv ↦ mem_sphereBundle_of_mem_attachUnion_erase f hfX hinter hv) ?_
  rw [← attachUnion_insert, Finset.insert_erase hc]

/-! ### Joint injectivity of the projections -/

/-- A morphism `g` into `Hₙ(T, X)`, for subsets `X ⊆ A ⊆ T`, kills the map to `Hₙ(T, A)` as soon
as it kills the map to `Hₙ(T, A')` for a set `A'` equal to `A`. -/
private lemma comp_singularHomologyMap_quotMap_eq_zero_of_eq {A A' T : Set Z} (hXA : X ⊆ A)
    (hAT : A ⊆ T) (hXA' : X ⊆ A') (hA'T : A' ⊆ T) (hA : A' = A) {Y : C}
    (g : Y ⟶ (TopPair.ofInclusion (hXA.trans hAT)).singularHomology R n)
    (hg : g ≫ TopPair.singularHomologyMap (quotMap hXA' hA'T) R n = 0) :
    g ≫ TopPair.singularHomologyMap (quotMap hXA hAT) R n = 0 := by
  subst hA
  exact hg

/-- The inclusion `(Zₛ, X) ⟶ (Zₜ, X)` for `s ⊆ t`. -/
private abbrev inclMap {s t : Finset ι} (hst : s ⊆ t) :
    TopPair.ofInclusion (subset_attachUnion f s) ⟶ TopPair.ofInclusion (subset_attachUnion f t) :=
  TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion (attachUnion_mono f hst))
    fun _ hx ↦ by simpa using hx

/-- **Comparison along an inclusion.** For `c ∈ s ⊆ t`, a morphism `g` into `Hₙ(Zₛ, X)` vanishes
in `Hₙ(Zₛ, Z_{s ∖ {c}})` as soon as its image in `Hₙ(Zₜ, X)` vanishes in `Hₙ(Zₜ, Z_{t ∖ {c}})`:
the map `Hₙ(Zₛ, Z_{s ∖ {c}}) ⟶ Hₙ(Zₜ, Z_{t ∖ {c}})` is an isomorphism, both sides being
`Hₙ(D(E c), S(E c))`. -/
private lemma comp_quotMap_eq_zero_of_comp_inclMap [DecidableEq ι]
    (hnorm : ∀ a, Continuous fun v : TotalSpace (F a) (E a) ↦ ‖v.2‖) (hX : IsClosed X)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a (v : discBundle (F a) (E a)),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ sphereBundle (F a) (E a))
    (hinter : Pairwise fun a b ↦
      range (TopPair.Hom.fst (f a)) ∩ range (TopPair.Hom.fst (f b)) ⊆ X)
    {s t : Finset ι} (hst : s ⊆ t) {c : ι} (hc : c ∈ s) {Y : C}
    (g : Y ⟶ (TopPair.ofInclusion (subset_attachUnion f s)).singularHomology R n)
    (hg : g ≫ TopPair.singularHomologyMap (inclMap f hst) R n ≫ TopPair.singularHomologyMap
      (quotMap (subset_attachUnion f (t.erase c)) (attachUnion_mono f (t.erase_subset c))) R n =
        0) :
    g ≫ TopPair.singularHomologyMap (quotMap (subset_attachUnion f (s.erase c))
      (attachUnion_mono f (s.erase_subset c))) R n = 0 := by
  -- The map `k : (Zₛ, Z_{s ∖ {c}}) ⟶ (Zₜ, Z_{t ∖ {c}})`.
  let k : TopPair.ofInclusion (attachUnion_mono f (s.erase_subset c)) ⟶
      TopPair.ofInclusion (attachUnion_mono f (t.erase_subset c)) :=
    TopPair.ofInclusionMap _ _ (ContinuousMap.inclusion (attachUnion_mono f hst))
      fun _ hx ↦ by simpa using attachUnion_mono f (Finset.erase_subset_erase c hst) hx
  have hk : TopPair.singularHomologyMap (discMap f c _ (subset_attachUnion f _)
        (range_subset_attachUnion f hc)) R n ≫ TopPair.singularHomologyMap k R n =
      TopPair.singularHomologyMap (discMap f c _ (subset_attachUnion f _)
        (range_subset_attachUnion f (hst hc))) R n := by
    rw [← TopPair.singularHomologyMap_comp,
      discMap_comp_ofInclusionMap f c _ _ _ _ _ _ _ _ fun _ ↦ rfl]
  have := isIso_singularHomologyMap_discMap_erase f R n hnorm hX hf hfX hinter hc
  have := isIso_singularHomologyMap_discMap_erase f R n hnorm hX hf hfX hinter (hst hc)
  have : IsIso (TopPair.singularHomologyMap k R n) := IsIso.of_isIso_fac_left hk
  -- The square `(Zₛ, X) ⟶ (Zₜ, X) ⟶ (Zₜ, Z_{t ∖ {c}})` and `(Zₛ, X) ⟶ (Zₛ, Z_{s ∖ {c}}) ⟶ ⋯`.
  have hsq : quotMap (subset_attachUnion f (s.erase c)) (attachUnion_mono f (s.erase_subset c)) ≫
      k = inclMap f hst ≫ quotMap (subset_attachUnion f (t.erase c))
        (attachUnion_mono f (t.erase_subset c)) :=
    TopPair.ofInclusionMap_comp_ofInclusionMap_eq _ _ _ _ _ _ _ _ fun _ ↦ rfl
  rw [← cancel_mono (TopPair.singularHomologyMap k R n), Category.assoc,
    ← TopPair.singularHomologyMap_comp, hsq, TopPair.singularHomologyMap_comp, hg]
  simp

/-- **The projections are jointly monomorphic.** A morphism into `Hₙ(Zₛ, X)` which vanishes
after each of the maps `Hₙ(Zₛ, X) ⟶ Hₙ(Zₛ, Z_{s ∖ {c}})`, `c ∈ s`, vanishes. -/
private lemma eq_zero_of_forall_comp_singularHomologyMap_eq_zero [DecidableEq ι]
    (hnorm : ∀ a, Continuous fun v : TotalSpace (F a) (E a) ↦ ‖v.2‖) (hX : IsClosed X)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a (v : discBundle (F a) (E a)),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ sphereBundle (F a) (E a))
    (hinter : Pairwise fun a b ↦
      range (TopPair.Hom.fst (f a)) ∩ range (TopPair.Hom.fst (f b)) ⊆ X)
    (s : Finset ι) {Y : C}
    (g : Y ⟶ (TopPair.ofInclusion (subset_attachUnion f s)).singularHomology R n)
    (hg : ∀ c ∈ s, g ≫ TopPair.singularHomologyMap (quotMap (subset_attachUnion f (s.erase c))
      (attachUnion_mono f (s.erase_subset c))) R n = 0) :
    g = 0 := by
  induction s using Finset.induction_on generalizing Y with
  | empty =>
    have h0 := TopPair.isZero_singularHomology_ofInclusion_self R X n
    rw [← TopPair.isZero_singularHomology_ofInclusion_congr R (subset_attachUnion f ∅)
      (subset_refl X) (attachUnion_empty f) rfl n] at h0
    exact h0.eq_of_tgt _ _
  | insert a s ha ih =>
    -- The triple `(Z_{s ∪ {a}}, Zₛ, X)`.
    have hs := Finset.subset_insert a s
    let T₃ := TopTriple.ofInclusions (subset_attachUnion f s) (attachUnion_mono f hs)
    have hi : TopTriple.innerToTotal.app T₃ = inclMap f hs :=
      TopPair.hom_ext_of_fst _ (by rw [TopPair.ofInclusionMap_fst]; rfl)
    have hq : TopTriple.totalToOuter.app T₃ =
        quotMap (subset_attachUnion f s) (attachUnion_mono f hs) :=
      TopTriple.totalToOuter_app_ofInclusions _ _
    -- `g` vanishes in `Hₙ(Z_{s ∪ {a}}, Zₛ)`, so up to an epimorphism it comes from `Hₙ(Zₛ, X)`.
    have hga : g ≫ TopPair.singularHomologyMap (TopTriple.totalToOuter.app T₃) R n = 0 := by
      rw [hq]
      exact comp_singularHomologyMap_quotMap_eq_zero_of_eq R n _ _ _ _
        (by rw [Finset.erase_insert ha]) g (hg a (Finset.mem_insert_self a s))
    obtain ⟨Y', p, _, g', hpg⟩ :=
      (T₃.singularHomology_exact_total R n).exact_up_to_refinements g hga
    suffices H : ∀ g'' : Y' ⟶
        (TopPair.ofInclusion (subset_attachUnion f s)).singularHomology R n,
        p ≫ g = g'' ≫ TopPair.singularHomologyMap (inclMap f hs) R n → g = 0 from
      H g' (hpg.trans (congrArg (fun φ ↦ g' ≫ TopPair.singularHomologyMap φ R n) hi))
    intro g' hpg
    suffices hg' : g' = 0 by
      rw [← cancel_epi p, hpg, hg']
      simp
    -- The lift `g'` vanishes after each map `Hₙ(Zₛ, X) ⟶ Hₙ(Zₛ, Z_{s ∖ {c}})`, `c ∈ s`.
    refine ih g' fun c hc ↦ comp_quotMap_eq_zero_of_comp_inclMap f R n hnorm hX hf hfX hinter hs
      hc g' ?_
    rw [← Category.assoc, ← hpg, Category.assoc, hg c (Finset.mem_insert_of_mem hc)]
    simp

/-! ### The biproduct -/

/-- **Attaching finitely many disc bundles.** Let `E a → B a`, for `a` in a finite type `ι`, be
real vector bundles whose fibre norms are continuous on the total spaces, and let
`f a : (D(E a), S(E a)) ⟶ (Z, X)` be maps of pairs with `X` closed in `Z`. Suppose that each
`f a` is a closed embedding of `D(E a)` into `Z` sending a point into `X` only if it lies in
`S(E a)`, that the images of two different `f a` meet only inside `X`, and that `X` together with
the images of the `f a` is all of `Z`: the space `Z` is obtained from `X` by attaching the disc
bundles `D(E a)` along their sphere bundles. Then the maps induced by the `f a` exhibit `Hₙ(Z, X)`
as the coproduct of the `Hₙ(D(E a), S(E a))`, for relative singular homology with coefficients in
any abelian category with coproducts, in every degree. -/
def isColimitCofanSingularHomologyOfAttachDiscBundles [Finite ι]
    (hnorm : ∀ a, Continuous fun v : TotalSpace (F a) (E a) ↦ ‖v.2‖) (hX : IsClosed X)
    (hf : ∀ a, IsClosedEmbedding (TopPair.Hom.fst (f a)))
    (hfX : ∀ a (v : discBundle (F a) (E a)),
      TopPair.Hom.fst (f a) v ∈ X → (v : TotalSpace (F a) (E a)) ∈ sphereBundle (F a) (E a))
    (hinter : Pairwise fun a b ↦
      range (TopPair.Hom.fst (f a)) ∩ range (TopPair.Hom.fst (f b)) ⊆ X)
    (hcover : X ∪ ⋃ a, range (TopPair.Hom.fst (f a)) = univ) :
    IsColimit (Cofan.mk ((TopPair.ofSubset X).singularHomology R n)
      fun a ↦ TopPair.singularHomologyMap (f a) R n) :=
  letI := Fintype.ofFinite ι
  letI := Classical.decEq ι
  -- The pair `(Z, X)` is the pair `(Z_ι, X)` of the union of `X` with all the discs.
  let e := TopPair.ofInclusionIsoOfSubset (subset_attachUnion f Finset.univ)
    (fun x ↦ by simpa [attachUnion] using hcover.ge (mem_univ x)) fun _ ↦ Iff.rfl
  -- The discs as maps of pairs into `(Z_ι, X)` and into `(Z_ι, Z_{ι ∖ {c}})`.
  let θ' (a : ι) := discMap f a (subset_attachUnion f Finset.univ) subset_rfl
    (range_subset_attachUnion f (Finset.mem_univ a))
  let θ (c : ι) := discMap f c (attachUnion_mono f (Finset.univ.erase_subset c))
    (subset_attachUnion f _) (range_subset_attachUnion f (Finset.mem_univ c))
  let q (c : ι) := quotMap (subset_attachUnion f (Finset.univ.erase c))
    (attachUnion_mono f (Finset.univ.erase_subset c))
  -- `f c` identifies `Hₙ(D(E c), S(E c))` with `Hₙ(Z_ι, Z_{ι ∖ {c}})`.
  let θi (c : ι) := @asIso _ _ _ _ (TopPair.singularHomologyMap (θ c) R n)
    (isIso_singularHomologyMap_discMap_erase f R n hnorm hX hf hfX hinter (Finset.mem_univ c))
  have hθ (c : ι) : TopPair.singularHomologyMap (θ' c) R n ≫ TopPair.singularHomologyMap (q c) R n =
      (θi c).hom := by
    rw [← TopPair.singularHomologyMap_comp,
      discMap_comp_ofInclusionMap f c _ _ _ _ _ _ _ _ fun _ ↦ rfl]
    -- `θi c` is `asIso` of this map.
    rfl
  have he (a : ι) : TopPair.singularHomologyMap (θ' a) R n ≫ TopPair.singularHomologyMap e.hom R n =
      TopPair.singularHomologyMap (f a) R n := by
    rw [← TopPair.singularHomologyMap_comp]
    congr 1
    refine TopPair.hom_ext_of_fst _ (TopCat.hom_ext (ContinuousMap.ext fun v ↦ ?_))
    rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply]
    exact (TopPair.ofInclusionIsoOfSubset_hom_fst_apply _ _ _).trans
      (congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ v))
  -- The projection to the disc of `c` goes through `Hₙ(Z_ι, Z_{ι ∖ {c}}) ≅ Hₙ(D(E c), S(E c))`.
  let b : Bicone fun a ↦ (discSpherePair (F a) (E a)).singularHomology R n :=
    Bicone.mk ((TopPair.ofInclusion (subset_attachUnion f Finset.univ)).singularHomology R n)
      (fun c ↦ TopPair.singularHomologyMap (q c) R n ≫ (θi c).inv)
      (fun a ↦ TopPair.singularHomologyMap (θ' a) R n) fun a c ↦ by
        split_ifs with h
        · subst h
          rw [← Category.assoc, hθ, Iso.hom_inv_id, eqToHom_refl]
        · -- The disc of `a` lands in the subspace `Z_{ι ∖ {c}}` of `(Z_ι, Z_{ι ∖ {c}})`.
          rw [← Category.assoc, singularHomologyMap_discMap_comp_quotMap_eq_zero f R n a _ _ _
            (range_subset_attachUnion f (Finset.mem_erase.2 ⟨h, Finset.mem_univ a⟩))]
          simp
  have hπ (c : ι) : b.π c = TopPair.singularHomologyMap (q c) R n ≫ (θi c).inv := rfl
  have total : ∑ c, b.π c ≫ b.ι c = 𝟙 b.pt := by
    -- The difference `𝟙 - ∑ c, π c ≫ ι c` vanishes after every projection, hence vanishes.
    refine (sub_eq_zero.1 ?_).symm
    refine eq_zero_of_forall_comp_singularHomologyMap_eq_zero f R n hnorm hX hf hfX hinter _ _
      fun c _ ↦ (Preadditive.IsIso.comp_right_eq_zero _ (θi c).inv).1 ?_
    rw [Category.assoc, ← hπ, Preadditive.sub_comp, Category.id_comp, Preadditive.sum_comp,
      Finset.sum_eq_single c (fun a _ ha ↦ by rw [Category.assoc, bicone_ι_π_ne b ha]; simp)
        (by simp), Category.assoc, bicone_ι_π_self, Category.comp_id, sub_self]
  IsColimit.ofIsoColimit (isBilimitOfTotal b total).isColimit
    (Cofan.ext (TopPair.singularHomologyMapIso R e n) fun a ↦ he a)

end TauCeti
