/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import TauCeti.AlgebraicTopology.Singular.Excision

/-!
# Relative homology of a union of disjoint closed sets

Let `L` be a subset of a topological space and let `D j`, for `j` in a finite type, be pairwise
disjoint closed subsets. Write `Z = L ∪ ⋃ j, D j`. Then, in every degree and with coefficients in
any abelian category with coproducts, the relative singular homology `Hₙ(Z, L)` is the coproduct
of the groups `Hₙ(L ∪ D j, L)`, with the maps induced by the inclusions as the coproduct
inclusions (`TopPair.isColimitCofanSingularHomologyOfDisjointClosed`). The sets `D j` may meet
`L`, and they need not be attached along any particular subspace: only their closedness and
disjointness enter. This is how the relative homology across a critical level of a function
splits over the critical sets on that level, when these are compact and disjoint.

The proof compares `Hₙ(Z, L)` with the groups `Hₙ(Z, Tⱼ)`, where `Tⱼ = L ∪ (Z ∖ D j)`. Excision
of the closed sets `D k`, `k ≠ j`, identifies `Hₙ(L ∪ D j, L)` with `Hₙ(Z, Tⱼ)`, and the inclusion
of `L ∪ D k` into `Z` carries `L ∪ D k` into `Tⱼ` for `k ≠ j`, so it induces zero into `Hₙ(Z, Tⱼ)`.
Finally `L` is the intersection of the `Tⱼ`, and any two of the `Tⱼ` have interiors covering `Z`;
so a morphism into `Hₙ(Z, L)` is determined by its images in the `Hₙ(Z, Tⱼ)`
(`TopPair.singularHomology_iInter_hom_ext`). This is the finite form of
`TopPair.singularHomology_inter_hom_ext`, proved from it by induction on the number of sets.
Together these make the maps `Hₙ(L ∪ D j, L) ⟶ Hₙ(Z, L)` and the projections through the
excision isomorphisms a biproduct.

## Main results

* `TopPair.singularHomology_iInter_hom_ext`: for finitely many subsets `U j` of a space `X`, any two
  of whose interiors cover `X`, a morphism into `Hₙ(X, ⋂ j, U j)` is determined by its images in
  the groups `Hₙ(X, U j)`.
* `TopPair.isColimitCofanSingularHomologyOfDisjointClosed`: `Hₙ(L ∪ ⋃ j, D j, L)` is the coproduct
  of the `Hₙ(L ∪ D j, L)` for finitely many pairwise disjoint closed sets `D j`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 2.1, Theorem 2.20
  (excision) and Proposition 2.22.
-/

public section

noncomputable section

open CategoryTheory Function Limits Set Topology

universe w v u

namespace TopPair

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (R : A)

section Detection

variable {X : TopCat.{w}} {ι : Type*} {U : ι → Set X}

/-- The induction behind `TopPair.singularHomology_iInter_hom_ext`, over the finite set `s` of
indices of the subsets intersected. -/
private theorem singularHomology_biInter_hom_ext
    (hU : Pairwise fun j k ↦ interior (U j) ∪ interior (U k) = univ) (s : Finset ι)
    {W : Set X} (hW : W = ⋂ j ∈ s, U j) (n : ℕ) {M : A}
    {u v : M ⟶ (ofSubset W).singularHomology R n}
    (h : ∀ j ∈ s, ∀ hj : MapsTo (𝟙 X) W (U j),
      u ≫ TopPair.singularHomologyMap (ofSubsetMap (𝟙 X) hj) R n =
        v ≫ TopPair.singularHomologyMap (ofSubsetMap (𝟙 X) hj) R n) :
    u = v := by
  classical
  induction s using Finset.induction_on generalizing W u v with
  | empty =>
    -- The intersection of no sets is everything, and `(X, X)` has no relative homology.
    subst hW
    refine (isZero_singularHomology_of_surjective_map _ R (range_eq_univ.1 ?_) n).eq_of_tgt u v
    rw [range_ofSubset_map]
    ext
    exact ⟨fun _ ↦ trivial, fun _ ↦ by simp⟩
  | insert a s ha ih =>
    obtain rfl : W = U a ∩ ⋂ j ∈ s, U j := by rw [hW, Finset.set_biInter_insert]
    refine singularHomology_inter_hom_ext R ?_ (fun _ hx ↦ hx.1) (fun _ hx ↦ hx.2) n
      (h a (Finset.mem_insert_self a s) _) ?_
    · -- A point outside the interior of `U a` lies in the interior of every other `U j`.
      refine eq_univ_of_forall fun x ↦ (em (x ∈ interior (U a))).imp id fun hx ↦ ?_
      rw [Finset.interior_iInter, mem_iInter₂]
      intro j hj
      exact ((hU (i := j) (j := a) fun hja ↦ ha (hja ▸ hj)).ge (mem_univ x)).resolve_right hx
    · refine ih rfl fun j hj hj' ↦ ?_
      have hV : MapsTo (𝟙 X) (U a ∩ ⋂ j ∈ s, U j) (⋂ j ∈ s, U j) := fun _ hx ↦ hx.2
      rw [Category.assoc, Category.assoc, ← singularHomologyMap_comp,
        ofSubsetMap_comp_ofSubsetMap_of_comp_eq hV hj' (fun x hx ↦ hj' (hV hx))
          (Category.comp_id _)]
      exact h j (Finset.mem_insert_of_mem hj) _

/-- **Relative homology modulo a finite intersection is detected on the members.** Let `U j`, for
`j` in a finite type, be subsets of a space `X` such that the interiors of any two of them cover
`X`, and let `W = ⋂ j, U j`. Two morphisms into `Hₙ(X, W)` agree as soon as their images in every
`Hₙ(X, U j)` agree. For two sets this is `TopPair.singularHomology_inter_hom_ext`. As there, the
inclusions are arguments, so that the maps of pairs in the hypotheses match those of the caller. -/
theorem singularHomology_iInter_hom_ext [Finite ι]
    (hU : Pairwise fun j k ↦ interior (U j) ∪ interior (U k) = univ) {W : Set X}
    (hW : W = ⋂ j, U j) (n : ℕ) {M : A} {u v : M ⟶ (ofSubset W).singularHomology R n}
    (h : ∀ j (hj : MapsTo (𝟙 X) W (U j)),
      u ≫ TopPair.singularHomologyMap (ofSubsetMap (𝟙 X) hj) R n =
        v ≫ TopPair.singularHomologyMap (ofSubsetMap (𝟙 X) hj) R n) :
    u = v := by
  have := Fintype.ofFinite ι
  exact singularHomology_biInter_hom_ext R hU Finset.univ (by simpa using hW) n
    fun j _ hj ↦ h j hj

end Detection

section DisjointClosed

variable {Y : TopCat.{w}} {ι : Type*} {L : Set Y} {D : ι → Set Y}

/-- The inclusion of pairs `(L ∪ D j, L) ⟶ (L ∪ ⋃ k, D k, L)`. -/
private abbrev unionMap (j : ι) :
    ofInclusion (subset_union_left : L ⊆ L ∪ D j) ⟶
      ofInclusion (subset_union_left : L ⊆ L ∪ ⋃ k, D k) :=
  ofInclusionMap _ _ (ContinuousMap.inclusion (union_subset_union_right L (subset_iUnion D j)))
    fun _ hx ↦ hx

/-- The subset `Tⱼ = L ∪ (Z ∖ D j)` of `Z = L ∪ ⋃ k, D k`. -/
private abbrev complPiece (L : Set Y) (D : ι → Set Y) (j : ι) : Set Y :=
  L ∪ ((L ∪ ⋃ k, D k) \ D j)

private lemma complPiece_subset (L : Set Y) (D : ι → Set Y) (j : ι) :
    complPiece L D j ⊆ L ∪ ⋃ k, D k :=
  union_subset subset_union_left sdiff_subset

private lemma mem_complPiece_of_mem {x : Y} (j : ι) (hx : x ∈ L) : x ∈ complPiece L D j :=
  Or.inl hx

/-- The map of pairs `(Z, L) ⟶ (Z, Tⱼ)` given by the identity of `Z = L ∪ ⋃ k, D k`. -/
private abbrev toCompl (j : ι) :
    ofInclusion (subset_union_left : L ⊆ L ∪ ⋃ k, D k) ⟶ ofInclusion (complPiece_subset L D j) :=
  ofInclusionMap _ _ (ContinuousMap.id _) fun _ hx ↦ mem_complPiece_of_mem j hx

/-- The inclusion of pairs `(L ∪ D j, L) ⟶ (Z, Tⱼ)`. -/
private abbrev unionToCompl (j k : ι) :
    ofInclusion (subset_union_left : L ⊆ L ∪ D k) ⟶ ofInclusion (complPiece_subset L D j) :=
  ofInclusionMap _ _ (ContinuousMap.inclusion (union_subset_union_right L (subset_iUnion D k)))
    fun _ hx ↦ mem_complPiece_of_mem j hx

private lemma unionMap_comp_toCompl (j k : ι) :
    unionMap (L := L) (D := D) k ≫ toCompl j = unionToCompl j k :=
  (ofInclusionMap_comp ..).symm

variable (hD : ∀ j, IsClosed (D j)) (hd : Pairwise (Disjoint on D))

include hD hd in
/-- **Excision of the other closed sets.** The inclusion `(L ∪ D j, L) ⟶ (Z, Tⱼ)` induces
isomorphisms on relative singular homology. -/
private lemma isIso_singularHomologyMap_unionToCompl [Finite ι] (j : ι) (n : ℕ) :
    IsIso (TopPair.singularHomologyMap (unionToCompl (L := L) (D := D) j j) R n) := by
  -- The complement of `⋃ k ≠ j, D k` is open and lies in `L ∪ D j`, while the complement of
  -- `D j` lies in `Tⱼ`; together they cover `Z`.
  have hO : IsOpen (⋃ k ∈ {k | k ≠ j}, D k)ᶜ :=
    ((toFinite _).isClosed_biUnion fun k _ ↦ hD k).isOpen_compl
  have hfx (x : (L ∪ D j : Set Y)) :
      Subtype.val (Hom.fst (unionToCompl (L := L) (D := D) j j) x) = Subtype.val x :=
    congrArg Subtype.val (ofInclusionMap_fst_apply _ _ x)
  refine isIso_singularHomologyMap_of_open_cover R _
    (by
      rw [ofInclusionMap_fst]
      exact IsEmbedding.inclusion (union_subset_union_right L (subset_iUnion D j)))
    (fun x hx ↦ ?_)
    (fun b : Bool ↦ Subtype.val ⁻¹' cond b (⋃ k ∈ {k | k ≠ j}, D k)ᶜ (D j)ᶜ)
    (fun b ↦ by
      cases b
      · exact (hD j).isOpen_compl.preimage continuous_subtype_val
      · exact hO.preimage continuous_subtype_val) ?_ (fun b ↦ ?_) n
  · -- A point of `L ∪ D j` lying in `Tⱼ` lies in `L`.
    rw [range_ofInclusion_map] at hx ⊢
    have hx' : Subtype.val x ∈ complPiece L D j :=
      (congrArg (· ∈ complPiece L D j) (hfx x)).mp hx
    rcases x.2 with hxL | hxj
    · exact hxL
    · exact hx'.resolve_right fun h ↦ h.2 hxj
  · refine eq_univ_of_forall fun z ↦ mem_iUnion.2 ?_
    by_cases hzj : Subtype.val z ∈ D j
    · refine ⟨true, ?_⟩
      have : Subtype.val z ∉ ⋃ k ∈ {k | k ≠ j}, D k := by
        simp only [mem_iUnion, not_exists]
        exact fun k hk hzk ↦ (hd hk).ne_of_mem hzk hzj rfl
      exact this
    · exact ⟨false, hzj⟩
  · cases b
    · rw [range_ofInclusion_map]
      exact Or.inl fun z hz ↦ Or.inr ⟨z.2, hz⟩
    · refine Or.inr fun z hzD ↦ ⟨⟨Subtype.val z, ?_⟩, Subtype.ext (hfx _)⟩
      have hzD' : Subtype.val z ∉ ⋃ k ∈ {k | k ≠ j}, D k := hzD
      simp only [mem_iUnion, not_exists] at hzD'
      rcases z.2 with hz | hz
      · exact Or.inl hz
      · obtain ⟨k, hk⟩ := mem_iUnion.1 hz
        refine Or.inr ?_
        by_contra hkj
        exact hzD' k (fun h ↦ hkj (h ▸ hk)) hk

include hd in
/-- The inclusion `(L ∪ D k, L) ⟶ (Z, Tⱼ)` induces zero for `k ≠ j`, since it sends all of
`L ∪ D k` into `Tⱼ`. -/
private lemma singularHomologyMap_unionToCompl_eq_zero {j k : ι} (hjk : k ≠ j) (n : ℕ) :
    TopPair.singularHomologyMap (unionToCompl (L := L) (D := D) j k) R n = 0 := by
  have hsub : L ∪ D k ⊆ complPiece L D j := by
    rintro x (hx | hx)
    · exact Or.inl hx
    · exact Or.inr ⟨Or.inr (mem_iUnion_of_mem k hx), fun hxj ↦ (hd hjk).ne_of_mem hx hxj rfl⟩
  refine singularHomologyMap_eq_zero_of_fac _ R (TopCat.ofHom (ContinuousMap.inclusion hsub)) ?_ n
  rw [ofInclusionMap_fst]
  rfl

include hD hd in
/-- The projection `Hₙ(Z, L) ⟶ Hₙ(Z, Tⱼ) ≅ Hₙ(L ∪ D j, L)`. -/
private noncomputable def proj [Finite ι] (j : ι) (n : ℕ) :
    (ofInclusion (subset_union_left : L ⊆ L ∪ ⋃ k, D k)).singularHomology R n ⟶
      (ofInclusion (subset_union_left : L ⊆ L ∪ D j)).singularHomology R n :=
  haveI := isIso_singularHomologyMap_unionToCompl (L := L) R hD hd j n
  TopPair.singularHomologyMap (toCompl (L := L) (D := D) j) R n ≫
    inv (TopPair.singularHomologyMap (unionToCompl (L := L) (D := D) j j) R n)

open scoped Classical in
/-- The inclusions and projections satisfy the relations of a biproduct. -/
private lemma singularHomologyMap_unionMap_comp_proj [Finite ι] (j k : ι) (n : ℕ) :
    TopPair.singularHomologyMap (unionMap (L := L) (D := D) k) R n ≫ proj R hD hd j n =
      if h : k = j then eqToHom (congrArg (fun j ↦
        (ofInclusion (subset_union_left : L ⊆ L ∪ D j)).singularHomology R n) h) else 0 := by
  have := isIso_singularHomologyMap_unionToCompl (L := L) R hD hd j n
  rw [proj, ← Category.assoc, ← singularHomologyMap_comp, unionMap_comp_toCompl]
  split_ifs with hkj
  · subst hkj
    rw [IsIso.hom_inv_id, eqToHom_refl]
  · rw [singularHomologyMap_unionToCompl_eq_zero R hd hkj, zero_comp]

/-- The sum of the composites of the projections with the inclusions is the identity of
`Hₙ(Z, L)`. -/
private lemma sum_proj_comp_singularHomologyMap_unionMap [Fintype ι] (n : ℕ) :
    ∑ j, proj R hD hd j n ≫ TopPair.singularHomologyMap (unionMap (L := L) (D := D) j) R n =
      𝟙 _ := by
  classical
  -- Both sides are detected on the pairs `(Z, Tⱼ)`, read in the ambient space `Z`.
  let e := ofSubsetPreimageValIso (subset_union_left : L ⊆ L ∪ ⋃ j, D j)
  rw [← cancel_mono (TopPair.singularHomologyMap e.inv R n)]
  refine singularHomology_iInter_hom_ext R
    (U := fun j ↦ Subtype.val ⁻¹' complPiece L D j) (fun j k hjk ↦ ?_) ?_ n fun j hj ↦ ?_
  · -- The interior of the preimage of `Tⱼ` contains the complement of `D j`.
    have hint (j : ι) : Subtype.val ⁻¹' (D j)ᶜ ⊆
        interior (Subtype.val ⁻¹' complPiece L D j : Set (L ∪ ⋃ k, D k : Set Y)) :=
      interior_maximal (fun x hx ↦ Or.inr ⟨x.2, hx⟩)
        ((hD j).isOpen_compl.preimage continuous_subtype_val)
    refine eq_univ_of_forall fun x ↦ ?_
    by_cases hxj : (x : Y) ∈ D j
    · exact Or.inr (hint k fun hxk ↦ (hd hjk).ne_of_mem hxj hxk rfl)
    · exact Or.inl (hint j hxj)
  · ext ⟨x, hx⟩
    simp only [mem_preimage, mem_iInter]
    refine ⟨fun hxL _ ↦ Or.inl hxL, fun hxT ↦ ?_⟩
    rcases hx with hx | hx
    · exact hx
    · obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      exact (hxT j).resolve_right fun h ↦ h.2 hj
  · -- Read in `Z`, the map `(Z, L) ⟶ (Z, Tⱼ)` is the identity of `Z`.
    have hsq : e.inv ≫ ofSubsetMap (𝟙 _) hj =
        toCompl j ≫ (ofSubsetPreimageValIso (complPiece_subset L D j)).inv := by
      refine hom_ext_of_fst _ ?_
      rw [Hom.fst_comp, Hom.fst_comp, ofSubsetPreimageValIso_inv_fst, ofSubsetMap_fst,
        ofInclusionMap_fst, ofSubsetPreimageValIso_inv_fst]
      rfl
    rw [Category.assoc, Category.assoc, ← singularHomologyMap_comp, hsq,
      singularHomologyMap_comp, ← Category.assoc, ← Category.assoc]
    congr 1
    have := isIso_singularHomologyMap_unionToCompl (L := L) R hD hd j n
    rw [Category.id_comp, Preadditive.sum_comp, Finset.sum_eq_single j]
    · rw [proj, Category.assoc, Category.assoc, ← singularHomologyMap_comp,
        unionMap_comp_toCompl, IsIso.inv_hom_id, Category.comp_id]
    · intro k _ hkj
      rw [Category.assoc, ← singularHomologyMap_comp, unionMap_comp_toCompl,
        singularHomologyMap_unionToCompl_eq_zero R hd hkj, comp_zero]
    · exact fun h ↦ absurd (Finset.mem_univ j) h

include hD hd in
/-- **Relative homology of a union of disjoint closed sets.** Let `L` be a subset of a
topological space and let `D j`, for `j` in a finite type, be pairwise disjoint closed subsets.
Then, in every degree and with coefficients in any abelian category with coproducts,
`Hₙ(L ∪ ⋃ j, D j, L)` is the coproduct of the `Hₙ(L ∪ D j, L)`, with the maps induced by the
inclusions of pairs as the coproduct inclusions. -/
def isColimitCofanSingularHomologyOfDisjointClosed [Finite ι] (n : ℕ) :
    IsColimit (Cofan.mk
      ((ofInclusion (subset_union_left : L ⊆ L ∪ ⋃ j, D j)).singularHomology R n)
      fun j ↦ TopPair.singularHomologyMap (ofInclusionMap subset_union_left subset_union_left
        (ContinuousMap.inclusion (union_subset_union_right L (subset_iUnion D j)))
        fun _ hx ↦ hx) R n) :=
  have := Fintype.ofFinite ι
  let b : Bicone fun j ↦ (ofInclusion (subset_union_left : L ⊆ L ∪ D j)).singularHomology R n :=
    { pt := (ofInclusion (subset_union_left : L ⊆ L ∪ ⋃ j, D j)).singularHomology R n
      π := fun j ↦ proj R hD hd j n
      ι := fun j ↦ TopPair.singularHomologyMap (unionMap j) R n
      ι_π := fun k j ↦ singularHomologyMap_unionMap_comp_proj R hD hd j k n }
  IsColimit.ofIsoColimit
    (isBilimitOfTotal b (sum_proj_comp_singularHomologyMap_unionMap R hD hd n)).isColimit
    (Cofan.ext (Iso.refl _) fun _ ↦ Category.comp_id _)

end DisjointClosed

end TopPair
