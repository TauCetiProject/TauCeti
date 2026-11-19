/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Pair

/-!
# The Mayer–Vietoris sequence for the complements of two closed sets

Let `S` and `T` be closed subsets of a topological space `X`, and write `Hⁿ(-)` for relative
singular cohomology. The pairs `(X, X ∖ S)` and `(X, X ∖ T)` have the Mayer–Vietoris sequence
`⋯ ⟶ Hⁿ(X, X ∖ (S ∩ T)) ⟶ Hⁿ(X, X ∖ S) ⊞ Hⁿ(X, X ∖ T) ⟶ Hⁿ(X, X ∖ (S ∪ T)) ⟶`
`Hᵐ(X, X ∖ (S ∩ T)) ⟶ ⋯`, `n + 1 = m`, whose first two maps are restrictions
(`TopCat.singularCohomologyComplRestrict`).
This is the Mayer–Vietoris sequence of the pairs `(univ, X ∖ S)` and `(univ, X ∖ T)`
(`TopCat.singularCohomologyPairMayerVietorisδ`), transported along the identifications of these
pairs, and of their intersection and union, with pairs of the form `(X, -)`
(`TopCat.univComplPairIso`, `TopCat.interComplPairIso` and `TopCat.unionComplPairIso`). The
complements are open because `S` and `T` are closed.

For compact sets of a Hausdorff space, these are the sequences whose colimit over compact sets is
the Mayer–Vietoris sequence of cohomology with compact supports.

## Main definitions and results

* `TopCat.exists_singularCohomologyComplRestrict_eq_of_add_eq_zero`: exactness at
  `Hⁿ(X, X ∖ S) ⊞ Hⁿ(X, X ∖ T)`, stated with the restrictions.
* `TopCat.singularCohomologyComplMayerVietorisδ`: the connecting morphism
  `Hⁿ(X, X ∖ (S ∪ T)) ⟶ Hᵐ(X, X ∖ (S ∩ T))`, characterized by
  `TopCat.singularCohomologyComplMayerVietorisδ_def`.
* `TopCat.singularCohomologyComplRestrict_singularCohomologyComplMayerVietorisδ_left` and its
  three variants: the composites of the connecting morphism with the restrictions vanish.
* `TopCat.exists_sub_eq_of_singularCohomologyComplMayerVietorisδ_eq_zero` and
  `TopCat.exists_singularCohomologyComplMayerVietorisδ_eq`: exactness at `Hⁿ(X, X ∖ (S ∪ T))` and
  at `Hᵐ(X, X ∖ (S ∩ T))`.
* `TopCat.singularCohomologyComplMayerVietorisδ_naturality`: naturality along maps `f : X ⟶ Y`
  carrying `X ∖ S` and `X ∖ T` into `Y ∖ S'` and `Y ∖ T'`, with the case of the identity of `X`
  and closed sets `S ⊆ S'`, `T ⊆ T'` in
  `TopCat.singularCohomologyComplMayerVietorisδ_naturality_of_subset`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the Mayer–Vietoris sequence of the pairs `(X, X ∖ K)` and `(X, X ∖ L)` in the proof
  of Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Limits

universe w v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] {R : C}
  {k : Type*} [Ring k] [Linear k C] {M : C} {X : TopCat.{w}}

/-! ### The pairs `(univ, X ∖ S)` -/

/-- The pair `(univ, X ∖ S)` is the pair `(X, X ∖ S)`. -/
abbrev univComplPairIso (S : Set X) :
    TopPair.ofInclusion (Set.subset_univ Sᶜ) ≅ TopPair.ofSubset Sᶜ :=
  TopPair.ofInclusionIsoOfSubset _ Set.mem_univ fun _ ↦ Iff.rfl

/-- The pair `(univ ∩ univ, (X ∖ S) ∩ (X ∖ T))` is the pair `(X, X ∖ (S ∪ T))`. -/
abbrev interComplPairIso (S T : Set X) :
    TopPair.ofInclusion (Set.inter_subset_inter (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)) ≅
      TopPair.ofSubset (S ∪ T)ᶜ :=
  TopPair.ofInclusionIsoOfSubset _ (fun x ↦ Set.mem_inter (Set.mem_univ x) (Set.mem_univ x))
    fun _ ↦ by rw [Set.compl_union]

/-- The pair `(univ ∪ univ, (X ∖ S) ∪ (X ∖ T))` is the pair `(X, X ∖ (S ∩ T))`. -/
abbrev unionComplPairIso (S T : Set X) :
    TopPair.ofInclusion (Set.union_subset_union (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)) ≅
      TopPair.ofSubset (S ∩ T)ᶜ :=
  TopPair.ofInclusionIsoOfSubset _ (fun x ↦ Set.mem_union_left _ (Set.mem_univ x))
    fun _ ↦ by rw [Set.compl_inter]

variable {S T : Set X}

/-- Under `TopCat.univComplPairIso` and `TopCat.interComplPairIso`, the restriction from
`(univ, X ∖ S)` to `(univ ∩ univ, (X ∖ S) ∩ (X ∖ T))` is the restriction
`Hⁿ(X, X ∖ S) ⟶ Hⁿ(X, X ∖ (S ∪ T))`. -/
@[reassoc, elementwise]
private lemma singularCohomologyMap_univComplPairIso_hom_inter_left (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (univComplPairIso S).hom n ≫
        TopPair.singularCohomologyMap (TopPair.ofInclusionMap
          (Set.inter_subset_inter (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)) (Set.subset_univ Sᶜ)
          (ContinuousMap.inclusion Set.inter_subset_left) fun _ hx ↦ Set.inter_subset_left hx) n =
      singularCohomologyComplRestrict R k M Set.subset_union_left n ≫
        TopPair.singularCohomologyMap (interComplPairIso S T).hom n := by
  rw [← TopPair.singularCohomologyMap_comp, ← TopPair.singularCohomologyMap_comp]
  exact congrArg (TopPair.singularCohomologyMap · n)
    (TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _
      (mapsTo_id_compl Set.subset_union_left))

@[reassoc, elementwise]
private lemma singularCohomologyMap_univComplPairIso_hom_inter_right (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (univComplPairIso T).hom n ≫
        TopPair.singularCohomologyMap (TopPair.ofInclusionMap
          (Set.inter_subset_inter (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)) (Set.subset_univ Tᶜ)
          (ContinuousMap.inclusion Set.inter_subset_right) fun _ hx ↦ Set.inter_subset_right hx) n =
      singularCohomologyComplRestrict R k M Set.subset_union_right n ≫
        TopPair.singularCohomologyMap (interComplPairIso S T).hom n := by
  rw [← TopPair.singularCohomologyMap_comp, ← TopPair.singularCohomologyMap_comp]
  exact congrArg (TopPair.singularCohomologyMap · n)
    (TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _
      (mapsTo_id_compl Set.subset_union_right))

/-- Under `TopCat.unionComplPairIso` and `TopCat.univComplPairIso`, the restriction from
`(univ ∪ univ, (X ∖ S) ∪ (X ∖ T))` to `(univ, X ∖ S)` is the restriction
`Hⁿ(X, X ∖ (S ∩ T)) ⟶ Hⁿ(X, X ∖ S)`. -/
@[reassoc, elementwise]
private lemma singularCohomologyMap_unionComplPairIso_hom_union_left (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (unionComplPairIso S T).hom n ≫
        TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.subset_univ Sᶜ)
          (Set.union_subset_union (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ))
          (ContinuousMap.inclusion Set.subset_union_left) fun _ hx ↦ Set.subset_union_left hx) n =
      singularCohomologyComplRestrict R k M Set.inter_subset_left n ≫
        TopPair.singularCohomologyMap (univComplPairIso S).hom n := by
  rw [← TopPair.singularCohomologyMap_comp, ← TopPair.singularCohomologyMap_comp]
  exact congrArg (TopPair.singularCohomologyMap · n)
    (TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _
      (mapsTo_id_compl Set.inter_subset_left))

@[reassoc, elementwise]
private lemma singularCohomologyMap_unionComplPairIso_hom_union_right (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (unionComplPairIso S T).hom n ≫
        TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.subset_univ Tᶜ)
          (Set.union_subset_union (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ))
          (ContinuousMap.inclusion Set.subset_union_right) fun _ hx ↦ Set.subset_union_right hx) n =
      singularCohomologyComplRestrict R k M Set.inter_subset_right n ≫
        TopPair.singularCohomologyMap (univComplPairIso T).hom n := by
  rw [← TopPair.singularCohomologyMap_comp, ← TopPair.singularCohomologyMap_comp]
  exact congrArg (TopPair.singularCohomologyMap · n)
    (TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _
      (mapsTo_id_compl Set.inter_subset_right))

/-- The inverse form of `singularCohomologyMap_unionComplPairIso_hom_union_left`. -/
@[reassoc]
private lemma singularCohomologyMap_unionComplPairIso_inv_union_left (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (unionComplPairIso S T).inv n ≫
        singularCohomologyComplRestrict R k M Set.inter_subset_left n =
      TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.subset_univ Sᶜ)
          (Set.union_subset_union (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ))
          (ContinuousMap.inclusion Set.subset_union_left) fun _ hx ↦ Set.subset_union_left hx) n ≫
        TopPair.singularCohomologyMap (univComplPairIso S).inv n := by
  rw [← TopPair.singularCohomologyMap_comp, ← TopPair.singularCohomologyMap_comp]
  refine congrArg (TopPair.singularCohomologyMap · n) ?_
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _
    (mapsTo_id_compl Set.inter_subset_left)).symm

@[reassoc]
private lemma singularCohomologyMap_unionComplPairIso_inv_union_right (n : ℕ) :
    TopPair.singularCohomologyMap (R := R) (k := k) (M := M) (unionComplPairIso S T).inv n ≫
        singularCohomologyComplRestrict R k M Set.inter_subset_right n =
      TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.subset_univ Tᶜ)
          (Set.union_subset_union (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ))
          (ContinuousMap.inclusion Set.subset_union_right) fun _ hx ↦ Set.subset_union_right hx) n ≫
        TopPair.singularCohomologyMap (univComplPairIso T).inv n := by
  rw [← TopPair.singularCohomologyMap_comp, ← TopPair.singularCohomologyMap_comp]
  refine congrArg (TopPair.singularCohomologyMap · n) ?_
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
  exact (TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _
    (mapsTo_id_compl Set.inter_subset_right)).symm

/-! ### Exactness at the middle term -/

/-- **Mayer–Vietoris for the complements of two closed sets**, exactness at the middle term: if
`a ∈ Hⁿ(X, X ∖ S)` and `b ∈ Hⁿ(X, X ∖ T)` restrict to classes of `Hⁿ(X, X ∖ (S ∪ T))` with sum
zero, then `a` and `-b` are the restrictions of one class of `Hⁿ(X, X ∖ (S ∩ T))`. This is
`TopCat.singularCohomologyPairMayerVietoris_exact₂` for the pairs `(univ, X ∖ S)` and
`(univ, X ∖ T)`. -/
lemma exists_singularCohomologyComplRestrict_eq_of_add_eq_zero (hS : IsClosed S)
    (hT : IsClosed T) {n : ℕ} (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n)
    (b : (TopPair.ofSubset Tᶜ).singularCohomology R k M n)
    (h : singularCohomologyComplRestrict R k M Set.subset_union_left n a +
      singularCohomologyComplRestrict R k M Set.subset_union_right n b = 0) :
    ∃ z : (TopPair.ofSubset (S ∩ T)ᶜ).singularCohomology R k M n,
      singularCohomologyComplRestrict R k M Set.inter_subset_left n z = a ∧
        singularCohomologyComplRestrict R k M Set.inter_subset_right n z = -b := by
  have hCA : Sᶜ ⊆ (Set.univ : Set X) := Set.subset_univ _
  have hDB : Tᶜ ⊆ (Set.univ : Set X) := Set.subset_univ _
  have hex := (ShortComplex.moduleCat_exact_iff _).1
    (singularCohomologyPairMayerVietoris_exact₂ R k M hCA hDB isOpen_univ isOpen_univ
      (hS.isOpen_compl.preimage continuous_subtypeVal)
      (hT.isOpen_compl.preimage continuous_subtypeVal) n)
  let HC := (TopPair.ofInclusion hCA).singularCohomology R k M n
  let HD := (TopPair.ofInclusion hDB).singularCohomology R k M n
  obtain ⟨q, hq⟩ := hex ((biprod.inl : HC ⟶ HC ⊞ HD)
      (TopPair.singularCohomologyMap (univComplPairIso S).hom n a) +
    (biprod.inr : HD ⟶ HC ⊞ HD) (-TopPair.singularCohomologyMap (univComplPairIso T).hom n b)) (by
      dsimp only [HC, HD]
      simp only [map_add, map_neg, inl_singularCohomologyPairMayerVietorisFromBiprod_apply,
        inr_singularCohomologyPairMayerVietorisFromBiprod_apply, neg_neg,
        singularCohomologyMap_univComplPairIso_hom_inter_left_apply,
        singularCohomologyMap_univComplPairIso_hom_inter_right_apply]
      rw [← map_add, h, map_zero])
  -- transport the solution back along the identifications of pairs
  have hU : TopPair.singularCohomologyMap (unionComplPairIso S T).hom n
      (TopPair.singularCohomologyMap (unionComplPairIso S T).inv n q) = q :=
    ((TopPair.singularCohomologyFunctor R k M n).mapIso
      (unionComplPairIso S T).op).inv_hom_id_apply q
  have hinjS : Function.Injective (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (univComplPairIso S).hom n) :=
    ((TopPair.singularCohomologyFunctor R k M n).mapIso
      (univComplPairIso S).op).toLinearEquiv.injective
  have hinjT : Function.Injective (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (univComplPairIso T).hom n) :=
    ((TopPair.singularCohomologyFunctor R k M n).mapIso
      (univComplPairIso T).op).toLinearEquiv.injective
  refine ⟨TopPair.singularCohomologyMap (unionComplPairIso S T).inv n q, hinjS ?_, hinjT ?_⟩
  · rw [← singularCohomologyMap_unionComplPairIso_hom_union_left_apply, hU,
      ← singularCohomologyPairMayerVietorisToBiprod_fst_apply R k M hCA hDB, hq]
    simp [HC, HD]
  · rw [← singularCohomologyMap_unionComplPairIso_hom_union_right_apply, hU,
      ← singularCohomologyPairMayerVietorisToBiprod_snd_apply R k M hCA hDB, hq]
    simp [HC, HD]

/-! ### The connecting morphism -/

variable (R k M) in
/-- The connecting morphism `Hⁿ(X, X ∖ (S ∪ T)) ⟶ Hᵐ(X, X ∖ (S ∩ T))`, `n + 1 = m`, of the
Mayer–Vietoris sequence of the pairs `(X, X ∖ S)` and `(X, X ∖ T)` for closed sets `S` and `T`:
the connecting morphism `TopCat.singularCohomologyPairMayerVietorisδ` of the pairs
`(univ, X ∖ S)` and `(univ, X ∖ T)`, transported along `TopCat.interComplPairIso` and
`TopCat.unionComplPairIso`. -/
def singularCohomologyComplMayerVietorisδ (hS : IsClosed S) (hT : IsClosed T)
    (n m : ℕ) (h : n + 1 = m := by lia) :
    (TopPair.ofSubset (S ∪ T)ᶜ).singularCohomology R k M n ⟶
      (TopPair.ofSubset (S ∩ T)ᶜ).singularCohomology R k M m :=
  TopPair.singularCohomologyMap (interComplPairIso S T).hom n ≫
    singularCohomologyPairMayerVietorisδ R k M (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)
      isOpen_univ isOpen_univ (hS.isOpen_compl.preimage continuous_subtypeVal)
      (hT.isOpen_compl.preimage continuous_subtypeVal) n m h ≫
    TopPair.singularCohomologyMap (unionComplPairIso S T).inv m

variable (R k M) in
/-- The connecting morphism for the complements of two closed sets is the connecting morphism of
the pairs `(univ, X ∖ S)` and `(univ, X ∖ T)`, transported along `TopCat.interComplPairIso` and
`TopCat.unionComplPairIso`. -/
@[elementwise]
lemma singularCohomologyComplMayerVietorisδ_def (hS : IsClosed S) (hT : IsClosed T)
    (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyComplMayerVietorisδ R k M hS hT n m h =
      TopPair.singularCohomologyMap (interComplPairIso S T).hom n ≫
        singularCohomologyPairMayerVietorisδ R k M (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)
          isOpen_univ isOpen_univ (hS.isOpen_compl.preimage continuous_subtypeVal)
          (hT.isOpen_compl.preimage continuous_subtypeVal) n m h ≫
        TopPair.singularCohomologyMap (unionComplPairIso S T).inv m :=
  (rfl)

variable (R k M) in
/-- The connecting morphism vanishes on classes restricted from `Hⁿ(X, X ∖ S)`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma singularCohomologyComplRestrict_singularCohomologyComplMayerVietorisδ_left
    (hS : IsClosed S) (hT : IsClosed T) (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyComplRestrict R k M Set.subset_union_left n ≫
      singularCohomologyComplMayerVietorisδ R k M hS hT n m h = 0 := by
  have hδ := singularCohomologyPairMayerVietorisFromBiprod_δ R k M (Set.subset_univ Sᶜ)
    (Set.subset_univ Tᶜ) isOpen_univ isOpen_univ (hS.isOpen_compl.preimage continuous_subtypeVal)
    (hT.isOpen_compl.preimage continuous_subtypeVal) n m h
  rw [singularCohomologyComplMayerVietorisδ_def R k M hS hT n m h,
    ← singularCohomologyMap_univComplPairIso_hom_inter_left_assoc (R := R) (k := k) (M := M),
    ← inl_singularCohomologyPairMayerVietorisFromBiprod_assoc R k M _ (Set.subset_univ Tᶜ),
    reassoc_of% hδ]
  simp

variable (R k M) in
/-- The connecting morphism vanishes on classes restricted from `Hⁿ(X, X ∖ T)`. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma singularCohomologyComplRestrict_singularCohomologyComplMayerVietorisδ_right
    (hS : IsClosed S) (hT : IsClosed T) (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyComplRestrict R k M Set.subset_union_right n ≫
      singularCohomologyComplMayerVietorisδ R k M hS hT n m h = 0 := by
  have hD := inr_singularCohomologyPairMayerVietorisFromBiprod_assoc R k M (Set.subset_univ Sᶜ)
    (Set.subset_univ Tᶜ) n (singularCohomologyPairMayerVietorisδ R k M (Set.subset_univ Sᶜ)
      (Set.subset_univ Tᶜ) isOpen_univ isOpen_univ
      (hS.isOpen_compl.preimage continuous_subtypeVal)
      (hT.isOpen_compl.preimage continuous_subtypeVal) n m h)
  rw [singularCohomologyPairMayerVietorisFromBiprod_δ R k M (Set.subset_univ Sᶜ)
      (Set.subset_univ Tᶜ) isOpen_univ isOpen_univ (hS.isOpen_compl.preimage continuous_subtypeVal)
      (hT.isOpen_compl.preimage continuous_subtypeVal) n m h,
    comp_zero, Preadditive.neg_comp, zero_eq_neg] at hD
  rw [singularCohomologyComplMayerVietorisδ_def R k M hS hT n m h,
    ← singularCohomologyMap_univComplPairIso_hom_inter_right_assoc (R := R) (k := k) (M := M),
    reassoc_of% hD]
  simp

variable (R k M) in
/-- The connecting morphism followed by the restriction to `Hᵐ(X, X ∖ S)` vanishes. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma singularCohomologyComplMayerVietorisδ_singularCohomologyComplRestrict_left
    (hS : IsClosed S) (hT : IsClosed T) (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyComplMayerVietorisδ R k M hS hT n m h ≫
      singularCohomologyComplRestrict R k M Set.inter_subset_left m = 0 := by
  have hδ := singularCohomologyPairMayerVietorisδ_toBiprod R k M (Set.subset_univ Sᶜ)
    (Set.subset_univ Tᶜ) isOpen_univ isOpen_univ (hS.isOpen_compl.preimage continuous_subtypeVal)
    (hT.isOpen_compl.preimage continuous_subtypeVal) n m h
  rw [singularCohomologyComplMayerVietorisδ_def R k M hS hT n m h, Category.assoc, Category.assoc,
    singularCohomologyMap_unionComplPairIso_inv_union_left (R := R) (k := k) (M := M),
    ← singularCohomologyPairMayerVietorisToBiprod_fst_assoc R k M _ (Set.subset_univ Tᶜ),
    reassoc_of% hδ]
  simp

variable (R k M) in
/-- The connecting morphism followed by the restriction to `Hᵐ(X, X ∖ T)` vanishes. -/
@[reassoc (attr := simp), elementwise (attr := simp)]
lemma singularCohomologyComplMayerVietorisδ_singularCohomologyComplRestrict_right
    (hS : IsClosed S) (hT : IsClosed T) (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyComplMayerVietorisδ R k M hS hT n m h ≫
      singularCohomologyComplRestrict R k M Set.inter_subset_right m = 0 := by
  have hδ := singularCohomologyPairMayerVietorisδ_toBiprod R k M (Set.subset_univ Sᶜ)
    (Set.subset_univ Tᶜ) isOpen_univ isOpen_univ (hS.isOpen_compl.preimage continuous_subtypeVal)
    (hT.isOpen_compl.preimage continuous_subtypeVal) n m h
  rw [singularCohomologyComplMayerVietorisδ_def R k M hS hT n m h, Category.assoc, Category.assoc,
    singularCohomologyMap_unionComplPairIso_inv_union_right (R := R) (k := k) (M := M),
    ← singularCohomologyPairMayerVietorisToBiprod_snd_assoc R k M (Set.subset_univ Sᶜ),
    reassoc_of% hδ]
  simp

/-- Exactness of the Mayer–Vietoris sequence of the pairs `(X, X ∖ S)` and `(X, X ∖ T)` at
`Hⁿ(X, X ∖ (S ∪ T))`: a class killed by the connecting morphism is a difference of restrictions of
classes of `Hⁿ(X, X ∖ S)` and `Hⁿ(X, X ∖ T)`. -/
lemma exists_sub_eq_of_singularCohomologyComplMayerVietorisδ_eq_zero
    (hS : IsClosed S) (hT : IsClosed T) {n m : ℕ} (h : n + 1 = m)
    (a : (TopPair.ofSubset (S ∪ T)ᶜ).singularCohomology R k M n)
    (ha : singularCohomologyComplMayerVietorisδ R k M hS hT n m h a = 0) :
    ∃ (b : (TopPair.ofSubset Sᶜ).singularCohomology R k M n)
      (c : (TopPair.ofSubset Tᶜ).singularCohomology R k M n),
        singularCohomologyComplRestrict R k M Set.subset_union_left n b -
          singularCohomologyComplRestrict R k M Set.subset_union_right n c = a := by
  have hCA : Sᶜ ⊆ (Set.univ : Set X) := Set.subset_univ _
  have hDB : Tᶜ ⊆ (Set.univ : Set X) := Set.subset_univ _
  have hex := (ShortComplex.moduleCat_exact_iff _).1
    (singularCohomologyPairMayerVietoris_exact₃ R k M hCA hDB isOpen_univ isOpen_univ
      (hS.isOpen_compl.preimage continuous_subtypeVal)
      (hT.isOpen_compl.preimage continuous_subtypeVal) n m h)
  have hinjU : Function.Injective (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (unionComplPairIso S T).inv m) :=
    ((TopPair.singularCohomologyFunctor R k M m).mapIso
      (unionComplPairIso S T).op).symm.toLinearEquiv.injective
  have hinjI : Function.Injective (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (interComplPairIso S T).hom n) :=
    ((TopPair.singularCohomologyFunctor R k M n).mapIso
      (interComplPairIso S T).op).toLinearEquiv.injective
  rw [singularCohomologyComplMayerVietorisδ_def_apply R k M hS hT n m h] at ha
  obtain ⟨p, hp⟩ := hex _ (hinjU (ha.trans (map_zero _).symm))
  let HC := (TopPair.ofInclusion hCA).singularCohomology R k M n
  let HD := (TopPair.ofInclusion hDB).singularCohomology R k M n
  have hS' (y : HC) : TopPair.singularCohomologyMap (univComplPairIso S).hom n
      (TopPair.singularCohomologyMap (univComplPairIso S).inv n y) = y :=
    ((TopPair.singularCohomologyFunctor R k M n).mapIso (univComplPairIso S).op).inv_hom_id_apply y
  have hT' (y : HD) : TopPair.singularCohomologyMap (univComplPairIso T).hom n
      (TopPair.singularCohomologyMap (univComplPairIso T).inv n y) = y :=
    ((TopPair.singularCohomologyFunctor R k M n).mapIso (univComplPairIso T).op).inv_hom_id_apply y
  refine ⟨TopPair.singularCohomologyMap (univComplPairIso S).inv n ((biprod.fst : HC ⊞ HD ⟶ HC) p),
    TopPair.singularCohomologyMap (univComplPairIso T).inv n ((biprod.snd : HC ⊞ HD ⟶ HD) p),
    hinjI ?_⟩
  rw [map_sub, ← singularCohomologyMap_univComplPairIso_hom_inter_left_apply,
    ← singularCohomologyMap_univComplPairIso_hom_inter_right_apply, hS', hT']
  dsimp only at hp
  rw [← hp]
  conv_rhs => rw [← ModuleCat.biprod_inl_fst_add_inr_snd_apply p]
  simp [HC, HD, sub_eq_add_neg]

/-- Exactness of the Mayer–Vietoris sequence of the pairs `(X, X ∖ S)` and `(X, X ∖ T)` at
`Hᵐ(X, X ∖ (S ∩ T))`: a class restricting to zero in `Hᵐ(X, X ∖ S)` and in `Hᵐ(X, X ∖ T)` is in the
image of the connecting morphism. -/
lemma exists_singularCohomologyComplMayerVietorisδ_eq (hS : IsClosed S) (hT : IsClosed T)
    {n m : ℕ} (h : n + 1 = m) (z : (TopPair.ofSubset (S ∩ T)ᶜ).singularCohomology R k M m)
    (hzS : singularCohomologyComplRestrict R k M Set.inter_subset_left m z = 0)
    (hzT : singularCohomologyComplRestrict R k M Set.inter_subset_right m z = 0) :
    ∃ a, singularCohomologyComplMayerVietorisδ R k M hS hT n m h a = z := by
  have hCA : Sᶜ ⊆ (Set.univ : Set X) := Set.subset_univ _
  have hDB : Tᶜ ⊆ (Set.univ : Set X) := Set.subset_univ _
  have hex := (ShortComplex.moduleCat_exact_iff _).1
    (singularCohomologyPairMayerVietoris_exact₁ R k M hCA hDB isOpen_univ isOpen_univ
      (hS.isOpen_compl.preimage continuous_subtypeVal)
      (hT.isOpen_compl.preimage continuous_subtypeVal) n m h)
  obtain ⟨x, hx⟩ := hex (TopPair.singularCohomologyMap (unionComplPairIso S T).hom m z) (by
    dsimp only
    rw [← ModuleCat.biprod_inl_fst_add_inr_snd_apply
        (singularCohomologyPairMayerVietorisToBiprod R k M hCA hDB m _),
      singularCohomologyPairMayerVietorisToBiprod_fst_apply,
      singularCohomologyPairMayerVietorisToBiprod_snd_apply,
      singularCohomologyMap_unionComplPairIso_hom_union_left_apply,
      singularCohomologyMap_unionComplPairIso_hom_union_right_apply, hzS, hzT]
    simp)
  have hI (y) : TopPair.singularCohomologyMap (interComplPairIso S T).hom n
      (TopPair.singularCohomologyMap (interComplPairIso S T).inv n y) = y :=
    ((TopPair.singularCohomologyFunctor R k M n).mapIso (interComplPairIso S T).op).inv_hom_id_apply
      y
  have hU : TopPair.singularCohomologyMap (unionComplPairIso S T).inv m
      (TopPair.singularCohomologyMap (unionComplPairIso S T).hom m z) = z :=
    ((TopPair.singularCohomologyFunctor R k M m).mapIso (unionComplPairIso S T).op).hom_inv_id_apply
      z
  refine ⟨TopPair.singularCohomologyMap (interComplPairIso S T).inv n x, ?_⟩
  rw [singularCohomologyComplMayerVietorisδ_def_apply R k M hS hT n m h, hI]
  dsimp only at hx
  rw [hx, hU]

/-! ### Naturality -/

section Naturality

variable {Y : TopCat.{w}} {S' T' : Set Y}

variable (R k M) in
/-- **Naturality of the connecting morphism for complements of closed sets.** A map `f : X ⟶ Y`
carrying `X ∖ S` into `Y ∖ S'` and `X ∖ T` into `Y ∖ T'` commutes with the connecting morphisms,
where `(X, X ∖ (S ∪ T)) ⟶ (Y, Y ∖ (S' ∪ T'))` and `(X, X ∖ (S ∩ T)) ⟶ (Y, Y ∖ (S' ∩ T'))` are the
maps of pairs given by `f`. -/
@[reassoc]
lemma singularCohomologyComplMayerVietorisδ_naturality (hS : IsClosed S) (hT : IsClosed T)
    (hS' : IsClosed S') (hT' : IsClosed T') (f : X ⟶ Y) (hfS : Set.MapsTo f Sᶜ S'ᶜ)
    (hfT : Set.MapsTo f Tᶜ T'ᶜ) (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyComplMayerVietorisδ R k M hS' hT' n m h ≫
        TopPair.singularCohomologyMap (TopPair.ofSubsetMap (B := (S ∩ T)ᶜ) (B' := (S' ∩ T')ᶜ) f
          fun _ hx hST ↦ hx ⟨Classical.byContradiction fun hS ↦ hfS hS hST.1,
            Classical.byContradiction fun hT ↦ hfT hT hST.2⟩) m =
      TopPair.singularCohomologyMap (TopPair.ofSubsetMap (B := (S ∪ T)ᶜ) (B' := (S' ∪ T')ᶜ) f
          fun _ hx hST ↦ Or.elim hST (hfS fun hS ↦ hx (Or.inl hS))
            (hfT fun hT ↦ hx (Or.inr hT))) n ≫
        singularCohomologyComplMayerVietorisδ R k M hS hT n m h := by
  have hfI : Set.MapsTo f (S ∩ T)ᶜ (S' ∩ T')ᶜ := fun _ hx hST ↦
    hx ⟨Classical.byContradiction fun hS ↦ hfS hS hST.1,
      Classical.byContradiction fun hT ↦ hfT hT hST.2⟩
  have hfV : Set.MapsTo f (S ∪ T)ᶜ (S' ∪ T')ᶜ := fun _ hx hST ↦
    Or.elim hST (hfS fun hS ↦ hx (Or.inl hS)) (hfT fun hT ↦ hx (Or.inr hT))
  have hfU : Set.MapsTo f Set.univ Set.univ := Set.mapsTo_univ _ _
  have hnat := singularCohomologyPairMayerVietorisδ_naturality R k M
    (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ) isOpen_univ isOpen_univ
    (hS.isOpen_compl.preimage continuous_subtypeVal)
    (hT.isOpen_compl.preimage continuous_subtypeVal)
    (Set.subset_univ S'ᶜ) (Set.subset_univ T'ᶜ) isOpen_univ isOpen_univ
    (hS'.isOpen_compl.preimage continuous_subtypeVal)
    (hT'.isOpen_compl.preimage continuous_subtypeVal) f hfU hfU hfS hfT n m h
  -- the two squares of pairs relating the maps of pairs induced by `f`
  have hI : TopPair.ofInclusionMap
        (Set.inter_subset_inter (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ))
        (Set.inter_subset_inter (Set.subset_univ S'ᶜ) (Set.subset_univ T'ᶜ))
        ⟨(hfU.inter_inter hfU).restrict, f.hom.continuous.restrict (hfU.inter_inter hfU)⟩
        (fun _ hx ↦ hfS.inter_inter hfT hx) ≫ (interComplPairIso S' T').hom =
      (interComplPairIso S T).hom ≫ TopPair.ofSubsetMap f hfV :=
    TopPair.hom_ext_of_fst _ (ConcreteCategory.ext_apply fun x ↦
      (TopPair.ofInclusionIsoOfSubset_hom_fst_apply _ _ _).trans
        ((congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x)).trans
          ((congrArg f (TopPair.ofInclusionIsoOfSubset_hom_fst_apply _ _ x).symm).trans
            (TopPair.ofSubsetMap_fst_apply f hfV _).symm)))
  have hU : TopPair.ofInclusionMap
        (Set.union_subset_union (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ))
        (Set.union_subset_union (Set.subset_univ S'ᶜ) (Set.subset_univ T'ᶜ))
        ⟨(hfU.union_union hfU).restrict, f.hom.continuous.restrict (hfU.union_union hfU)⟩
        (fun _ hx ↦ hfS.union_union hfT hx) ≫ (unionComplPairIso S' T').hom =
      (unionComplPairIso S T).hom ≫ TopPair.ofSubsetMap f hfI :=
    TopPair.hom_ext_of_fst _ (ConcreteCategory.ext_apply fun x ↦
      (TopPair.ofInclusionIsoOfSubset_hom_fst_apply _ _ _).trans
        ((congrArg Subtype.val (TopPair.ofInclusionMap_fst_apply _ _ x)).trans
          ((congrArg f (TopPair.ofInclusionIsoOfSubset_hom_fst_apply _ _ x).symm).trans
            (TopPair.ofSubsetMap_fst_apply f hfI _).symm)))
  have hU' : TopPair.ofSubsetMap f hfI ≫ (unionComplPairIso S' T').inv =
      (unionComplPairIso S T).inv ≫ TopPair.ofInclusionMap
        (Set.union_subset_union (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ))
        (Set.union_subset_union (Set.subset_univ S'ᶜ) (Set.subset_univ T'ᶜ))
        ⟨(hfU.union_union hfU).restrict, f.hom.continuous.restrict (hfU.union_union hfU)⟩
        (fun _ hx ↦ hfS.union_union hfT hx) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, hU]
  simp only [singularCohomologyComplMayerVietorisδ_def, Category.assoc]
  rw [← TopPair.singularCohomologyMap_comp, hU', TopPair.singularCohomologyMap_comp,
    reassoc_of% hnat, ← TopPair.singularCohomologyMap_comp_assoc, hI,
    TopPair.singularCohomologyMap_comp_assoc]

end Naturality

variable (R k M) in
/-- **Naturality of the connecting morphism for complements of closed sets in inclusions.** For
closed sets `S ⊆ S'` and `T ⊆ T'`, the connecting morphisms commute with the restrictions
`Hⁿ(X, X ∖ (S ∪ T)) ⟶ Hⁿ(X, X ∖ (S' ∪ T'))` and `Hᵐ(X, X ∖ (S ∩ T)) ⟶ Hᵐ(X, X ∖ (S' ∩ T'))`. -/
@[reassoc, elementwise]
lemma singularCohomologyComplMayerVietorisδ_naturality_of_subset {S' T' : Set X}
    (hS : IsClosed S) (hT : IsClosed T) (hS' : IsClosed S') (hT' : IsClosed T') (hSS' : S ⊆ S')
    (hTT' : T ⊆ T') (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyComplMayerVietorisδ R k M hS hT n m h ≫
        singularCohomologyComplRestrict R k M (Set.inter_subset_inter hSS' hTT') m =
      singularCohomologyComplRestrict R k M (Set.union_subset_union hSS' hTT') n ≫
        singularCohomologyComplMayerVietorisδ R k M hS' hT' n m h :=
  singularCohomologyComplMayerVietorisδ_naturality R k M hS' hT' hS hT (𝟙 X)
    (mapsTo_id_compl hSS') (mapsTo_id_compl hTT') n m h

end TopCat
