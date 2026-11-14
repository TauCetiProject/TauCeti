/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.CompactSupport.MayerVietoris

/-!
# The connecting map of the Mayer–Vietoris sequence of cohomology with compact supports

Let `X` be a Hausdorff space covered by two open sets `U V : Opens X`, and write `Hⁿ_c(-)` for
singular cohomology with compact supports. This file constructs the connecting map
`Hⁿ_c(X) ⟶ Hᵐ_c(U ∩ V)`, `n + 1 = m`, of the Mayer–Vietoris sequence of cohomology with compact
supports
`⋯ ⟶ Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X) ⟶ Hᵐ_c(U ∩ V) ⟶ Hᵐ_c(U) ⊞ Hᵐ_c(V) ⟶ ⋯`
and proves that the sequence is exact at `Hⁿ_c(X)` and at `Hᵐ_c(U ∩ V)`. Together with
`TopCat.compactSupportCohomologyMayerVietoris_exact₂` this is the long exact sequence used in
Hatcher's proof of Lemma 3.36, the induction step of Poincaré duality for open subsets of a
manifold.

The construction follows Hatcher. For closed sets `S` and `T`, the Mayer–Vietoris sequence of the
pairs `(X, X ∖ S)` and `(X, X ∖ T)` has the connecting morphism
`Hⁿ(X, X ∖ (S ∪ T)) ⟶ Hᵐ(X, X ∖ (S ∩ T))` (`TopCat.singularCohomologyComplMayerVietorisδ`), the
connecting morphism `TopCat.singularCohomologyPairMayerVietorisδ` of the pairs `(univ, X ∖ S)` and
`(univ, X ∖ T)`, natural in `S` and `T`. For compact sets `K ⊆ U` and `L ⊆ V`, composing it with
excision `Hᵐ(X, X ∖ (K ∩ L)) ≅ Hᵐ(U ∩ V, U ∩ V ∖ (K ∩ L))` gives a map
`Hⁿ(X, X ∖ (K ∪ L)) ⟶ Hᵐ_c(U ∩ V)`. These maps are compatible with enlarging `K` and `L`, by
naturality, and every compact subset of `X` lies in some `K ∪ L` (`IsCompact.binary_compact_cover`),
so they define a map out of the colimit `Hⁿ_c(X)`. Exactness passes to the colimit and is checked
on elements, using the description of the elements of `Hⁿ_c` in
`TopCat.exists_compactSupportCohomologyι_eq` and `TopCat.compactSupportCohomologyι_eq_zero_iff`.

The signs follow `TopCat.compactSupportCohomologyMayerVietorisToBiprod`, whose components are the
extension to `U` and minus the extension to `V`. The connecting map carries no extra sign: the
signs of the first two maps do not affect the kernels and images at `Hⁿ_c(X)` and `Hᵐ_c(U ∩ V)`.

## Main definitions and results

* `TopCat.singularCohomologyComplMayerVietorisδ`: the connecting morphism
  `Hⁿ(X, X ∖ (S ∪ T)) ⟶ Hᵐ(X, X ∖ (S ∩ T))` for closed `S` and `T`, with its naturality
  `TopCat.singularCohomologyComplMayerVietorisδ_naturality`, the vanishing of the composites with
  the restrictions, and exactness at both ends
  (`TopCat.exists_sub_eq_of_singularCohomologyComplMayerVietorisδ_eq_zero`,
  `TopCat.exists_singularCohomologyComplMayerVietorisδ_eq`).
* `TopCat.compactSupportCohomologyMayerVietorisδ`: the connecting map `Hⁿ_c(X) ⟶ Hᵐ_c(U ∩ V)`,
  characterized on `Hⁿ(X, X ∖ C)` by
  `TopCat.compactSupportCohomologyι_compactSupportCohomologyMayerVietorisδ`.
* `TopCat.compactSupportCohomologyMayerVietorisFromBiprod_δ` and
  `TopCat.compactSupportCohomologyMayerVietorisδ_toBiprod`: the composites with the neighbouring
  maps vanish.
* `TopCat.compactSupportCohomologyMayerVietoris_exact₃` and
  `TopCat.compactSupportCohomologyMayerVietoris_exact₁`: exactness at `Hⁿ_c(X)` and at
  `Hᵐ_c(U ∩ V)`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.3, the Mayer–Vietoris sequence `⋯ ⟶ Hⁿ_c(U ∩ V) ⟶ Hⁿ_c(U) ⊕ Hⁿ_c(V) ⟶ Hⁿ_c(X) ⟶
  Hⁿ⁺¹_c(U ∩ V) ⟶ ⋯` in the proof of Lemma 3.36.
-/

public section

noncomputable section

open CategoryTheory Limits TopologicalSpace Topology Opens

universe v u

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasCoproducts.{v} C] [Abelian C] {R : C}
  {k : Type v} [Ring k] [Linear k C] {M : C} {X : TopCat.{v}}

/-! ### Mayer–Vietoris for the complements of two closed sets -/

section Compl

/-- The pair `(univ, X ∖ S)` is the pair `(X, X ∖ S)`. -/
private abbrev complIso (S : Set X) :
    TopPair.ofInclusion (Set.subset_univ Sᶜ) ≅ TopPair.ofSubset Sᶜ :=
  TopPair.ofInclusionIsoOfSubset _ Set.mem_univ fun _ ↦ Iff.rfl

/-- The pair `(univ ∩ univ, (X ∖ S) ∩ (X ∖ T))` is the pair `(X, X ∖ (S ∪ T))`. -/
private abbrev complInterIso (S T : Set X) :
    TopPair.ofInclusion (Set.inter_subset_inter (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)) ≅
      TopPair.ofSubset (S ∪ T)ᶜ :=
  TopPair.ofInclusionIsoOfSubset _ (fun x ↦ Set.mem_inter (Set.mem_univ x) (Set.mem_univ x))
    fun _ ↦ by rw [Set.compl_union]

/-- The pair `(univ ∪ univ, (X ∖ S) ∪ (X ∖ T))` is the pair `(X, X ∖ (S ∩ T))`. -/
private abbrev complUnionIso (S T : Set X) :
    TopPair.ofInclusion (Set.union_subset_union (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)) ≅
      TopPair.ofSubset (S ∩ T)ᶜ :=
  TopPair.ofInclusionIsoOfSubset _ (fun x ↦ Set.mem_union_left _ (Set.mem_univ x))
    fun _ ↦ by rw [Set.compl_inter]

private lemma isOpen_univ_preimage_val :
    IsOpen ((↑) ⁻¹' (Set.univ : Set X) : Set ↥((Set.univ : Set X) ∪ Set.univ)) := by
  simp

variable (R k M) in
/-- The connecting morphism `Hⁿ(X, X ∖ (S ∪ T)) ⟶ Hᵐ(X, X ∖ (S ∩ T))`, `n + 1 = m`, of the
Mayer–Vietoris sequence of the pairs `(X, X ∖ S)` and `(X, X ∖ T)` for closed sets `S` and `T`:
the connecting morphism `TopCat.singularCohomologyPairMayerVietorisδ` of the pairs
`(univ, X ∖ S)` and `(univ, X ∖ T)`, transported along the identifications of `(univ, X ∖ S)`
with `(X, X ∖ S)`. -/
def singularCohomologyComplMayerVietorisδ {S T : Set X} (hS : IsClosed S) (hT : IsClosed T)
    (n m : ℕ) (h : n + 1 = m := by lia) :
    (TopPair.ofSubset (S ∪ T)ᶜ).singularCohomology R k M n ⟶
      (TopPair.ofSubset (S ∩ T)ᶜ).singularCohomology R k M m :=
  TopPair.singularCohomologyMap (complInterIso S T).hom n ≫
    singularCohomologyPairMayerVietorisδ R k M (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)
      isOpen_univ_preimage_val isOpen_univ_preimage_val
      (hS.isOpen_compl.preimage continuous_subtype_val)
      (hT.isOpen_compl.preimage continuous_subtype_val) n m h ≫
    TopPair.singularCohomologyMap (complUnionIso S T).inv m

/-- Two equal composites of maps of pairs induce equal maps on cohomology classes. -/
private lemma singularCohomologyMap_apply_eq_of_comp_eq {P Q P' Q' : TopPair.{v}} {f : P ⟶ Q}
    {g : Q ⟶ Q'} {f' : P ⟶ P'} {g' : P' ⟶ Q'} (hfg : f ≫ g = f' ≫ g') {n : ℕ}
    (y : Q'.singularCohomology R k M n) :
    TopPair.singularCohomologyMap f n (TopPair.singularCohomologyMap g n y) =
      TopPair.singularCohomologyMap f' n (TopPair.singularCohomologyMap g' n y) := by
  simp only [← TopPair.singularCohomologyMap_comp_apply, hfg]

private lemma singularCohomologyMap_hom_inv_apply {P Q : TopPair.{v}} (e : P ≅ Q) {n : ℕ}
    (y : P.singularCohomology R k M n) :
    TopPair.singularCohomologyMap e.hom n (TopPair.singularCohomologyMap e.inv n y) = y := by
  rw [← TopPair.singularCohomologyMap_comp_apply, e.hom_inv_id,
    TopPair.singularCohomologyMap_id, ModuleCat.id_apply]

private lemma singularCohomologyMap_inv_hom_apply {P Q : TopPair.{v}} (e : P ≅ Q) {n : ℕ}
    (y : Q.singularCohomology R k M n) :
    TopPair.singularCohomologyMap e.inv n (TopPair.singularCohomologyMap e.hom n y) = y := by
  rw [← TopPair.singularCohomologyMap_comp_apply, e.inv_hom_id,
    TopPair.singularCohomologyMap_id, ModuleCat.id_apply]

private lemma singularCohomologyMap_hom_injective {P Q : TopPair.{v}} (e : P ≅ Q) (n : ℕ) :
    Function.Injective (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) e.hom n) :=
  Function.LeftInverse.injective (singularCohomologyMap_inv_hom_apply e)

private lemma singularCohomologyMap_inv_injective {P Q : TopPair.{v}} (e : P ≅ Q) (n : ℕ) :
    Function.Injective (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) e.inv n) :=
  Function.LeftInverse.injective (singularCohomologyMap_hom_inv_apply e)

section PairApply

variable {A B C₁ D₁ : Set X} (hCA : C₁ ⊆ A) (hDB : D₁ ⊆ B) {n : ℕ}

private lemma singularCohomologyPairMayerVietorisFromBiprod_inl_apply
    (y : (TopPair.ofInclusion hCA).singularCohomology R k M n) :
    singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n
        ((biprod.inl : _ ⟶ _ ⊞ (TopPair.ofInclusion hDB).singularCohomology R k M n) y) =
      TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hCA
        (ContinuousMap.inclusion Set.inter_subset_left) fun _ hx ↦ Set.inter_subset_left hx) n
          y := by
  rw [← ConcreteCategory.comp_apply, inl_singularCohomologyPairMayerVietorisFromBiprod]

private lemma singularCohomologyPairMayerVietorisFromBiprod_inr_apply
    (y : (TopPair.ofInclusion hDB).singularCohomology R k M n) :
    singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n
        ((biprod.inr : _ ⟶ (TopPair.ofInclusion hCA).singularCohomology R k M n ⊞ _) y) =
      -TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.inter_subset_inter hCA hDB) hDB
        (ContinuousMap.inclusion Set.inter_subset_right) fun _ hx ↦ Set.inter_subset_right hx) n
          y := by
  rw [← ConcreteCategory.comp_apply, inr_singularCohomologyPairMayerVietorisFromBiprod]
  rfl

private lemma singularCohomologyPairMayerVietorisToBiprod_fst_apply
    (z : (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).singularCohomology R k M n) :
    (biprod.fst : _ ⊞ (TopPair.ofInclusion hDB).singularCohomology R k M n ⟶ _)
        (singularCohomologyPairMayerVietorisToBiprod R k M hCA hDB n z) =
      TopPair.singularCohomologyMap (TopPair.ofInclusionMap hCA (Set.union_subset_union hCA hDB)
        (ContinuousMap.inclusion Set.subset_union_left) fun _ hx ↦ Set.subset_union_left hx) n
          z := by
  rw [← ConcreteCategory.comp_apply, singularCohomologyPairMayerVietorisToBiprod_fst]

private lemma singularCohomologyPairMayerVietorisToBiprod_snd_apply
    (z : (TopPair.ofInclusion (Set.union_subset_union hCA hDB)).singularCohomology R k M n) :
    (biprod.snd : (TopPair.ofInclusion hCA).singularCohomology R k M n ⊞ _ ⟶ _)
        (singularCohomologyPairMayerVietorisToBiprod R k M hCA hDB n z) =
      TopPair.singularCohomologyMap (TopPair.ofInclusionMap hDB (Set.union_subset_union hCA hDB)
        (ContinuousMap.inclusion Set.subset_union_right) fun _ hx ↦ Set.subset_union_right hx) n
          z := by
  rw [← ConcreteCategory.comp_apply, singularCohomologyPairMayerVietorisToBiprod_snd]

variable (hA : IsOpen ((↑) ⁻¹' A : Set ↥(A ∪ B))) (hB : IsOpen ((↑) ⁻¹' B : Set ↥(A ∪ B)))
  (hC : IsOpen ((↑) ⁻¹' C₁ : Set ↥(C₁ ∪ D₁))) (hD : IsOpen ((↑) ⁻¹' D₁ : Set ↥(C₁ ∪ D₁)))

private lemma singularCohomologyPairMayerVietorisδ_fromBiprod_apply {m : ℕ} (h : n + 1 = m)
    (p : ((TopPair.ofInclusion hCA).singularCohomology R k M n ⊞
      (TopPair.ofInclusion hDB).singularCohomology R k M n : ModuleCat.{v} k)) :
    singularCohomologyPairMayerVietorisδ R k M hCA hDB hA hB hC hD n m h
      (singularCohomologyPairMayerVietorisFromBiprod R k M hCA hDB n p) = 0 := by
  rw [← ConcreteCategory.comp_apply,
    singularCohomologyPairMayerVietorisFromBiprod_δ R k M hCA hDB hA hB hC hD n m h]
  rfl

private lemma singularCohomologyPairMayerVietorisToBiprod_δ_apply {m : ℕ} (h : n + 1 = m)
    (x : (TopPair.ofInclusion (Set.inter_subset_inter hCA hDB)).singularCohomology R k M n) :
    singularCohomologyPairMayerVietorisToBiprod R k M hCA hDB m
      (singularCohomologyPairMayerVietorisδ R k M hCA hDB hA hB hC hD n m h x) = 0 := by
  rw [← ConcreteCategory.comp_apply,
    singularCohomologyPairMayerVietorisδ_toBiprod R k M hCA hDB hA hB hC hD n m h]
  rfl

end PairApply

variable {S T : Set X}

/-- The restriction from `(univ, X ∖ S)` to `(univ ∩ univ, (X ∖ S) ∩ (X ∖ T))`, under the
identifications with `(X, X ∖ S)` and `(X, X ∖ (S ∪ T))`, is the restriction
`Hⁿ(X, X ∖ S) ⟶ Hⁿ(X, X ∖ (S ∪ T))`. -/
private lemma singularCohomologyMap_inter_left_apply {n : ℕ}
    (b : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (TopPair.ofInclusionMap
        (Set.inter_subset_inter (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)) (Set.subset_univ Sᶜ)
        (ContinuousMap.inclusion Set.inter_subset_left) fun _ hx ↦ Set.inter_subset_left hx) n
        (TopPair.singularCohomologyMap (complIso S).hom n b) =
      TopPair.singularCohomologyMap (complInterIso S T).hom n
        (singularCohomologyComplRestrict R k M Set.subset_union_left n b) :=
  singularCohomologyMap_apply_eq_of_comp_eq
    (TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _
      (mapsTo_id_compl Set.subset_union_left)) b

private lemma singularCohomologyMap_inter_right_apply {n : ℕ}
    (c : (TopPair.ofSubset Tᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (TopPair.ofInclusionMap
        (Set.inter_subset_inter (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)) (Set.subset_univ Tᶜ)
        (ContinuousMap.inclusion Set.inter_subset_right) fun _ hx ↦ Set.inter_subset_right hx) n
        (TopPair.singularCohomologyMap (complIso T).hom n c) =
      TopPair.singularCohomologyMap (complInterIso S T).hom n
        (singularCohomologyComplRestrict R k M Set.subset_union_right n c) :=
  singularCohomologyMap_apply_eq_of_comp_eq
    (TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _
      (mapsTo_id_compl Set.subset_union_right)) c

/-- The restriction from `(univ ∪ univ, (X ∖ S) ∪ (X ∖ T))` to `(univ, X ∖ S)`, under the
identifications with `(X, X ∖ (S ∩ T))` and `(X, X ∖ S)`, is the restriction
`Hⁿ(X, X ∖ (S ∩ T)) ⟶ Hⁿ(X, X ∖ S)`. -/
private lemma singularCohomologyMap_union_left_apply {n : ℕ}
    (z : (TopPair.ofSubset (S ∩ T)ᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.subset_univ Sᶜ)
        (Set.union_subset_union (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ))
        (ContinuousMap.inclusion Set.subset_union_left) fun _ hx ↦ Set.subset_union_left hx) n
        (TopPair.singularCohomologyMap (complUnionIso S T).hom n z) =
      TopPair.singularCohomologyMap (complIso S).hom n
        (singularCohomologyComplRestrict R k M Set.inter_subset_left n z) :=
  singularCohomologyMap_apply_eq_of_comp_eq
    (TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _
      (mapsTo_id_compl Set.inter_subset_left)) z

private lemma singularCohomologyMap_union_right_apply {n : ℕ}
    (z : (TopPair.ofSubset (S ∩ T)ᶜ).singularCohomology R k M n) :
    TopPair.singularCohomologyMap (TopPair.ofInclusionMap (Set.subset_univ Tᶜ)
        (Set.union_subset_union (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ))
        (ContinuousMap.inclusion Set.subset_union_right) fun _ hx ↦ Set.subset_union_right hx) n
        (TopPair.singularCohomologyMap (complUnionIso S T).hom n z) =
      TopPair.singularCohomologyMap (complIso T).hom n
        (singularCohomologyComplRestrict R k M Set.inter_subset_right n z) :=
  singularCohomologyMap_apply_eq_of_comp_eq
    (TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _
      (mapsTo_id_compl Set.inter_subset_right)) z

private lemma singularCohomologyComplMayerVietorisδ_apply (hS : IsClosed S) (hT : IsClosed T)
    {n m : ℕ} (h : n + 1 = m) (a : (TopPair.ofSubset (S ∪ T)ᶜ).singularCohomology R k M n) :
    singularCohomologyComplMayerVietorisδ R k M hS hT n m h a =
      TopPair.singularCohomologyMap (complUnionIso S T).inv m
        (singularCohomologyPairMayerVietorisδ R k M (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ)
          isOpen_univ_preimage_val isOpen_univ_preimage_val
          (hS.isOpen_compl.preimage continuous_subtype_val)
          (hT.isOpen_compl.preimage continuous_subtype_val) n m h
          (TopPair.singularCohomologyMap (complInterIso S T).hom n a)) :=
  rfl

/-- The connecting morphism vanishes on classes restricted from `Hⁿ(X, X ∖ S)`. -/
lemma singularCohomologyComplMayerVietorisδ_restrict_left (hS : IsClosed S) (hT : IsClosed T)
    {n m : ℕ} (h : n + 1 = m) (b : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    singularCohomologyComplMayerVietorisδ R k M hS hT n m h
      (singularCohomologyComplRestrict R k M Set.subset_union_left n b) = 0 := by
  rw [singularCohomologyComplMayerVietorisδ_apply, ← singularCohomologyMap_inter_left_apply,
    ← singularCohomologyPairMayerVietorisFromBiprod_inl_apply _ (Set.subset_univ Tᶜ),
    singularCohomologyPairMayerVietorisδ_fromBiprod_apply, map_zero]

/-- The connecting morphism vanishes on classes restricted from `Hⁿ(X, X ∖ T)`. -/
lemma singularCohomologyComplMayerVietorisδ_restrict_right (hS : IsClosed S) (hT : IsClosed T)
    {n m : ℕ} (h : n + 1 = m) (c : (TopPair.ofSubset Tᶜ).singularCohomology R k M n) :
    singularCohomologyComplMayerVietorisδ R k M hS hT n m h
      (singularCohomologyComplRestrict R k M Set.subset_union_right n c) = 0 := by
  rw [singularCohomologyComplMayerVietorisδ_apply, ← singularCohomologyMap_inter_right_apply,
    ← neg_neg (TopPair.singularCohomologyMap _ n _),
    ← singularCohomologyPairMayerVietorisFromBiprod_inr_apply (Set.subset_univ Sᶜ), map_neg,
    singularCohomologyPairMayerVietorisδ_fromBiprod_apply, neg_zero, map_zero]

/-- The connecting morphism followed by the restriction to `Hᵐ(X, X ∖ S)` vanishes. -/
lemma singularCohomologyComplRestrict_singularCohomologyComplMayerVietorisδ_left
    (hS : IsClosed S) (hT : IsClosed T) {n m : ℕ} (h : n + 1 = m)
    (a : (TopPair.ofSubset (S ∪ T)ᶜ).singularCohomology R k M n) :
    singularCohomologyComplRestrict R k M Set.inter_subset_left m
      (singularCohomologyComplMayerVietorisδ R k M hS hT n m h a) = 0 := by
  apply singularCohomologyMap_hom_injective (complIso S)
  rw [← singularCohomologyMap_union_left_apply, singularCohomologyComplMayerVietorisδ_apply,
    singularCohomologyMap_hom_inv_apply]
  rw [← singularCohomologyPairMayerVietorisToBiprod_fst_apply _ (Set.subset_univ Tᶜ),
    singularCohomologyPairMayerVietorisToBiprod_δ_apply, map_zero, map_zero]

/-- The connecting morphism followed by the restriction to `Hᵐ(X, X ∖ T)` vanishes. -/
lemma singularCohomologyComplRestrict_singularCohomologyComplMayerVietorisδ_right
    (hS : IsClosed S) (hT : IsClosed T) {n m : ℕ} (h : n + 1 = m)
    (a : (TopPair.ofSubset (S ∪ T)ᶜ).singularCohomology R k M n) :
    singularCohomologyComplRestrict R k M Set.inter_subset_right m
      (singularCohomologyComplMayerVietorisδ R k M hS hT n m h a) = 0 := by
  apply singularCohomologyMap_hom_injective (complIso T)
  rw [← singularCohomologyMap_union_right_apply, singularCohomologyComplMayerVietorisδ_apply,
    singularCohomologyMap_hom_inv_apply]
  rw [← singularCohomologyPairMayerVietorisToBiprod_snd_apply (Set.subset_univ Sᶜ),
    singularCohomologyPairMayerVietorisToBiprod_δ_apply, map_zero, map_zero]

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
    (singularCohomologyPairMayerVietoris_exact₃ R k M hCA hDB isOpen_univ_preimage_val
      isOpen_univ_preimage_val (hS.isOpen_compl.preimage continuous_subtype_val)
      (hT.isOpen_compl.preimage continuous_subtype_val) n m h)
  rw [singularCohomologyComplMayerVietorisδ_apply] at ha
  obtain ⟨p, hp⟩ := hex _ (singularCohomologyMap_inv_injective (complUnionIso S T) m
    (ha.trans (map_zero _).symm))
  let HC := (TopPair.ofInclusion hCA).singularCohomology R k M n
  let HD := (TopPair.ofInclusion hDB).singularCohomology R k M n
  refine ⟨TopPair.singularCohomologyMap (complIso S).inv n ((biprod.fst : HC ⊞ HD ⟶ HC) p),
    TopPair.singularCohomologyMap (complIso T).inv n ((biprod.snd : HC ⊞ HD ⟶ HD) p),
    singularCohomologyMap_hom_injective (complInterIso S T) n ?_⟩
  rw [map_sub, ← singularCohomologyMap_inter_left_apply, ← singularCohomologyMap_inter_right_apply,
    singularCohomologyMap_hom_inv_apply, singularCohomologyMap_hom_inv_apply]
  dsimp only at hp
  rw [← hp]
  conv_rhs => rw [← ModuleCat.biprod_inl_fst_add_inr_snd_apply p]
  rw [map_add,
    singularCohomologyPairMayerVietorisFromBiprod_inl_apply,
    singularCohomologyPairMayerVietorisFromBiprod_inr_apply, sub_eq_add_neg]

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
    (singularCohomologyPairMayerVietoris_exact₁ R k M hCA hDB isOpen_univ_preimage_val
      isOpen_univ_preimage_val (hS.isOpen_compl.preimage continuous_subtype_val)
      (hT.isOpen_compl.preimage continuous_subtype_val) n m h)
  obtain ⟨x, hx⟩ := hex (TopPair.singularCohomologyMap (complUnionIso S T).hom m z) (by
    dsimp only
    rw [← ModuleCat.biprod_inl_fst_add_inr_snd_apply
        (singularCohomologyPairMayerVietorisToBiprod R k M hCA hDB m _),
      singularCohomologyPairMayerVietorisToBiprod_fst_apply,
      singularCohomologyPairMayerVietorisToBiprod_snd_apply,
      singularCohomologyMap_union_left_apply, singularCohomologyMap_union_right_apply, hzS, hzT]
    simp)
  refine ⟨TopPair.singularCohomologyMap (complInterIso S T).inv n x, ?_⟩
  rw [singularCohomologyComplMayerVietorisδ_apply, singularCohomologyMap_hom_inv_apply]
  dsimp only at hx
  rw [hx, singularCohomologyMap_inv_hom_apply]

/-- **Naturality of the connecting morphism for complements of closed sets.** For closed sets
`S ⊆ S'` and `T ⊆ T'`, the connecting morphisms commute with the restrictions
`Hⁿ(X, X ∖ (S ∪ T)) ⟶ Hⁿ(X, X ∖ (S' ∪ T'))` and `Hᵐ(X, X ∖ (S ∩ T)) ⟶ Hᵐ(X, X ∖ (S' ∩ T'))`. -/
@[reassoc]
lemma singularCohomologyComplMayerVietorisδ_naturality {S' T' : Set X} (hS : IsClosed S)
    (hT : IsClosed T) (hS' : IsClosed S') (hT' : IsClosed T') (hSS' : S ⊆ S') (hTT' : T ⊆ T')
    (n m : ℕ) (h : n + 1 = m := by lia) :
    singularCohomologyComplMayerVietorisδ R k M hS hT n m h ≫
        singularCohomologyComplRestrict R k M (Set.inter_subset_inter hSS' hTT') m =
      singularCohomologyComplRestrict R k M (Set.union_subset_union hSS' hTT') n ≫
        singularCohomologyComplMayerVietorisδ R k M hS' hT' n m h := by
  have hnat := singularCohomologyPairMayerVietorisδ_naturality_of_subset R k M
    (Set.subset_univ S'ᶜ) (Set.subset_univ T'ᶜ) isOpen_univ_preimage_val isOpen_univ_preimage_val
    (hS'.isOpen_compl.preimage continuous_subtype_val)
    (hT'.isOpen_compl.preimage continuous_subtype_val)
    (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ) isOpen_univ_preimage_val isOpen_univ_preimage_val
    (hS.isOpen_compl.preimage continuous_subtype_val)
    (hT.isOpen_compl.preimage continuous_subtype_val) subset_rfl subset_rfl
    (Set.compl_subset_compl.2 hSS') (Set.compl_subset_compl.2 hTT') n m h
  have hU : TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl (Set.inter_subset_inter hSS' hTT')) ≫
      (complUnionIso S T).inv = (complUnionIso S' T').inv ≫ TopPair.ofInclusionMap
        (Set.union_subset_union (Set.subset_univ S'ᶜ) (Set.subset_univ T'ᶜ))
        (Set.union_subset_union (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ))
        (ContinuousMap.inclusion (Set.union_subset_union subset_rfl subset_rfl))
        fun _ hx ↦ Set.union_subset_union (Set.compl_subset_compl.2 hSS')
          (Set.compl_subset_compl.2 hTT') hx := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    exact (TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _ _).symm
  have hI : TopPair.ofInclusionMap
        (Set.inter_subset_inter (Set.subset_univ S'ᶜ) (Set.subset_univ T'ᶜ))
        (Set.inter_subset_inter (Set.subset_univ Sᶜ) (Set.subset_univ Tᶜ))
        (ContinuousMap.inclusion (Set.inter_subset_inter subset_rfl subset_rfl))
        (fun _ hx ↦ Set.inter_subset_inter (Set.compl_subset_compl.2 hSS')
          (Set.compl_subset_compl.2 hTT') hx) ≫ (complInterIso S T).hom =
      (complInterIso S' T').hom ≫
        TopPair.ofSubsetMap (𝟙 X) (mapsTo_id_compl (Set.union_subset_union hSS' hTT')) :=
    TopPair.ofInclusionMap_inclusion_comp_ofInclusionIsoOfSubset_hom _ _ _ _ _ _ _
  simp only [singularCohomologyComplMayerVietorisδ, Category.assoc]
  rw [← TopPair.singularCohomologyMap_comp, hU, TopPair.singularCohomologyMap_comp,
    reassoc_of% hnat, ← TopPair.singularCohomologyMap_comp_assoc, hI,
    TopPair.singularCohomologyMap_comp_assoc]

end Compl

/-! ### Compactly supported classes on an open set from classes supported in it -/

section Restrict

/-- Restricting along the identity of `X` from `X ∖ S` to itself is the identity. -/
private lemma singularCohomologyComplRestrict_self_apply {S : Set X} (h : S ⊆ S) {n : ℕ}
    (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    singularCohomologyComplRestrict R k M h n a = a := by
  rw [singularCohomologyComplRestrict, TopPair.ofSubsetMap_id, TopPair.singularCohomologyMap_id,
    ModuleCat.id_apply]

/-- The maps into cohomology with compact supports are compatible with restriction. -/
private lemma compactSupportCohomologyι_singularCohomologyComplRestrict {K L : Compacts X}
    (h : (K : Set X) ⊆ L) {n : ℕ} (a : (TopPair.ofSubset (K : Set X)ᶜ).singularCohomology R k M n) :
    compactSupportCohomologyι n L (singularCohomologyComplRestrict R k M h n a) =
      compactSupportCohomologyι n K a :=
  singularCohomologyMap_comp_compactSupportCohomologyι_apply n h a

variable {Y : TopCat.{v}} {f : Y ⟶ X} (hf : IsOpenEmbedding f)

/-- The preimage of a compact set `S` lying in the image of an open embedding `f`. -/
private def preimageCompacts {S : Set X} (hS : IsCompact S) (hSf : S ⊆ Set.range f) :
    Compacts Y :=
  ⟨f ⁻¹' S, hf.isInducing.isCompact_preimage' hS hSf⟩

private lemma subset_preimageCompacts_map {S : Set X} (hS : IsCompact S)
    (hSf : S ⊆ Set.range f) :
    S ⊆ ((preimageCompacts hf hS hSf).map f f.hom.continuous : Set X) := fun x hx ↦ by
  obtain ⟨u, rfl⟩ := hSf hx
  exact ⟨u, hx, rfl⟩

/-- Restricting a class of `Hⁿ(X, X ∖ S)` along `f` to `Hⁿ(Y, Y ∖ K)` and passing to `Hⁿ_c(Y)`
does not depend on the compact `K ⊆ Y` with `S ⊆ f(K)`. -/
private lemma compactSupportCohomologyι_singularCohomologyComplCompactsMap_restrict_eq
    {S : Set X} {K L : Compacts Y} (hK : S ⊆ (K.map f f.hom.continuous : Set X))
    (hL : S ⊆ (L.map f f.hom.continuous : Set X)) {n : ℕ}
    (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    compactSupportCohomologyι n K (singularCohomologyComplCompactsMap hf.injective K n
        (singularCohomologyComplRestrict R k M hK n a)) =
      compactSupportCohomologyι n L (singularCohomologyComplCompactsMap hf.injective L n
        (singularCohomologyComplRestrict R k M hL n a)) := by
  have key {K L : Compacts Y} (hKL : K ≤ L) (hK : S ⊆ (K.map f f.hom.continuous : Set X))
      (hL : S ⊆ (L.map f f.hom.continuous : Set X)) :
      compactSupportCohomologyι n K (singularCohomologyComplCompactsMap hf.injective K n
          (singularCohomologyComplRestrict R k M hK n a)) =
        compactSupportCohomologyι n L (singularCohomologyComplCompactsMap hf.injective L n
          (singularCohomologyComplRestrict R k M hL n a)) := by
    rw [←
      compactSupportCohomologyι_singularCohomologyComplCompactsMap_singularCohomologyComplRestrict
        hf.injective hKL, singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict]
    exact Compacts.map_mono f f.hom.continuous hKL
  rw [key le_sup_left hK (hK.trans (Compacts.map_mono f f.hom.continuous le_sup_left)),
    key le_sup_right hL (hL.trans (Compacts.map_mono f f.hom.continuous le_sup_right))]

/-- The class of `Hⁿ_c(Y)` of a class of `Hⁿ(X, X ∖ S)`, for a compact `S` in the image of an
open embedding `f : Y ⟶ X`: restrict along `f` to `Hⁿ(Y, Y ∖ f⁻¹(S))`. -/
private def restrictι {S : Set X} (hS : IsCompact S) (hSf : S ⊆ Set.range f) (n : ℕ) :
    (TopPair.ofSubset Sᶜ).singularCohomology R k M n ⟶ Y.compactSupportCohomology R k M n :=
  singularCohomologyComplRestrict R k M (subset_preimageCompacts_map hf hS hSf) n ≫
    singularCohomologyComplCompactsMap hf.injective _ n ≫ compactSupportCohomologyι n _

private lemma restrictι_apply {S : Set X} (hS : IsCompact S) (hSf : S ⊆ Set.range f)
    {K : Compacts Y} (hK : S ⊆ (K.map f f.hom.continuous : Set X)) {n : ℕ}
    (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    restrictι hf hS hSf n a = compactSupportCohomologyι n K
      (singularCohomologyComplCompactsMap hf.injective K n
        (singularCohomologyComplRestrict R k M hK n a)) := by
  rw [restrictι, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
  exact compactSupportCohomologyι_singularCohomologyComplCompactsMap_restrict_eq hf _ _ a

/-- `restrictι` is compatible with enlarging the compact set. -/
private lemma restrictι_singularCohomologyComplRestrict {S T : Set X} (hS : IsCompact S)
    (hSf : S ⊆ Set.range f) (hT : IsCompact T) (hTf : T ⊆ Set.range f) (hST : S ⊆ T) {n : ℕ}
    (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    restrictι hf hT hTf n (singularCohomologyComplRestrict R k M hST n a) =
      restrictι hf hS hSf n a := by
  rw [restrictι_apply hf hT hTf (subset_preimageCompacts_map hf hT hTf),
    restrictι_apply hf hS hSf (hST.trans (subset_preimageCompacts_map hf hT hTf)),
    singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict]

/-- Every class with compact support on `Y` is a `restrictι`. -/
private lemma exists_restrictι_eq [T2Space X] {n : ℕ} (y : Y.compactSupportCohomology R k M n) :
    ∃ (S : Set X) (hS : IsCompact S) (hSf : S ⊆ Set.range f)
      (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n), restrictι hf hS hSf n a = y := by
  obtain ⟨K, -, y, rfl⟩ := exists_compactSupportCohomologyι_eq y ⊥
  refine ⟨K.map f f.hom.continuous, (K.map f f.hom.continuous).isCompact,
    fun _ ⟨u, _, hu⟩ ↦ ⟨u, hu⟩, (singularCohomologyComplCompactsMapIso R k M hf K n).inv y, ?_⟩
  refine (restrictι_apply hf _ _ (K := K) subset_rfl _).trans ?_
  have hy := (singularCohomologyComplCompactsMapIso R k M hf K n).inv_hom_id_apply y
  rw [singularCohomologyComplCompactsMapIso_hom] at hy
  rw [singularCohomologyComplRestrict_self_apply, hy]

/-- A `restrictι` vanishes only if the class vanishes on a larger compact set in the image. -/
private lemma exists_singularCohomologyComplRestrict_eq_zero_of_restrictι_eq_zero [T2Space X]
    {S : Set X} (hS : IsCompact S) (hSf : S ⊆ Set.range f) {n : ℕ}
    (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) (ha : restrictι hf hS hSf n a = 0) :
    ∃ (T : Set X) (_ : IsCompact T) (_ : T ⊆ Set.range f) (hST : S ⊆ T),
      singularCohomologyComplRestrict R k M hST n a = 0 := by
  rw [restrictι_apply hf hS hSf (subset_preimageCompacts_map hf hS hSf),
    compactSupportCohomologyι_eq_zero_iff] at ha
  obtain ⟨L, hKL, hL⟩ := ha
  refine ⟨L.map f f.hom.continuous, (L.map f f.hom.continuous).isCompact,
    fun _ ⟨u, _, hu⟩ ↦ ⟨u, hu⟩,
    (subset_preimageCompacts_map hf hS hSf).trans (Compacts.map_mono f f.hom.continuous hKL), ?_⟩
  apply (singularCohomologyComplCompactsMapIso R k M hf L n).toLinearEquiv.injective
  have hnat := ConcreteCategory.congr_hom (singularCohomologyComplCompactsMapIso_hom_naturality
    (R := R) (k := k) (M := M) hf hKL n)
    (singularCohomologyComplRestrict R k M (subset_preimageCompacts_map hf hS hSf) n a)
  simp only [ConcreteCategory.comp_apply, singularCohomologyComplCompactsMapIso_hom] at hnat
  rw [map_zero]
  change (singularCohomologyComplCompactsMapIso R k M hf L n).hom _ = 0
  rw [singularCohomologyComplCompactsMapIso_hom,
    ← singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict
    (subset_preimageCompacts_map hf hS hSf) (Compacts.map_mono f f.hom.continuous hKL)]
  exact hnat.trans hL

/-- `restrictι` followed by extension along `f` is the map into `Hⁿ_c(X)`. -/
private lemma compactSupportCohomologyExtend_restrictι [T2Space X] {S : Set X}
    (hS : IsCompact S) (hSf : S ⊆ Set.range f) {n : ℕ}
    (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    compactSupportCohomologyExtend hf n (restrictι hf hS hSf n a) =
      compactSupportCohomologyι n ⟨S, hS⟩ a := by
  have hext := ConcreteCategory.congr_hom
    (singularCohomologyMap_comp_compactSupportCohomologyι_comp_extend (R := R) (k := k) (M := M)
      hf n (preimageCompacts hf hS hSf))
    (singularCohomologyComplRestrict R k M (subset_preimageCompacts_map hf hS hSf) n a)
  simp only [ConcreteCategory.comp_apply] at hext
  exact hext.trans (compactSupportCohomologyι_singularCohomologyComplRestrict
    (K := ⟨S, hS⟩) (subset_preimageCompacts_map hf hS hSf) a)

/-- `restrictι` along a composite open embedding `i = g ≫ f`, followed by extension along `g`,
is `restrictι` along `f` of the restriction to a larger compact set. -/
private lemma compactSupportCohomologyExtend_restrictι_of_comp_eq
    {Y' : TopCat.{v}} [T2Space Y] {g : Y' ⟶ Y} {i : Y' ⟶ X} (hg : IsOpenEmbedding g)
    (hi : IsOpenEmbedding i) (hgf : g ≫ f = i) {S T : Set X} (hS : IsCompact S)
    (hSi : S ⊆ Set.range i) (hT : IsCompact T) (hTf : T ⊆ Set.range f) (hST : S ⊆ T) {n : ℕ}
    (a : (TopPair.ofSubset Sᶜ).singularCohomology R k M n) :
    compactSupportCohomologyExtend hg n (restrictι hi hS hSi n a) =
      restrictι hf hT hTf n (singularCohomologyComplRestrict R k M hST n a) := by
  have hsub : ((preimageCompacts hi hS hSi).map i i.hom.continuous : Set X) ⊆
      (preimageCompacts hf hT hTf).map f f.hom.continuous := by
    rintro _ ⟨y, hy, rfl⟩
    exact subset_preimageCompacts_map hf hT hTf (hST hy)
  rw [restrictι, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    compactSupportCohomologyExtend_compactSupportCohomologyι_singularCohomologyComplCompactsMap
      hf hg hi hgf hsub,
    restrictι_apply hf hT hTf (subset_preimageCompacts_map hf hT hTf),
    singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict,
    singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict]

end Restrict

/-! ### The connecting map -/

section Connecting

private lemma subset_range_inclusion'_of_subset {W : Opens X} {S : Set X} (hS : S ⊆ W) :
    S ⊆ Set.range (Opens.inclusion' W) := by
  rwa [set_range_inclusion']

private lemma subset_of_subset_range_inclusion' {W : Opens X} {S : Set X}
    (hS : S ⊆ Set.range (Opens.inclusion' W)) : S ⊆ W := by
  rwa [set_range_inclusion'] at hS

variable (U V : Opens X)

private lemma inter_subset_range_inclusion'_inf {K L : Set X} (hKU : K ⊆ U) (hLV : L ⊆ V) :
    K ∩ L ⊆ Set.range (Opens.inclusion' (U ⊓ V)) :=
  subset_range_inclusion'_of_subset (by rw [Opens.coe_inf]; exact Set.inter_subset_inter hKU hLV)

variable [T2Space X]

/-- Every compact subset of `X = U ∪ V` lies in `K ∪ L` for compact sets `K ⊆ U` and `L ⊆ V`. -/
private lemma exists_isCompact_subset_union (hUV : U ⊔ V = ⊤) {C : Set X} (hC : IsCompact C) :
    ∃ KL : Set X × Set X, IsCompact KL.1 ∧ IsCompact KL.2 ∧ KL.1 ⊆ U ∧ KL.2 ⊆ V ∧
      C ⊆ KL.1 ∪ KL.2 := by
  obtain ⟨K, L, hK, hL, hKU, hLV, rfl⟩ := hC.binary_compact_cover U.isOpen V.isOpen
    (by rw [← Opens.coe_sup, hUV, Opens.coe_top]; exact Set.subset_univ _)
  exact ⟨(K, L), hK, hL, hKU, hLV, subset_rfl⟩

variable (R k M) in
/-- The connecting map on `Hⁿ(X, X ∖ (K ∪ L))` for compact sets `K ⊆ U` and `L ⊆ V`: the
connecting morphism into `Hᵐ(X, X ∖ (K ∩ L))`, followed by excision to `Hᵐ_c(U ∩ V)`. -/
private def mayerVietorisδAux {K L : Set X} (hK : IsCompact K) (hL : IsCompact L) (hKU : K ⊆ U)
    (hLV : L ⊆ V) (n m : ℕ) (h : n + 1 = m) :
    (TopPair.ofSubset (K ∪ L)ᶜ).singularCohomology R k M n ⟶
      ((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M m :=
  singularCohomologyComplMayerVietorisδ R k M hK.isClosed hL.isClosed n m h ≫
    restrictι (U ⊓ V).isOpenEmbedding (hK.inter_right hL.isClosed)
      (inter_subset_range_inclusion'_inf U V hKU hLV) m

private lemma mayerVietorisδAux_apply {K L : Set X} (hK : IsCompact K) (hL : IsCompact L)
    (hKU : K ⊆ U) (hLV : L ⊆ V) {n m : ℕ} (h : n + 1 = m)
    (a : (TopPair.ofSubset (K ∪ L)ᶜ).singularCohomology R k M n) :
    mayerVietorisδAux R k M U V hK hL hKU hLV n m h a =
      restrictι (U ⊓ V).isOpenEmbedding (hK.inter_right hL.isClosed)
        (inter_subset_range_inclusion'_inf U V hKU hLV) m
        (singularCohomologyComplMayerVietorisδ R k M hK.isClosed hL.isClosed n m h a) :=
  ConcreteCategory.comp_apply _ _ a

/-- The connecting maps on `Hⁿ(X, X ∖ (K ∪ L))` are compatible with enlarging `K` and `L`. -/
private lemma mayerVietorisδAux_singularCohomologyComplRestrict {K L K' L' : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V) (hK' : IsCompact K')
    (hL' : IsCompact L') (hK'U : K' ⊆ U) (hL'V : L' ⊆ V) (hKK' : K ⊆ K') (hLL' : L ⊆ L')
    {n m : ℕ} (h : n + 1 = m) (a : (TopPair.ofSubset (K ∪ L)ᶜ).singularCohomology R k M n) :
    mayerVietorisδAux R k M U V hK' hL' hK'U hL'V n m h
        (singularCohomologyComplRestrict R k M (Set.union_subset_union hKK' hLL') n a) =
      mayerVietorisδAux R k M U V hK hL hKU hLV n m h a := by
  have hnat := ConcreteCategory.congr_hom (singularCohomologyComplMayerVietorisδ_naturality
    (R := R) (k := k) (M := M) hK.isClosed hL.isClosed hK'.isClosed hL'.isClosed hKK' hLL' n m h) a
  simp only [ConcreteCategory.comp_apply] at hnat
  rw [mayerVietorisδAux_apply, mayerVietorisδAux_apply, ← hnat,
    restrictι_singularCohomologyComplRestrict]

variable (R k M) in
/-- The connecting map on `Hⁿ(X, X ∖ C)`, through a chosen cover of `C` by compact sets `K ⊆ U`
and `L ⊆ V`. -/
private def mayerVietorisδOn (hUV : U ⊔ V = ⊤) (C : Compacts X) (n m : ℕ) (h : n + 1 = m) :
    (TopPair.ofSubset (C : Set X)ᶜ).singularCohomology R k M n ⟶
      ((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M m :=
  have hKL := (exists_isCompact_subset_union U V hUV C.isCompact).choose_spec
  singularCohomologyComplRestrict R k M hKL.2.2.2.2 n ≫
    mayerVietorisδAux R k M U V hKL.1 hKL.2.1 hKL.2.2.1 hKL.2.2.2.1 n m h

/-- The connecting map on `Hⁿ(X, X ∖ C)` may be computed through any cover of `C` by compact sets
`K ⊆ U` and `L ⊆ V`. -/
private lemma mayerVietorisδOn_apply (hUV : U ⊔ V = ⊤) (C : Compacts X) {K L : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (hC : (C : Set X) ⊆ K ∪ L) {n m : ℕ} (h : n + 1 = m)
    (a : (TopPair.ofSubset (C : Set X)ᶜ).singularCohomology R k M n) :
    mayerVietorisδOn R k M U V hUV C n m h a =
      mayerVietorisδAux R k M U V hK hL hKU hLV n m h
        (singularCohomologyComplRestrict R k M hC n a) := by
  obtain ⟨hK₀, hL₀, hK₀U, hL₀V, -⟩ :=
    (exists_isCompact_subset_union U V hUV C.isCompact).choose_spec
  rw [mayerVietorisδOn, ConcreteCategory.comp_apply,
    ← mayerVietorisδAux_singularCohomologyComplRestrict U V hK₀ hL₀ hK₀U hL₀V (hK.union hK₀)
      (hL.union hL₀) (Set.union_subset hKU hK₀U) (Set.union_subset hLV hL₀V)
      Set.subset_union_right Set.subset_union_right,
    ← mayerVietorisδAux_singularCohomologyComplRestrict U V hK hL hKU hLV (hK.union hK₀)
      (hL.union hL₀) (Set.union_subset hKU hK₀U) (Set.union_subset hLV hL₀V)
      Set.subset_union_left Set.subset_union_left,
    singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict,
    singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict]

variable (R k M) in
/-- The **connecting map** `Hⁿ_c(X) ⟶ Hᵐ_c(U ∩ V)`, `n + 1 = m`, of the Mayer–Vietoris sequence of
cohomology with compact supports, for an open cover `X = U ∪ V` of a Hausdorff space. On
`Hⁿ(X, X ∖ (K ∪ L))` for compact sets `K ⊆ U` and `L ⊆ V` it is the connecting morphism
`Hⁿ(X, X ∖ (K ∪ L)) ⟶ Hᵐ(X, X ∖ (K ∩ L))` of the Mayer–Vietoris sequence of the pairs
`(X, X ∖ K)` and `(X, X ∖ L)`, followed by excision to `Hᵐ(U ∩ V, U ∩ V ∖ (K ∩ L))` and the map into
`Hᵐ_c(U ∩ V)` (`TopCat.compactSupportCohomologyι_compactSupportCohomologyMayerVietorisδ`). -/
def compactSupportCohomologyMayerVietorisδ (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    X.compactSupportCohomology R k M n ⟶
      ((Opens.toTopCat X).obj (U ⊓ V)).compactSupportCohomology R k M m :=
  compactSupportCohomologyDesc (fun C ↦ mayerVietorisδOn R k M U V hUV C n m h)
    fun C C' hCC' ↦ by
      obtain ⟨hK, hL, hKU, hLV, hC'⟩ :=
        (exists_isCompact_subset_union U V hUV C'.isCompact).choose_spec
      ext a
      change mayerVietorisδOn R k M U V hUV C' n m h
        (singularCohomologyComplRestrict R k M hCC' n a) = _
      rw [mayerVietorisδOn_apply U V hUV C' hK hL hKU hLV hC',
        singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict,
        ← mayerVietorisδOn_apply]
      exact hCC'

private lemma compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply
    (hUV : U ⊔ V = ⊤) {n m : ℕ} (h : n + 1 = m) (C : Compacts X) {K L : Set X}
    (hK : IsCompact K) (hL : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V)
    (hC : (C : Set X) ⊆ K ∪ L) (a : (TopPair.ofSubset (C : Set X)ᶜ).singularCohomology R k M n) :
    compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h (compactSupportCohomologyι n C a) =
      mayerVietorisδAux R k M U V hK hL hKU hLV n m h
        (singularCohomologyComplRestrict R k M hC n a) := by
  rw [← mayerVietorisδOn_apply, compactSupportCohomologyMayerVietorisδ,
    ← ConcreteCategory.comp_apply, compactSupportCohomologyι_desc]

/-- **The connecting map of the Mayer–Vietoris sequence of cohomology with compact supports on
`Hⁿ(X, X ∖ C)`.** For compact sets `K ⊆ U` and `L ⊆ V` with `C ⊆ K ∪ L`, a class of
`Hⁿ(X, X ∖ C)` is restricted to `Hⁿ(X, X ∖ (K ∪ L))`, carried by the connecting morphism of the
pairs `(X, X ∖ K)` and `(X, X ∖ L)` to `Hᵐ(X, X ∖ (K ∩ L))`, restricted to `Hᵐ(X, X ∖ N)` and then
to `Hᵐ(U ∩ V, U ∩ V ∖ N)` for any compact `N ⊆ U ∩ V` containing `K ∩ L`, and mapped to
`Hᵐ_c(U ∩ V)`. -/
lemma compactSupportCohomologyι_compactSupportCohomologyMayerVietorisδ (hUV : U ⊔ V = ⊤)
    {n m : ℕ} (h : n + 1 = m) (C : Compacts X) {K L : Set X} (hK : IsCompact K)
    (hL : IsCompact L) (hKU : K ⊆ U) (hLV : L ⊆ V) (hC : (C : Set X) ⊆ K ∪ L)
    (N : Compacts ((Opens.toTopCat X).obj (U ⊓ V)))
    (hN : K ∩ L ⊆ (N.map (Opens.inclusion' (U ⊓ V)) (Opens.inclusion' (U ⊓ V)).hom.continuous))
    (a : (TopPair.ofSubset (C : Set X)ᶜ).singularCohomology R k M n) :
    compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h (compactSupportCohomologyι n C a) =
      compactSupportCohomologyι m N (singularCohomologyComplCompactsMap
        (U ⊓ V).isOpenEmbedding.injective N m (singularCohomologyComplRestrict R k M hN m
          (singularCohomologyComplMayerVietorisδ R k M hK.isClosed hL.isClosed n m h
            (singularCohomologyComplRestrict R k M hC n a)))) := by
  rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h C hK hL
    hKU hLV hC, mayerVietorisδAux_apply, restrictι_apply _ _ _ hN]

/-- The connecting map vanishes on classes supported in `U` or in `V`. -/
private lemma compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_eq_zero
    (hUV : U ⊔ V = ⊤) {n m : ℕ} (h : n + 1 = m) (C : Compacts X)
    (hC : (C : Set X) ⊆ U ∨ (C : Set X) ⊆ V)
    (a : (TopPair.ofSubset (C : Set X)ᶜ).singularCohomology R k M n) :
    compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h (compactSupportCohomologyι n C a) =
      0 := by
  rcases hC with hC | hC
  · rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h C
      C.isCompact isCompact_empty hC (Set.empty_subset _) Set.subset_union_left,
      mayerVietorisδAux_apply, singularCohomologyComplMayerVietorisδ_restrict_left, map_zero]
  · rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h C
      isCompact_empty C.isCompact (Set.empty_subset _) hC Set.subset_union_right,
      mayerVietorisδAux_apply, singularCohomologyComplMayerVietorisδ_restrict_right, map_zero]

/-- The connecting map vanishes on classes extended from `Hⁿ_c(U)` and from `Hⁿ_c(V)`: the
composite `Hⁿ_c(U) ⊞ Hⁿ_c(V) ⟶ Hⁿ_c(X) ⟶ Hᵐ_c(U ∩ V)` is zero. -/
@[reassoc (attr := simp)]
lemma compactSupportCohomologyMayerVietorisFromBiprod_δ (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    compactSupportCohomologyMayerVietorisFromBiprod R k M U V n ≫
      compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h = 0 := by
  have key (W : Opens X) (hW : W = U ∨ W = V) :
      compactSupportCohomologyExtend (R := R) (k := k) (M := M) W.isOpenEmbedding n ≫
        compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h = 0 := by
    refine compactSupportCohomology_hom_ext fun K ↦ ?_
    rw [compactSupportCohomologyι_comp_extend_assoc, comp_zero]
    ext a
    have hK : (K.map (Opens.inclusion' W) (Opens.inclusion' W).hom.continuous : Set X) ⊆ W := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply]
    exact compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_eq_zero U V hUV h _
      (hW.imp (fun hWU ↦ hWU ▸ hK) fun hWV ↦ hWV ▸ hK) _
  apply biprod.hom_ext'
  · rw [inl_compactSupportCohomologyMayerVietorisFromBiprod_assoc, comp_zero]
    exact key U (Or.inl rfl)
  · rw [inr_compactSupportCohomologyMayerVietorisFromBiprod_assoc, comp_zero]
    exact key V (Or.inr rfl)

/-- The extensions to `U` and to `V` of a class in the image of the connecting map vanish. -/
private lemma compactSupportCohomologyExtend_compactSupportCohomologyMayerVietorisδ_eq_zero
    (hUV : U ⊔ V = ⊤) {n m : ℕ} (h : n + 1 = m) (x : X.compactSupportCohomology R k M n) :
    compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_left)) m
        (compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h x) = 0 ∧
      compactSupportCohomologyExtend (isOpenEmbedding_toTopCat_map (homOfLE inf_le_right)) m
        (compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h x) = 0 := by
  obtain ⟨C, -, a, rfl⟩ := exists_compactSupportCohomologyι_eq x ⊥
  obtain ⟨⟨K, L⟩, hK, hL, hKU, hLV, hC⟩ := exists_isCompact_subset_union U V hUV C.isCompact
  rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h C hK hL
    hKU hLV hC, mayerVietorisδAux_apply]
  constructor
  · rw [compactSupportCohomologyExtend_restrictι_of_comp_eq U.isOpenEmbedding _
      (U ⊓ V).isOpenEmbedding (toTopCat_map_comp_inclusion' _) _ _ hK
      (subset_range_inclusion'_of_subset hKU) Set.inter_subset_left,
      singularCohomologyComplRestrict_singularCohomologyComplMayerVietorisδ_left, map_zero]
  · rw [compactSupportCohomologyExtend_restrictι_of_comp_eq V.isOpenEmbedding _
      (U ⊓ V).isOpenEmbedding (toTopCat_map_comp_inclusion' _) _ _ hL
      (subset_range_inclusion'_of_subset hLV) Set.inter_subset_right,
      singularCohomologyComplRestrict_singularCohomologyComplMayerVietorisδ_right, map_zero]

/-- The connecting map followed by `Hᵐ_c(U ∩ V) ⟶ Hᵐ_c(U) ⊞ Hᵐ_c(V)` is zero. -/
@[reassoc (attr := simp)]
lemma compactSupportCohomologyMayerVietorisδ_toBiprod (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    compactSupportCohomologyMayerVietorisδ R k M U V hUV n m h ≫
      compactSupportCohomologyMayerVietorisToBiprod R k M U V m = 0 := by
  apply biprod.hom_ext
  · rw [Category.assoc, compactSupportCohomologyMayerVietorisToBiprod_fst, zero_comp]
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    simpa using (compactSupportCohomologyExtend_compactSupportCohomologyMayerVietorisδ_eq_zero
      U V hUV h x).1
  · rw [Category.assoc, compactSupportCohomologyMayerVietorisToBiprod_snd, zero_comp]
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    simpa using (compactSupportCohomologyExtend_compactSupportCohomologyMayerVietorisδ_eq_zero
      U V hUV h x).2

variable (R k M) in
/-- **Exactness of the Mayer–Vietoris sequence of cohomology with compact supports at
`Hⁿ_c(X)`**, for an open cover `X = U ∪ V` of a Hausdorff space: a class killed by the connecting
map is a sum of extensions of classes of `Hⁿ_c(U)` and `Hⁿ_c(V)`. -/
lemma compactSupportCohomologyMayerVietoris_exact₃ (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (compactSupportCohomologyMayerVietorisFromBiprod_δ (R := R) (k := k) (M := M) U V hUV n m
        h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro x hx
  dsimp only at hx ⊢
  obtain ⟨C, -, a, rfl⟩ := exists_compactSupportCohomologyι_eq x ⊥
  obtain ⟨⟨K, L⟩, hK, hL, hKU, hLV, hC⟩ := exists_isCompact_subset_union U V hUV C.isCompact
  dsimp only at hK hL hKU hLV hC
  rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h C hK hL
    hKU hLV hC, mayerVietorisδAux_apply] at hx
  -- the image of the class in `Hᵐ(X, X ∖ (K ∩ L))` dies on some compact `T ⊆ U ∩ V`
  obtain ⟨T, hT, hTW, hKLT, hzero⟩ :=
    exists_singularCohomologyComplRestrict_eq_zero_of_restrictι_eq_zero (U ⊓ V).isOpenEmbedding
      (hK.inter_right hL.isClosed) (inter_subset_range_inclusion'_inf U V hKU hLV) _ hx
  have hTUV : T ⊆ (U ⊓ V : Opens X) := subset_of_subset_range_inclusion' hTW
  rw [Opens.coe_inf] at hTUV
  -- enlarge `K` and `L` by `T`
  have hK' := hK.union hT
  have hL' := hL.union hT
  have hK'U : K ∪ T ⊆ U := Set.union_subset hKU (hTUV.trans Set.inter_subset_left)
  have hL'V : L ∪ T ⊆ V := Set.union_subset hLV (hTUV.trans Set.inter_subset_right)
  have hδ : singularCohomologyComplMayerVietorisδ R k M hK'.isClosed hL'.isClosed n m h
      (singularCohomologyComplRestrict R k M
        (Set.union_subset_union (Set.subset_union_left (t := T))
          (Set.subset_union_left (t := T))) n
        (singularCohomologyComplRestrict R k M hC n a)) = 0 := by
    have hnat := ConcreteCategory.congr_hom (singularCohomologyComplMayerVietorisδ_naturality
      (R := R) (k := k) (M := M) hK.isClosed hL.isClosed hK'.isClosed hL'.isClosed
      Set.subset_union_left Set.subset_union_left n m h)
      (singularCohomologyComplRestrict R k M hC n a)
    simp only [ConcreteCategory.comp_apply] at hnat
    rw [← hnat, ← singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict hKLT
      (Set.subset_inter Set.subset_union_right Set.subset_union_right), hzero, map_zero]
  obtain ⟨b, c, hbc⟩ :=
    exists_sub_eq_of_singularCohomologyComplMayerVietorisδ_eq_zero
      hK'.isClosed hL'.isClosed h _ hδ
  let HU := ((Opens.toTopCat X).obj U).compactSupportCohomology R k M n
  let HV := ((Opens.toTopCat X).obj V).compactSupportCohomology R k M n
  refine ⟨(biprod.inl : HU ⟶ HU ⊞ HV)
      (restrictι U.isOpenEmbedding hK' (subset_range_inclusion'_of_subset hK'U) n b) +
    (biprod.inr : HV ⟶ HU ⊞ HV)
      (-restrictι V.isOpenEmbedding hL' (subset_range_inclusion'_of_subset hL'V) n c), ?_⟩
  have h₁ := ConcreteCategory.congr_hom
    (inl_compactSupportCohomologyMayerVietorisFromBiprod R k M U V n)
    (restrictι U.isOpenEmbedding hK' (subset_range_inclusion'_of_subset hK'U) n b)
  have h₂ := ConcreteCategory.congr_hom
    (inr_compactSupportCohomologyMayerVietorisFromBiprod R k M U V n)
    (-restrictι V.isOpenEmbedding hL' (subset_range_inclusion'_of_subset hL'V) n c)
  rw [ConcreteCategory.comp_apply] at h₁ h₂
  rw [map_add, h₁, h₂, map_neg,
    compactSupportCohomologyExtend_restrictι U.isOpenEmbedding hK'
      (subset_range_inclusion'_of_subset hK'U) b,
    compactSupportCohomologyExtend_restrictι V.isOpenEmbedding hL'
      (subset_range_inclusion'_of_subset hL'V) c, ← sub_eq_add_neg]
  let B : Compacts X := ⟨(K ∪ T) ∪ (L ∪ T), hK'.union hL'⟩
  rw [← compactSupportCohomologyι_singularCohomologyComplRestrict (K := ⟨K ∪ T, hK'⟩) (L := B)
      Set.subset_union_left b,
    ← compactSupportCohomologyι_singularCohomologyComplRestrict (K := ⟨L ∪ T, hL'⟩) (L := B)
      Set.subset_union_right c,
    ← map_sub, hbc, singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict]
  exact compactSupportCohomologyι_singularCohomologyComplRestrict (K := C) (L := B) _ a

variable (R k M) in
/-- **Exactness of the Mayer–Vietoris sequence of cohomology with compact supports at
`Hᵐ_c(U ∩ V)`**, for an open cover `X = U ∪ V` of a Hausdorff space: a class whose extensions to
`U` and to `V` vanish is in the image of the connecting map. -/
lemma compactSupportCohomologyMayerVietoris_exact₁ (hUV : U ⊔ V = ⊤) (n m : ℕ)
    (h : n + 1 = m := by lia) :
    (ShortComplex.mk _ _
      (compactSupportCohomologyMayerVietorisδ_toBiprod (R := R) (k := k) (M := M) U V hUV n m
        h)).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro y hy
  dsimp only at hy ⊢
  have hfst := ConcreteCategory.congr_hom
    (compactSupportCohomologyMayerVietorisToBiprod_fst R k M U V m) y
  have hsnd := ConcreteCategory.congr_hom
    (compactSupportCohomologyMayerVietorisToBiprod_snd R k M U V m) y
  rw [ConcreteCategory.comp_apply, hy, map_zero] at hfst hsnd
  replace hfst := hfst.symm
  replace hsnd : compactSupportCohomologyExtend
      (isOpenEmbedding_toTopCat_map (homOfLE inf_le_right)) m y = 0 := by
    simpa using hsnd.symm
  obtain ⟨S, hS, hSW, z, rfl⟩ := exists_restrictι_eq (R := R) (k := k) (M := M)
    (U ⊓ V).isOpenEmbedding y
  have hSUV : S ⊆ (U ⊓ V : Opens X) := subset_of_subset_range_inclusion' hSW
  rw [Opens.coe_inf] at hSUV
  rw [compactSupportCohomologyExtend_restrictι_of_comp_eq U.isOpenEmbedding _
    (U ⊓ V).isOpenEmbedding (toTopCat_map_comp_inclusion' _) hS hSW hS
    (subset_range_inclusion'_of_subset (hSUV.trans Set.inter_subset_left)) subset_rfl] at hfst
  rw [compactSupportCohomologyExtend_restrictι_of_comp_eq V.isOpenEmbedding _
    (U ⊓ V).isOpenEmbedding (toTopCat_map_comp_inclusion' _) hS hSW hS
    (subset_range_inclusion'_of_subset (hSUV.trans Set.inter_subset_right)) subset_rfl] at hsnd
  obtain ⟨K, hK, hKU, hSK, hK0⟩ :=
    exists_singularCohomologyComplRestrict_eq_zero_of_restrictι_eq_zero _ _ _ _ hfst
  obtain ⟨L, hL, hLV, hSL, hL0⟩ :=
    exists_singularCohomologyComplRestrict_eq_zero_of_restrictι_eq_zero _ _ _ _ hsnd
  rw [singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict] at hK0 hL0
  have hKU' := subset_of_subset_range_inclusion' hKU
  have hLV' := subset_of_subset_range_inclusion' hLV
  obtain ⟨a, ha⟩ := exists_singularCohomologyComplMayerVietorisδ_eq hK.isClosed hL.isClosed h
    (singularCohomologyComplRestrict R k M (Set.subset_inter hSK hSL) m z)
    (by rw [singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict]; exact hK0)
    (by rw [singularCohomologyComplRestrict_apply_singularCohomologyComplRestrict]; exact hL0)
  refine ⟨compactSupportCohomologyι n ⟨K ∪ L, hK.union hL⟩ a, ?_⟩
  rw [compactSupportCohomologyMayerVietorisδ_compactSupportCohomologyι_apply U V hUV h _ hK hL
    hKU' hLV' subset_rfl, singularCohomologyComplRestrict_self_apply, mayerVietorisδAux_apply, ha,
    restrictι_singularCohomologyComplRestrict]

end Connecting

end TopCat
