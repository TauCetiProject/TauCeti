/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.FiveLemma
public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.Cup
public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism

/-!
# The Thom map and the Mayer–Vietoris sequence

Let `E → B` be a vector bundle with Thom pair `(E, E₀)` and let `u ∈ Hⁿ(E, E₀; K)`. For a subset
`W` of the base, the Thom map `TauCeti.thomMapOver` of a class `u_W ∈ Hⁿ(E|_W, E₀|_W; K)` is
`a ↦ π_W^*a ⌣ u_W`, where `π_W : E|_W ⟶ W` is the restricted projection; it is defined, with its
naturality in restrictions, in `TauCeti.Topology.VectorBundle.Thom.Isomorphism`.

The main result is the **Mayer–Vietoris step of the Thom isomorphism**
(`TauCeti.thomMap_bijective_of_union_eq_univ`). Let `U` and `V` be open sets covering the base. If
the Thom maps of the restrictions of `u` over `U`, `V` and `U ∩ V` are bijective in every degree,
and `Hⁿ⁻¹(E|_{U ∩ V}, E₀|_{U ∩ V}; M)` vanishes, then the Thom map of `u` is bijective in every
degree. This is the gluing step in the proof of the Thom isomorphism by induction over trivializing
open sets (Milnor and Stasheff, proof of Theorem 10.4; Hatcher, proof of Theorem 4D.10). For a real
vector bundle of rank `n`, the vanishing hypothesis holds when `U ∩ V` is a finite union of
trivializing open sets (`TauCeti.isZero_singularCohomology_thomPairOver_biUnion`).

The Thom maps form a map from the Mayer–Vietoris sequence of the cover `{U, V}` of the base
(`TopCat.singularCohomologyMayerVietorisδ`) to the Mayer–Vietoris sequence of the Thom pairs over
`U` and over `V` (`TopCat.singularCohomologyPairMayerVietorisδ`). The squares through restrictions
commute by naturality of the cup product. The square through the connecting morphisms commutes
because the connecting morphism of the pairs carries `a ⌣ u|` to `δ a ⌣ u`
(`TopCat.singularCohomologyPairMayerVietorisδ_singularCup`), and the connecting morphism of the
cover of the total space by the preimages of `U` and `V` is compatible with the projection
(`TopCat.singularCohomologyMayerVietorisδ_naturality`). The five lemma
(`ModuleCat.bijective_of_surjective_of_bijective_of_bijective_of_injective`) concludes; in degree
`m = n`, where the ladder starts with the first maps of the sequences, its left exact form
(`ModuleCat.bijective_of_bijective_of_injective_of_left_exact`) does.

## Main results

* `TauCeti.thomMap_bijective_of_union_eq_univ`: the Mayer–Vietoris step of the Thom isomorphism.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Set

universe w

namespace TauCeti

section MayerVietoris

/-! ### The Mayer–Vietoris step

Throughout, `U` and `V` are open sets of the base with `U ∪ V = B`. The Mayer–Vietoris sequence of
the Thom pairs over `U` and over `V` is stated for the pairs `(E|_U ∩ E|_V, E₀|_U ∩ E₀|_V)` and
`(E|_U ∪ E|_V, E₀|_U ∪ E₀|_V)`; the first is the Thom pair over `U ∩ V`
(`TauCeti.thomPairOverInterIso`), and the second maps isomorphically onto the Thom pair
`(E, E₀)`. -/

variable {B : Type w} [TopologicalSpace B] {F : Type*} [TopologicalSpace F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] {M : ModuleCat.{w} K} {U V : Set B}

variable (F E U V) in
/-- The intersection pair of the Mayer–Vietoris sequence of the Thom pairs over `U` and `V`. -/
private abbrev interPair : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of (TotalSpace F E))
    (inter_subset_inter (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))

variable (F E U V) in
/-- The union pair of the Mayer–Vietoris sequence of the Thom pairs over `U` and `V`. -/
private abbrev unionPair : TopPair.{w} :=
  TopPair.ofInclusion (X := TopCat.of (TotalSpace F E))
    (union_subset_union (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V))

variable (F E) in
/-- The restriction from the Thom pair `(E, E₀)` to the Thom pair over `W`. -/
private abbrev thomPairRestrict (W : Set B) : thomPairOver F E W ⟶ thomPair F E :=
  thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom

variable (F E U V) in
/-- The inclusion of the union pair into the Thom pair `(E, E₀)`. -/
private abbrev unionToThomPair : unionPair F E U V ⟶ thomPair F E :=
  (thomPairOverUnionIso F E U V).inv ≫ thomPairRestrict F E (U ∪ V)

variable (F E U V) in
/-- The inclusion of the intersection pair into the Thom pair `(E, E₀)`. -/
private abbrev interToThomPair : interPair F E U V ⟶ thomPair F E :=
  TopCat.interToUnionMap (X := TopCat.of (TotalSpace F E))
      (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
      (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) ≫
    unionToThomPair F E U V

variable (F E U V) in
/-- The projection `E|_U ∩ E|_V ⟶ U ∩ V`, the restriction of the projection of the total space. -/
private abbrev interProj : TopCat.of ↥(π F E ⁻¹' U ∩ π F E ⁻¹' V) ⟶ TopCat.of ↥(U ∩ V) :=
  TopCat.ofHom ⟨((mapsTo_thomPairProj F E U).inter_inter (mapsTo_thomPairProj F E V)).restrict,
    (thomPairProj F E).hom.continuous.restrict _⟩

omit [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
private theorem isIso_unionToThomPair (hUV : U ∪ V = univ) :
    IsIso (unionToThomPair F E U V) := by
  have : IsIso (thomPairOverMap F E (subset_univ (U ∪ V))) :=
    ⟨thomPairOverMap F E hUV.ge, by simp, by simp⟩
  infer_instance

/-! #### Compatibilities of the maps of pairs -/

private theorem thomPairOverInterIso_inv_fst_comp_thomPairOverProj :
    TopPair.Hom.fst (thomPairOverInterIso F E U V).inv ≫ thomPairOverProj F E (U ∩ V) =
      interProj F E U V :=
  TopCat.ext fun x ↦ by
    -- `x` lies in `(interPair F E U V).fst`, which is `π⁻¹U ∩ π⁻¹V` only after unfolding
    -- `TopPair.ofInclusion`, so the evaluation lemma applies only up to that unfolding.
    erw [TopCat.comp_app, thomPairOverInterIso_inv_fst_apply, thomPairOverProj_apply]
    exact Subtype.ext (thomPairProj_apply F E x.1).symm

private theorem unionToThomPair_fst_comp_thomPairProj :
    TopPair.Hom.fst (unionToThomPair F E U V) ≫ thomPairProj F E =
      TopCat.ofHom (ContinuousMap.subtypeVal _) ≫ thomPairProj F E := by
  rw [TopPair.Hom.fst_comp, Category.assoc,
    thomPairOverMap_comp_thomPairOverUnivIso_hom_fst_comp_thomPairProj]
  -- A point of `(unionPair F E U V).fst` is a point of `π⁻¹U ∪ π⁻¹V` only after unfolding
  -- `TopPair.ofInclusion`, so the evaluation lemma applies only up to that unfolding.
  exact TopCat.ext fun x ↦ by
    erw [TopCat.comp_app, thomPairOverUnionIso_inv_fst_apply, TopCat.comp_app,
      thomPairOverProj_apply, TopCat.comp_app, thomPairProj_apply]
    rfl

omit [TopologicalSpace B] [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] in
private theorem thomPairOverInterIso_inv_comp_thomPairRestrict :
    (thomPairOverInterIso F E U V).inv ≫ thomPairRestrict F E (U ∩ V) =
      interToThomPair F E U V := by
  rw [Iso.inv_comp_eq, interToThomPair,
    show TopCat.interToUnionMap _ _ = _ from TopPair.ofInclusionMap_comp _
      (hst' := (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U))
      (ContinuousMap.inclusion inter_subset_left) (ContinuousMap.inclusion subset_union_left)
      (fun _ hx ↦ inter_subset_left hx) (fun _ hx ↦ subset_union_left hx), Category.assoc,
    thomPairOverInterIso_hom_comp_ofInclusionMap_left_assoc, unionToThomPair,
    ofInclusionMap_comp_thomPairOverUnionIso_inv_left_assoc, thomPairRestrict, thomPairRestrict,
    thomPairOverMap_comp_thomPairOverMap_assoc, thomPairOverMap_comp_thomPairOverMap_assoc]

/-! #### The Thom maps on the pairs of the Mayer–Vietoris sequence -/

/-- The Thom map over `U ∩ V`, read on the intersection pair of the Mayer–Vietoris sequence, is the
cup product with the restriction of `u` to that pair. -/
private theorem singularCohomologyMap_thomPairOverInterIso_inv_thomMapOver {n p m : ℕ}
    (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of ↥(U ∩ V)).singularCohomology (ModuleCat.of K K) K M p) :
    TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m
        (thomMapOver F E M (U ∩ V) n p m h
          (TopPair.singularCohomologyMap (thomPairRestrict F E (U ∩ V)) n u) a) =
      (interPair F E U V).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv (ρ_ M).hom p n m h
        (TopCat.singularCohomologyMap (interProj F E U V) p a)
        (TopPair.singularCohomologyMap (interToThomPair F E U V) n u) := by
  rw [thomMapOver_apply, TopPair.singularCohomologyMap_singularCup_singularCohomologyMap K _ _ _
    thomPairOverInterIso_inv_fst_comp_thomPairOverProj, ← TopPair.singularCohomologyMap_comp_apply,
    thomPairOverInterIso_inv_comp_thomPairRestrict]
  rfl

/-- **The connecting morphisms commute with the Thom maps**: the connecting morphism of the
Mayer–Vietoris sequence of the Thom pairs over `U` and `V` carries the Thom map of `a` over
`U ∩ V` to the Thom map of the connecting morphism of `a` in the Mayer–Vietoris sequence of the
base. -/
private theorem singularCohomologyPairMayerVietorisδ_thomMapOver (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of ↥(U ∩ V)).singularCohomology (ModuleCat.of K K) K M p) :
    TopCat.singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M
        (X := TopCat.of (TotalSpace F E))
        (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
        (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)
        (isOpen_subtypeVal_preimage_preimage_proj hU _)
        (isOpen_subtypeVal_preimage_preimage_proj hV _)
        (isOpen_subtypeVal_preimage_preimage_proj_inter_zeroSectionCompl hU
          (union_subset inter_subset_right inter_subset_right))
        (isOpen_subtypeVal_preimage_preimage_proj_inter_zeroSectionCompl hV
          (union_subset inter_subset_right inter_subset_right)) m (m + 1) rfl
        (TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m
          (thomMapOver F E M (U ∩ V) n p m h
            (TopPair.singularCohomologyMap (thomPairRestrict F E (U ∩ V)) n u) a)) =
      TopPair.singularCohomologyMap (unionToThomPair F E U V) (m + 1)
        (thomMap F E M n (p + 1) (m + 1) (by omega) u
          (TopCat.singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M
            (X := TopCat.of B) hU hV hUV p (p + 1) rfl a)) := by
  have hU' : IsOpen (π F E ⁻¹' U) := hU.preimage (FiberBundle.continuous_proj F E)
  have hV' : IsOpen (π F E ⁻¹' V) := hV.preimage (FiberBundle.continuous_proj F E)
  have hUV' : π F E ⁻¹' U ∪ π F E ⁻¹' V = univ := by rw [← preimage_union, hUV, preimage_univ]
  rw [singularCohomologyMap_thomPairOverInterIso_inv_thomMapOver,
    TopPair.singularCohomologyMap_comp_apply (TopCat.interToUnionMap _ _)
      (unionToThomPair F E U V)]
  -- The connecting morphism of the pairs carries `a ⌣ u|` to `δ a ⌣ u`, where `δ a` is taken in
  -- the Mayer–Vietoris sequence of the cover of the total space by the preimages of `U` and `V`.
  refine (TopCat.singularCohomologyPairMayerVietorisδ_singularCup K hU' hV' hUV'
    (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
    (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)
    (isOpen_subtypeVal_preimage_preimage_proj_inter_zeroSectionCompl hU
      (union_subset inter_subset_right inter_subset_right))
    (isOpen_subtypeVal_preimage_preimage_proj_inter_zeroSectionCompl hV
      (union_subset inter_subset_right inter_subset_right)) _ _ h rfl rfl (by omega) _ _).trans ?_
  -- That connecting morphism is the pull-back of the one of the base along the projection.
  have hδ := ConcreteCategory.congr_hom (TopCat.singularCohomologyMayerVietorisδ_naturality
    (ModuleCat.of K K) K M hU' hV' hUV' hU hV hUV (thomPairProj F E) (mapsTo_thomPairProj F E U)
    (mapsTo_thomPairProj F E V) p (p + 1) rfl) a
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hδ
  rw [thomMap_apply, TopPair.singularCohomologyMap_singularCup_singularCohomologyMap K _ _ _
    unionToThomPair_fst_comp_thomPairProj]
  exact congrArg (fun z ↦ (unionPair F E U V).singularCup K (λ_ (𝟙_ (ModuleCat.{w} K))).inv
    (ρ_ M).hom (p + 1) n (m + 1) (by omega) z
    (TopPair.singularCohomologyMap (unionToThomPair F E U V) n u))
    ((congrArg (fun z ↦ TopCat.singularCohomologyMap
      (TopCat.ofHom (ContinuousMap.subtypeVal (π F E ⁻¹' U ∪ π F E ⁻¹' V))) (p + 1) z)
        hδ.symm).trans
    (ConcreteCategory.congr_hom (TopCat.singularCohomologyMap_comp _ _ (p + 1)) _).symm)

/-! #### The ladder of Mayer–Vietoris sequences -/

variable (F E M) in
/-- The Thom map over `W` of the restriction of `u`, as a morphism of modules. -/
private abbrev thomMapOverHom (W : Set B) {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (p m : ℕ) (h : p + n = m) :
    (TopCat.of W).singularCohomology (ModuleCat.of K K) K M p ⟶
      (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  ModuleCat.ofHom (thomMapOver F E M W n p m h
    (TopPair.singularCohomologyMap (thomPairRestrict F E W) n u))

/-- Restricting the Thom map over `W` to a subset `W'` gives the Thom map over `W'`. -/
@[reassoc]
private theorem thomMapOverHom_comp_singularCohomologyMap_thomPairOverMap {W' W : Set B}
    (hW : W' ⊆ W) {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (p m : ℕ) (h : p + n = m) :
    thomMapOverHom F E M W u p m h ≫ TopPair.singularCohomologyMap (thomPairOverMap F E hW) m =
      TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.inclusion hW)) p ≫
        thomMapOverHom F E M W' u p m h := by
  ext a
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
  refine (singularCohomologyMap_thomPairOverMap_thomMapOver F E hW h _ a).trans ?_
  rw [← TopPair.singularCohomologyMap_comp_apply, thomPairOverMap_comp_thomPairOverMap_assoc]
  rfl

/-- The square through the second maps of the Mayer–Vietoris sequences commutes. -/
private theorem singularCohomologyMayerVietorisFromBiprod_comp_thomMapOverHom {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (p m : ℕ) (h : p + n = m) :
    TopCat.singularCohomologyMayerVietorisFromBiprod (ModuleCat.of K K) K M (X := TopCat.of B)
        U V p ≫ thomMapOverHom F E M (U ∩ V) u p m h ≫
          TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m =
      biprod.map (thomMapOverHom F E M U u p m h) (thomMapOverHom F E M V u p m h) ≫
        TopCat.singularCohomologyPairMayerVietorisFromBiprod (ModuleCat.of K K) K M
          (X := TopCat.of (TotalSpace F E))
          (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) m := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [TopCat.inl_singularCohomologyMayerVietorisFromBiprod_assoc, biprod.inl_map_assoc,
      TopCat.inl_singularCohomologyPairMayerVietorisFromBiprod,
      (Iso.eq_inv_comp _).2 thomPairOverInterIso_hom_comp_ofInclusionMap_left,
      TopPair.singularCohomologyMap_comp,
      thomMapOverHom_comp_singularCohomologyMap_thomPairOverMap_assoc]
  · rw [TopCat.inr_singularCohomologyMayerVietorisFromBiprod_assoc, biprod.inr_map_assoc,
      TopCat.inr_singularCohomologyPairMayerVietorisFromBiprod, Preadditive.neg_comp,
      Preadditive.comp_neg, neg_inj,
      (Iso.eq_inv_comp _).2 thomPairOverInterIso_hom_comp_ofInclusionMap_right,
      TopPair.singularCohomologyMap_comp,
      thomMapOverHom_comp_singularCohomologyMap_thomPairOverMap_assoc]

/-- The square through the first maps of the Mayer–Vietoris sequences commutes. -/
private theorem singularCohomologyMayerVietorisToBiprod_comp_biprod_map {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (p m : ℕ) (h : p + n = m) :
    TopCat.singularCohomologyMayerVietorisToBiprod (ModuleCat.of K K) K M (X := TopCat.of B)
        U V p ≫ biprod.map (thomMapOverHom F E M U u p m h) (thomMapOverHom F E M V u p m h) =
      (ModuleCat.ofHom (thomMap F E M n p m h u) ≫
        TopPair.singularCohomologyMap (unionToThomPair F E U V) m) ≫
        TopCat.singularCohomologyPairMayerVietorisToBiprod (ModuleCat.of K K) K M
          (X := TopCat.of (TotalSpace F E))
          (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V) m := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, Category.assoc, biprod.map_fst,
      TopCat.singularCohomologyMayerVietorisToBiprod_fst_assoc,
      TopCat.singularCohomologyPairMayerVietorisToBiprod_fst, Category.assoc,
      ← TopPair.singularCohomologyMap_comp, unionToThomPair,
      ofInclusionMap_comp_thomPairOverUnionIso_inv_left_assoc, thomPairRestrict,
      thomPairOverMap_comp_thomPairOverMap_assoc]
    ext a
    exact (singularCohomologyMap_thomPairOverMap_thomMap F E U h u a).symm
  · rw [Category.assoc, Category.assoc, biprod.map_snd,
      TopCat.singularCohomologyMayerVietorisToBiprod_snd_assoc,
      TopCat.singularCohomologyPairMayerVietorisToBiprod_snd, Category.assoc,
      ← TopPair.singularCohomologyMap_comp, unionToThomPair,
      ofInclusionMap_comp_thomPairOverUnionIso_inv_right_assoc, thomPairRestrict,
      thomPairOverMap_comp_thomPairOverMap_assoc]
    ext a
    exact (singularCohomologyMap_thomPairOverMap_thomMap F E V h u a).symm

/-- The square through the connecting morphisms of the Mayer–Vietoris sequences commutes. -/
private theorem singularCohomologyMayerVietorisδ_comp_thomMap (hU : IsOpen U) (hV : IsOpen V)
    (hUV : U ∪ V = univ) {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (p m : ℕ) (h : p + n = m) :
    TopCat.singularCohomologyMayerVietorisδ (ModuleCat.of K K) K M (X := TopCat.of B) hU hV hUV
        p (p + 1) rfl ≫ ModuleCat.ofHom (thomMap F E M n (p + 1) (m + 1) (by omega) u) ≫
          TopPair.singularCohomologyMap (unionToThomPair F E U V) (m + 1) =
      (thomMapOverHom F E M (U ∩ V) u p m h ≫
        TopPair.singularCohomologyMap (thomPairOverInterIso F E U V).inv m) ≫
        TopCat.singularCohomologyPairMayerVietorisδ (ModuleCat.of K K) K M
          (X := TopCat.of (TotalSpace F E))
          (inter_subset_left : π F E ⁻¹' U ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' U)
          (inter_subset_left : π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆ π F E ⁻¹' V)
          (isOpen_subtypeVal_preimage_preimage_proj hU _)
          (isOpen_subtypeVal_preimage_preimage_proj hV _)
          (isOpen_subtypeVal_preimage_preimage_proj_inter_zeroSectionCompl hU
            (union_subset inter_subset_right inter_subset_right))
          (isOpen_subtypeVal_preimage_preimage_proj_inter_zeroSectionCompl hV
            (union_subset inter_subset_right inter_subset_right)) m (m + 1) rfl :=
  ModuleCat.hom_ext (LinearMap.ext fun a ↦
    (singularCohomologyPairMayerVietorisδ_thomMapOver hU hV hUV h u a).symm)

/-- The direct sum of the Thom maps over `U` and over `V` is bijective when both are. -/
private theorem bijective_biprod_map_thomMapOverHom {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    {p m : ℕ} (h : p + n = m)
    (hΦU : Function.Bijective (thomMapOver F E M U n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E U) n u)))
    (hΦV : Function.Bijective (thomMapOver F E M V n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E V) n u))) :
    Function.Bijective
      (biprod.map (thomMapOverHom F E M U u p m h) (thomMapOverHom F E M V u p m h)) := by
  have := (ConcreteCategory.isIso_iff_bijective (thomMapOverHom F E M U u p m h)).2 hΦU
  have := (ConcreteCategory.isIso_iff_bijective (thomMapOverHom F E M V u p m h)).2 hΦV
  exact ConcreteCategory.bijective_of_isIso
    (biprod.mapIso (asIso (thomMapOverHom F E M U u p m h))
      (asIso (thomMapOverHom F E M V u p m h))).hom

/-- The Thom map over `U ∩ V`, read on the intersection pair, is bijective when the Thom map over
`U ∩ V` is. -/
private theorem bijective_thomMapOverHom_comp {W : Set B} {P : TopPair.{w}}
    (e : P ≅ thomPairOver F E W) {n : ℕ}
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    {p m : ℕ} (h : p + n = m)
    (hΦ : Function.Bijective (thomMapOver F E M W n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E W) n u))) :
    Function.Bijective
      (thomMapOverHom F E M W u p m h ≫ TopPair.singularCohomologyMap e.hom m) := by
  have := (ConcreteCategory.isIso_iff_bijective (thomMapOverHom F E M W u p m h)).2 hΦ
  exact ConcreteCategory.bijective_of_isIso _

/-- The degree-`0` case of the Mayer–Vietoris step, read on the union pair: the five lemma for the
ladder of Mayer–Vietoris sequences starting with their first maps, which are monomorphisms since
`Hⁿ⁻¹(E|_{U ∩ V}, E₀|_{U ∩ V})` vanishes. -/
private theorem bijective_thomMap_comp_zero (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    {n : ℕ} (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hΦU : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M U n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E U) n u)))
    (hΦV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M V n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E V) n u)))
    (hΦUV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M (U ∩ V) n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E (U ∩ V)) n u)))
    (hUVn : ∀ k, k + 1 = n →
      IsZero ((thomPairOver F E (U ∩ V)).singularCohomology (ModuleCat.of K K) K M k))
    (h : 0 + n = n) :
    Function.Bijective (ModuleCat.ofHom (thomMap F E M n 0 n h u) ≫
      TopPair.singularCohomologyMap (unionToThomPair F E U V) n) := by
  have := TopCat.mono_singularCohomologyMayerVietorisToBiprod_zero (ModuleCat.of K K) K M
    (X := TopCat.of B) hU hV hUV
  have := mono_singularCohomologyPairMayerVietorisToBiprod_thomPairOver (k := K) hU hV hUVn
  exact ModuleCat.bijective_of_bijective_of_injective_of_left_exact
    (TopCat.singularCohomologyMayerVietoris_exact₂ (ModuleCat.of K K) K M (X := TopCat.of B)
      hU hV hUV 0)
    (TopCat.singularCohomologyPairMayerVietoris_exact₂ _ _ _ _ _
      (isOpen_subtypeVal_preimage_preimage_proj hU _)
      (isOpen_subtypeVal_preimage_preimage_proj hV _)
      (isOpen_subtypeVal_preimage_preimage_proj_inter_zeroSectionCompl hU
        (union_subset inter_subset_right inter_subset_right))
      (isOpen_subtypeVal_preimage_preimage_proj_inter_zeroSectionCompl hV
        (union_subset inter_subset_right inter_subset_right)) n)
    (singularCohomologyMayerVietorisToBiprod_comp_biprod_map u 0 n h)
    (singularCohomologyMayerVietorisFromBiprod_comp_thomMapOverHom u 0 n h)
    (bijective_biprod_map_thomMapOverHom u h (hΦU 0 n h) (hΦV 0 n h))
    (bijective_thomMapOverHom_comp (thomPairOverInterIso F E U V).symm u h (hΦUV 0 n h)).1

/-- The positive-degree case of the Mayer–Vietoris step, read on the union pair: the five lemma
applied to the ladder of Mayer–Vietoris sequences. -/
private theorem bijective_thomMap_comp_succ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    {n : ℕ} (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hΦU : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M U n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E U) n u)))
    (hΦV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M V n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E V) n u)))
    (hΦUV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M (U ∩ V) n p m h
      (TopPair.singularCohomologyMap (thomPairRestrict F E (U ∩ V)) n u)))
    (q : ℕ) (h : q + 1 + n = q + n + 1) :
    Function.Bijective (ModuleCat.ofHom (thomMap F E M n (q + 1) (q + n + 1) h u) ≫
      TopPair.singularCohomologyMap (unionToThomPair F E U V) (q + n + 1)) := by
  have hT : π F E ⁻¹' U ∩ zeroSectionCompl F E ∪ π F E ⁻¹' V ∩ zeroSectionCompl F E ⊆
      zeroSectionCompl F E := union_subset inter_subset_right inter_subset_right
  have hA := isOpen_subtypeVal_preimage_preimage_proj hU (π F E ⁻¹' U ∪ π F E ⁻¹' V)
  have hB := isOpen_subtypeVal_preimage_preimage_proj hV (π F E ⁻¹' U ∪ π F E ⁻¹' V)
  have hC := isOpen_subtypeVal_preimage_preimage_proj_inter_zeroSectionCompl hU hT
  have hD := isOpen_subtypeVal_preimage_preimage_proj_inter_zeroSectionCompl hV hT
  exact ModuleCat.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (TopCat.singularCohomologyMayerVietoris_exact₃ (ModuleCat.of K K) K M (X := TopCat.of B)
      hU hV hUV q (q + 1) rfl)
    (TopCat.singularCohomologyMayerVietoris_exact₁ (ModuleCat.of K K) K M (X := TopCat.of B)
      hU hV hUV q (q + 1) rfl)
    (TopCat.singularCohomologyMayerVietoris_exact₂ (ModuleCat.of K K) K M (X := TopCat.of B)
      hU hV hUV (q + 1))
    (TopCat.singularCohomologyPairMayerVietoris_exact₃ _ _ _ _ _ hA hB hC hD (q + n)
      (q + n + 1) rfl)
    (TopCat.singularCohomologyPairMayerVietoris_exact₁ _ _ _ _ _ hA hB hC hD (q + n)
      (q + n + 1) rfl)
    (TopCat.singularCohomologyPairMayerVietoris_exact₂ _ _ _ _ _ hA hB hC hD (q + n + 1))
    (singularCohomologyMayerVietorisFromBiprod_comp_thomMapOverHom u q (q + n) rfl)
    (singularCohomologyMayerVietorisδ_comp_thomMap hU hV hUV u q (q + n) rfl)
    (singularCohomologyMayerVietorisToBiprod_comp_biprod_map u (q + 1) (q + n + 1) h)
    (singularCohomologyMayerVietorisFromBiprod_comp_thomMapOverHom u (q + 1) (q + n + 1) h)
    (bijective_biprod_map_thomMapOverHom u rfl (hΦU q (q + n) rfl) (hΦV q (q + n) rfl)).2
    (bijective_thomMapOverHom_comp (thomPairOverInterIso F E U V).symm u rfl (hΦUV q (q + n) rfl))
    (bijective_biprod_map_thomMapOverHom u h (hΦU (q + 1) (q + n + 1) h)
      (hΦV (q + 1) (q + n + 1) h))
    (bijective_thomMapOverHom_comp (thomPairOverInterIso F E U V).symm u h
      (hΦUV (q + 1) (q + n + 1) h)).1

/-- **The Mayer–Vietoris step of the Thom isomorphism.** Let `U` and `V` be open sets covering the
base of a fibre bundle `E → B` and let `u ∈ Hⁿ(E, E₀; K)`. If the Thom maps of the restrictions of
`u` over `U`, `V` and `U ∩ V` are bijective in every degree, and
`Hⁿ⁻¹(E|_{U ∩ V}, E₀|_{U ∩ V}; M)` vanishes, then the Thom map `a ↦ π^*a ⌣ u` of `u` is bijective
in every degree. -/
theorem thomMap_bijective_of_union_eq_univ (hU : IsOpen U) (hV : IsOpen V) (hUV : U ∪ V = univ)
    {n : ℕ} (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (hΦU : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M U n p m h
      (TopPair.singularCohomologyMap (thomPairOverMap F E (subset_univ U) ≫
        (thomPairOverUnivIso F E).hom) n u)))
    (hΦV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M V n p m h
      (TopPair.singularCohomologyMap (thomPairOverMap F E (subset_univ V) ≫
        (thomPairOverUnivIso F E).hom) n u)))
    (hΦUV : ∀ p m (h : p + n = m), Function.Bijective (thomMapOver F E M (U ∩ V) n p m h
      (TopPair.singularCohomologyMap (thomPairOverMap F E (subset_univ (U ∩ V)) ≫
        (thomPairOverUnivIso F E).hom) n u)))
    (hUVn : ∀ k, k + 1 = n →
      IsZero ((thomPairOver F E (U ∩ V)).singularCohomology (ModuleCat.of K K) K M k))
    (p m : ℕ) (h : p + n = m) :
    Function.Bijective (thomMap F E M n p m h u) := by
  have := isIso_unionToThomPair (F := F) (E := E) hUV
  -- It suffices to show that the Thom map followed by the isomorphism onto the cohomology of the
  -- union pair of the Mayer–Vietoris sequence is bijective.
  suffices hI : Function.Bijective (ModuleCat.ofHom (thomMap F E M n p m h u) ≫
      TopPair.singularCohomologyMap (unionToThomPair F E U V) m) by
    have := (ConcreteCategory.isIso_iff_bijective _).2 hI
    have := IsIso.of_isIso_comp_right (ModuleCat.ofHom (thomMap F E M n p m h u))
      (TopPair.singularCohomologyMap (unionToThomPair F E U V) m)
    exact ConcreteCategory.bijective_of_isIso (ModuleCat.ofHom (thomMap F E M n p m h u))
  rcases p with _ | q
  · obtain rfl : m = n := by omega
    exact bijective_thomMap_comp_zero hU hV hUV u hΦU hΦV hΦUV hUVn h
  · obtain rfl : m = q + n + 1 := by omega
    exact bijective_thomMap_comp_succ hU hV hUV u hΦU hΦV hΦUV q h

end MayerVietoris

end TauCeti
