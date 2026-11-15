/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.ThomClass
public import TauCeti.Topology.VectorBundle.Thom.Homology
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
import TauCeti.AlgebraicTopology.Cohomology.Point
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.PullbackCup
import TauCeti.Topology.FiberBundle.Pullback

/-!
# The Thom isomorphism over finite trivializing covers

Let `E → B` be a real vector bundle with finite-dimensional model fibre `F` of rank
`r = finrank ℝ F`, Thom pair `(E, E₀) = TauCeti.thomPair F E`, and coefficient ring `K`. This file
proves that the Thom map

`Φ_u : Hᵖ(B; M) ⟶ Hᵐ(E, E₀; M)`,  `a ↦ π^* a ⌣ u`,  `p + r = m`,

(`TauCeti.thomMap`) is bijective in every degree `p` and for every `K`-module `M` whenever `u` is a
Thom class (`TauCeti.IsThomClass F E u`) and `E` admits a finite trivializing cover—in particular
whenever `B` is compact (`TauCeti.IsThomClass.bijective_thomMap_of_compactSpace`,
`TauCeti.IsThomClass.thomEquivOfCompactSpace`) or globally trivializable
(`Bundle.Trivialization.bijective_thomMap`, `Bundle.Trivialization.thomEquiv`).

## Proof outline

1. **Restriction to subsets of the base (`TauCeti.thomMapOver`)**: for `W ⊆ B`, `thomMapOver` wraps
   `TopCat.pullbackCupRestrict` of the bundle projection `π : E ⟶ B` into a `K`-bilinear map
   `Hⁿ(E, E₀; K) →ₗ[K] Hᵖ(W; M) →ₗ[K] Hᵐ(E|_W, E₀|_W; M)` that is natural along inclusions
   `W ⊆ W'` (`TauCeti.thomMapOver_naturality`), bijective over `∅`
   (`TauCeti.bijective_thomMapOver_empty`), equivalent over `Set.univ` to `TauCeti.thomMap`
   (`TauCeti.bijective_thomMapOver_univ_iff`), and equivalent over any `W` to `TauCeti.thomMap` of
   the pullback bundle along `W ↪ B` (`TauCeti.bijective_thomMapOver_iff_pullback`).
2. **Single trivializing set (`Bundle.Trivialization.bijective_thomMapOver`)**: over any subset
   `W ⊆ e.baseSet` of a linear trivialization `e`, `Bundle.Trivialization.thomPairOverIso`
   identifies `(E|_W, E₀|_W)` with `TauCeti.prodThomPair W F` compatibly with the bundle projection
   and fibre inclusions, reducing bijectivity to the product-bundle Thom isomorphism
   `TauCeti.bijective_pullbackCup_prodThomPair`.
3. **Finite unions of trivializing sets (`TauCeti.bijective_thomMapOver_biUnion`)**: for open sets
   `W i`, induction on `s : Finset ι` glues bijectivity over `⋃ i ∈ s, W i` via the Mayer–Vietoris
   five-lemma step `TopCat.bijective_pullbackCupRestrict_union` and the below-rank vanishing
   `TauCeti.isZero_singularCohomology_thomPairOver_biUnion` on the intersection
   `W a ∩ ⋃ i ∈ s, W i = ⋃ i ∈ s, (W a ∩ W i)`. For arbitrary sets `W i` contained in linear
   trivializations, pulling `E` back to `Y = ⋃ i ∈ s, W i` and replacing each pulled-back set by the
   open base set of its pulled-back trivialization reduces to the open-cover case on `Y`.
4. **Global specializations**: when `⋃ i ∈ s, W i = Set.univ`—and hence for any vector bundle over
   a compact space `B` by extracting a finite subcover of `trivializationAt`—`thomMap` is a linear
   equivalence (`TauCeti.IsThomClass.thomEquivOfBiUnionEqUniv`,
   `TauCeti.IsThomClass.thomEquivOfCompactSpace`). Combining this with:
   * `TauCeti.existsUnique_isThomClass_of_subsingleton_units` gives the canonical unoriented Thom
     isomorphism over rings with `Subsingleton Kˣ` such as `ZMod 2`
     (`TauCeti.thomEquivOfSubsingletonUnitsOfCompactSpace`);
   * `TauCeti.VectorBundleOrientation.thomClassOfModel` gives the oriented Thom isomorphism
     (`TauCeti.VectorBundleOrientation.thomEquivOfModelOfCompactSpace`);
   * `TauCeti.bijective_homologyThomMap_iff` gives the homological Thom isomorphism `x ↦ π_*(x ⌢ u)`
     over any field `K` (`TauCeti.IsThomClass.bijective_homologyThomMap_of_compactSpace`,
     `TauCeti.IsThomClass.homologyThomIsoOfCompactSpace`).

## Main definitions and results

* `TauCeti.thomMapOver`, `TauCeti.thomMapOver_naturality`, `TauCeti.bijective_thomMapOver_univ_iff`,
  `TauCeti.bijective_thomMapOver_iff_pullback`: the Thom map over subsets `W ⊆ B` and its
  comparison with the pullback bundle along `W ↪ B`.
* `Bundle.Trivialization.bijective_thomMapOver`, `Bundle.Trivialization.thomEquivOver`,
  `Bundle.Trivialization.bijective_thomMap`, `Bundle.Trivialization.thomEquiv`: local and global
  Thom isomorphisms from a single linear trivialization.
* `TauCeti.bijective_thomMapOver_biUnion`, `TauCeti.IsThomClass.bijective_thomMapOver_biUnion`,
  `TauCeti.IsThomClass.thomEquivOverBiUnion`: the Thom isomorphism over a finite union of
  trivializing sets.
* `TauCeti.IsThomClass.bijective_thomMap_of_biUnion_eq_univ`,
  `TauCeti.IsThomClass.thomEquivOfBiUnionEqUniv`: the Thom isomorphism for bundles admitting a
  finite trivializing cover.
* `TauCeti.IsThomClass.bijective_thomMap_of_compactSpace`,
  `TauCeti.IsThomClass.thomEquivOfCompactSpace`: the Thom isomorphism over a compact base.
* `TauCeti.thomClassOfSubsingletonUnits`, `TauCeti.thomEquivOfSubsingletonUnitsOfCompactSpace`:
  the canonical unoriented Thom isomorphism when `Kˣ` is a subsingleton.
* `TauCeti.VectorBundleOrientation.thomEquivOfModelOfCompactSpace`: the oriented Thom isomorphism
  over a compact base.
* `TauCeti.IsThomClass.bijective_homologyThomMap_of_biUnion_eq_univ`,
  `TauCeti.IsThomClass.bijective_homologyThomMap_of_compactSpace`,
  `TauCeti.IsThomClass.homologyThomIsoOfCompactSpace`: the homological Thom isomorphism with field
  coefficients.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Set

universe w

namespace TauCeti

/-! ### The Thom map over a subset of the base -/

section PullbackSubtypeVal

variable {B : Type w} [TopologicalSpace B] (F : Type*)
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]

attribute [local instance] pullbackFiberZero

/-- The canonical map `(i^* E, (i^* E)₀) ⟶ (E|_W, E₀|_W)` from the Thom pair of the pullback bundle
along `i = ContinuousMap.subtypeVal W` to `thomPairOver F E W`. -/
def pullbackSubtypeValThomPairMap (W : Set B) :
    thomPair F ((⇑(ContinuousMap.subtypeVal W)) *ᵖ E) ⟶ thomPairOver F E W :=
  TopPair.ofHom
    (TopCat.ofHom ⟨fun z ↦ ⟨Pullback.lift (ContinuousMap.subtypeVal W) z, z.proj.2⟩,
      (Pullback.continuous_lift F E _).subtype_mk _⟩)
    (TopCat.ofHom ⟨fun z ↦ ⟨Pullback.lift (ContinuousMap.subtypeVal W) z.1, z.1.proj.2,
        (mem_zeroSectionCompl (E := E)).2
          ((mem_zeroSectionCompl (E := (⇑(ContinuousMap.subtypeVal W)) *ᵖ E)).1 z.2)⟩,
      ((Pullback.continuous_lift F E _).comp continuous_subtype_val).subtype_mk _⟩)
    (by ext; rfl)

@[simp]
theorem pullbackSubtypeValThomPairMap_fst_apply (W : Set B)
    (z : TotalSpace F ((⇑(ContinuousMap.subtypeVal W)) *ᵖ E)) :
    TopPair.Hom.fst (pullbackSubtypeValThomPairMap F E W) z =
      ⟨Pullback.lift (ContinuousMap.subtypeVal W) z, z.proj.2⟩ :=
  (rfl)

/-- `pullbackSubtypeValThomPairMap` followed by the subspace inclusion `(E|_W, E₀|_W) ⟶ (E, E₀)` is
`pullbackThomPairMap` along `ContinuousMap.subtypeVal W`. -/
@[reassoc (attr := simp)]
theorem pullbackSubtypeValThomPairMap_comp_restrictPreimagePairMap (W : Set B) :
    pullbackSubtypeValThomPairMap F E W ≫
        TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E))
          (π F E) (zeroSectionCompl F E) W =
      pullbackThomPairMap F E (ContinuousMap.subtypeVal W) :=
  TopPair.hom_ext_of_fst _ (TopCat.ext fun z ↦
    (TopCat.restrictPreimagePairMap_fst_apply _ _ _ _).trans
      (pullbackThomPairMap_fst_apply F E _ z).symm)

variable [TopologicalSpace F] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- For any subset `W ⊆ B`, `pullbackSubtypeValThomPairMap F E W` is an isomorphism of Thom pairs
`(i^* E, (i^* E)₀) ≅ (E|_W, E₀|_W)`. -/
instance isIso_pullbackSubtypeValThomPairMap (W : Set B) :
    IsIso (pullbackSubtypeValThomPairMap F E W) := by
  let g : C(↥(π F E ⁻¹' W), TotalSpace F ((⇑(ContinuousMap.subtypeVal W)) *ᵖ E)) :=
    ⟨fun v ↦ TotalSpace.mk' F (⟨v.1.proj, v.2⟩ : W) v.1.2,
      Bundle.Pullback.continuous_iff.2
        ⟨((FiberBundle.continuous_proj F E).comp continuous_subtype_val).subtype_mk _,
          continuous_subtype_val⟩⟩
  have : IsIso (TopPair.Hom.fst (pullbackSubtypeValThomPairMap F E W)) :=
    ⟨TopCat.ofHom g, TopCat.ext fun ⟨⟨_, _⟩, _⟩ ↦ rfl, TopCat.ext fun ⟨⟨_, _⟩, _⟩ ↦ rfl⟩
  exact TopPair.isIso_of_isIso_fst_of_surjective_snd _ fun ⟨⟨b, x⟩, hb, hx⟩ ↦
    ⟨⟨TotalSpace.mk' F (⟨b, hb⟩ : W) x,
      (mem_zeroSectionCompl (E := (⇑(ContinuousMap.subtypeVal W)) *ᵖ E)).2
        ((mem_zeroSectionCompl (E := E)).1 hx)⟩, rfl⟩

end PullbackSubtypeVal

section ThomMapOver

variable {B : Type w} [TopologicalSpace B] (F : Type*) [TopologicalSpace F]
  (E : B → Type w) [TopologicalSpace (TotalSpace F E)] [∀ b, Zero (E b)]
  [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Thom map over a subset `W` of the base**: the `K`-bilinear map sending a global relative
class `u ∈ Hⁿ(E, E₀; K)` and `a ∈ Hᵖ(W; M)` to `(π|_W)^* a ⌣ (u|_W) ∈ Hᵐ(E|_W, E₀|_W; M)`, for
`p + n = m`. -/
def thomMapOver (W : Set B) (n p m : ℕ) (h : p + n = m) :
    (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n →ₗ[K]
      (TopCat.of ↥W).singularCohomology (ModuleCat.of K K) K M p →ₗ[K]
        (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  TopCat.pullbackCupRestrict (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩)
    (zeroSectionCompl F E) M W n p m h

/-- `thomMapOver` is `TopCat.pullbackCupRestrict` of the bundle projection and `zeroSectionCompl`,
so the Mayer–Vietoris gluing theorem `TopCat.bijective_pullbackCupRestrict_union` applies to it. -/
theorem thomMapOver_def (W : Set B) (n p m : ℕ) (h : p + n = m) :
    thomMapOver F E M W n p m h =
      TopCat.pullbackCupRestrict (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩)
        (zeroSectionCompl F E) M W n p m h :=
  (rfl)

variable {M}

/-- Evaluating `thomMapOver` at `u` gives `TopPair.pullbackCup` along `restrictPreimage W` of the
bundle projection and the restriction of `u` to `(E|_W, E₀|_W)`. -/
theorem thomMapOver_apply (W : Set B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    thomMapOver F E M W n p m h u =
      (thomPairOver F E W).pullbackCup M
        (TopCat.ofHom (ContinuousMap.restrictPreimage ⟨π F E, FiberBundle.continuous_proj F E⟩ W))
        n p m h
        (TopPair.singularCohomologyMap
          (TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E))
            (π F E) (zeroSectionCompl F E) W) n u) :=
  TopCat.pullbackCupRestrict_apply (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩)
    (zeroSectionCompl F E) M W h u

/-- **Naturality of `thomMapOver` in the subset**: for `W ⊆ W'`, restricting `a ∈ Hᵖ(W'; M)` to `W`
and applying `thomMapOver` over `W` agrees with applying `thomMapOver` over `W'` and restricting
along `thomPairOverMap`. -/
theorem thomMapOver_naturality {W W' : Set B} (hWW' : W ⊆ W') {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n)
    (a : (TopCat.of ↥W').singularCohomology (ModuleCat.of K K) K M p) :
    thomMapOver F E M W n p m h u
        (TopCat.singularCohomologyMap (TopCat.ofHom (ContinuousMap.inclusion hWW')) p a) =
      TopPair.singularCohomologyMap (thomPairOverMap F E hWW') m
        (thomMapOver F E M W' n p m h u a) := by
  refine (TopCat.pullbackCupRestrict_naturality
    (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩)
    (zeroSectionCompl F E) M hWW' h u a).trans ?_
  refine congrArg (fun φ ↦ TopPair.singularCohomologyMap φ m
    (thomMapOver F E M W' n p m h u a)) ?_
  exact TopPair.hom_ext_of_fst _ (TopCat.ext fun x ↦
    (TopPair.ofInclusionMap_fst_apply _ _ x).trans (thomPairOverMap_fst_apply F E hWW' x).symm)

/-- Over `Set.univ`, `thomMapOver` is bijective if and only if `thomMap` is. -/
theorem bijective_thomMapOver_univ_iff {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (thomMapOver F E M univ n p m h u) ↔
      Function.Bijective (thomMap F E M n p m h u) := by
  rw [thomMapOver_def, thomMap_def, thomPairProj_def]
  exact TopCat.bijective_pullbackCupRestrict_univ_iff _ _ M h u

/-- Over the empty set `∅ ⊆ B`, `thomMapOver` is bijective in every degree because both domain and
codomain vanish. -/
theorem bijective_thomMapOver_empty {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (thomMapOver F E M ∅ n p m h u) := by
  have : Subsingleton ((TopCat.of ↥(∅ : Set B)).singularCohomology (ModuleCat.of K K) K M p) :=
    ModuleCat.subsingleton_of_isZero (isZero_singularCohomology_of_isEmpty
      (ModuleCat.of K K) K M (TopCat.of ↥(∅ : Set B)) p)
  have : Subsingleton ((thomPairOver F E ∅).singularCohomology (ModuleCat.of K K) K M m) :=
    ModuleCat.subsingleton_of_isZero
      (TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of K K) M m
        fun j _ ↦ isZero_singularHomology_thomPairOver_empty (ModuleCat.of K K) j)
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

attribute [local instance] pullbackFiberZero in
/-- Over any subset `W ⊆ B`, `thomMapOver` of `u` is bijective if and only if `thomMap` of the
pulled-back class `i^* u` on the pullback bundle `i^* E` along `i = ContinuousMap.subtypeVal W` is
bijective. -/
theorem bijective_thomMapOver_iff_pullback (W : Set B) {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (thomMapOver F E M W n p m h u) ↔
      Function.Bijective (thomMap F ((⇑(ContinuousMap.subtypeVal W)) *ᵖ E) M n p m h
        (TopPair.singularCohomologyMap
          (pullbackThomPairMap F E (ContinuousMap.subtypeVal W)) n u)) := by
  rw [thomMapOver_apply, thomMap_def,
    ← pullbackSubtypeValThomPairMap_comp_restrictPreimagePairMap F E W,
    TopPair.singularCohomologyMap_comp_apply]
  have hcomm : TopPair.Hom.fst (pullbackSubtypeValThomPairMap F E W) ≫
      TopCat.ofHom (ContinuousMap.restrictPreimage ⟨π F E, FiberBundle.continuous_proj F E⟩ W) =
      thomPairProj F ((⇑(ContinuousMap.subtypeVal W)) *ᵖ E) ≫ 𝟙 (TopCat.of ↥W) :=
    TopCat.ext fun v ↦ Subtype.ext (congrArg Subtype.val (thomPairProj_apply F _ v).symm)
  exact (TopPair.bijective_pullbackCup_iff_of_isIso (pullbackSubtypeValThomPairMap F E W)
    (𝟙 (TopCat.of ↥W)) hcomm h _).symm

end ThomMapOver

end TauCeti

/-! ### Single linear trivialization -/

namespace Bundle.Trivialization

open TauCeti

section SingleTrivialization

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **Local Thom isomorphism over a subset of a trivializing set**: if `W ⊆ e.baseSet` for a linear
trivialization `e`, `F` is finite-dimensional, and `u` restricts to a generator of
`Hʳ(E_b, E_b ∖ {0}; K)` for every `b ∈ W`, then `thomMapOver` of `u` over `W` is bijective in every
degree. `W` need not be open, and `u` need not generate on fibres outside `W`. -/
theorem bijective_thomMapOver_of_forall_mem [FiniteDimensional ℝ F] {W : Set B}
    (hW : W ⊆ e.baseSet) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ W, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective (thomMapOver F E M W (finrank ℝ F) p m h u) := by
  let proj : TopCat.of (TotalSpace F E) ⟶ TopCat.of B :=
    TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩
  rw [thomMapOver_def, TopCat.pullbackCupRestrict_apply]
  have hproj : TopPair.Hom.fst (e.thomPairOverIso ℝ hW).hom ≫ prodThomPairProj W F =
      TopCat.ofHom (proj.hom.restrictPreimage W) :=
    TopCat.ext fun v ↦ (congrArg (prodThomPairProj W F)
      (e.thomPairOverIso_hom_fst_apply ℝ hW v)).trans (prodThomPairProj_apply F _)
  have hcomm : TopPair.Hom.fst (e.thomPairOverIso ℝ hW).inv ≫
      TopCat.ofHom (proj.hom.restrictPreimage W) = prodThomPairProj W F ≫ 𝟙 (TopCat.of ↥W) := by
    rw [Category.comp_id, ← hproj, ← Category.assoc, ← TopPair.Hom.fst_comp, Iso.inv_hom_id,
      TopPair.Hom.fst_id, Category.id_comp]
  refine (TopPair.bijective_pullbackCup_iff_of_isIso (e.thomPairOverIso ℝ hW).inv (𝟙 (TopCat.of ↥W))
    hcomm h _).1 (bijective_pullbackCup_prodThomPair M h fun ⟨b, hb⟩ ↦ ?_)
  have hfib : prodThomPairFiberMap F (⟨b, hb⟩ : W) ≫ (e.thomPairOverIso ℝ hW).inv ≫
      TopCat.restrictPreimagePairMap proj (zeroSectionCompl F E) W =
      (e.continuousLinearEquivAt ℝ b (hW hb)).complZeroPairIso.inv ≫
        fiberThomPairMap F E b := by
    have h1 := congrArg (fun φ ↦ (e.continuousLinearEquivAt ℝ b (hW hb)).complZeroPairIso.inv ≫
      φ ≫ (e.thomPairOverIso ℝ hW).inv) (e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW hb)
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Iso.inv_hom_id_assoc] at h1
    have h2 : fiberThomPairOverMap F E hb ≫
        TopCat.restrictPreimagePairMap proj (zeroSectionCompl F E) W = fiberThomPairMap F E b :=
      fiberThomPairOverMap_comp_restrictPreimagePairMap F E hb
    rw [← Category.assoc, ← h1, Category.assoc, h2]
  rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
    Category.assoc, hfib, TopPair.singularCohomologyMap_comp_apply]
  exact ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K (ModuleCat.of K K)
    (finrank ℝ F)).mapIso
      (e.continuousLinearEquivAt ℝ b (hW hb)).complZeroPairIso.symm.op
    ).toLinearEquiv.span_singleton_apply_eq_top_iff.2 (hu b hb)

/-- **Local Thom isomorphism over `W ⊆ e.baseSet`** for a Thom class `u` of `E`. -/
theorem bijective_thomMapOver {W : Set B} (hW : W ⊆ e.baseSet) {p m : ℕ}
    (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMapOver F E M W (finrank ℝ F) p m h u) := by
  obtain ⟨_, hfib⟩ := isThomClass_iff.1 hu
  exact e.bijective_thomMapOver_of_forall_mem M hW h fun b _ ↦ hfib b

/-- **Local Thom linear equivalence** `Hᵖ(W; M) ≃ₗ[K] Hᵐ(E|_W, E₀|_W; M)` over `W ⊆ e.baseSet`. -/
def thomEquivOver {W : Set B} (hW : W ⊆ e.baseSet) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (TopCat.of ↥W).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMapOver F E M W (finrank ℝ F) p m h u)
    (e.bijective_thomMapOver M hW h hu)

@[simp]
theorem thomEquivOver_apply {W : Set B} (hW : W ⊆ e.baseSet) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of ↥W).singularCohomology (ModuleCat.of K K) K M p) :
    e.thomEquivOver M hW h hu a = thomMapOver F E M W (finrank ℝ F) p m h u a :=
  (rfl)

/-- **Global Thom isomorphism for a globally trivializable bundle**: if `e.baseSet = Set.univ` for
a linear trivialization `e`, then `thomMap` of any Thom class `u` is bijective in every degree. -/
theorem bijective_thomMap (he : e.baseSet = univ) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) :=
  (bijective_thomMapOver_univ_iff F E h u).1 (e.bijective_thomMapOver M he.symm.subset h hu)

/-- **Global Thom linear equivalence** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` from a global linear
trivialization `e.baseSet = Set.univ`. -/
def thomEquiv (he : e.baseSet = univ) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u) (e.bijective_thomMap M he h hu)

@[simp]
theorem thomEquiv_apply (he : e.baseSet = univ) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    e.thomEquiv M he h hu a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

end SingleTrivialization

end Bundle.Trivialization

/-! ### Finite unions of trivializing sets, finite covers, and compact bases -/

namespace TauCeti

section TrivialBundle

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Thom isomorphism for `Bundle.Trivial B F`**: for any Thom class `u` of the trivial bundle,
`thomMap` is bijective in every degree. -/
theorem IsThomClass.bijective_thomMap_trivial {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u) :
    Function.Bijective (thomMap F (Bundle.Trivial B F) M (finrank ℝ F) p m h u) :=
  (Bundle.Trivial.trivialization B F).bijective_thomMap M
    (Bundle.Trivial.trivialization_baseSet B F) h hu

/-- **The Thom linear equivalence** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` for `Bundle.Trivial B F`. -/
def IsThomClass.trivialThomEquiv {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F (Bundle.Trivial B F)).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F (Bundle.Trivial B F) M (finrank ℝ F) p m h u)
    (hu.bijective_thomMap_trivial M h)

@[simp]
theorem IsThomClass.trivialThomEquiv_apply {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu.trivialThomEquiv M h a = thomMap F (Bundle.Trivial B F) M (finrank ℝ F) p m h u a :=
  (rfl)

end TrivialBundle

section FiniteCover

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- Open-set Mayer–Vietoris induction for `bijective_thomMapOver_biUnion`: when each `W i` is open
and contained in a linear trivialization, induction on `s : Finset ι` glues bijectivity via
`TopCat.bijective_pullbackCupRestrict_union`. -/
private theorem bijective_thomMapOver_biUnion_of_isOpen [FiniteDimensional ℝ F] {ι : Type*}
    (s : Finset ι) {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective (thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  -- `Finset.induction_on` requires decidable equality on the cover index type `ι`.
  classical
  induction s using Finset.induction_on generalizing W p m with
  | empty =>
    have hempty : (⋃ i ∈ (∅ : Finset ι), W i) = ∅ := by simp
    rw [hempty]
    exact bijective_thomMapOver_empty F E h u
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert] at hu ⊢
    obtain ⟨e, he, hWa⟩ := hWe a (Finset.mem_insert_self a s)
    have hWa_open : IsOpen (W a) := hWo a (Finset.mem_insert_self a s)
    have hs_open : IsOpen (⋃ i ∈ s, W i) :=
      isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi)
    have hWo' (i : ι) (hi : i ∈ s) : IsOpen (W a ∩ W i) :=
      hWa_open.inter (hWo i (Finset.mem_insert_of_mem hi))
    have hWe' (i : ι) (hi : i ∈ s) :
        ∃ (e' : Trivialization F (π F E)) (_ : e'.IsLinear ℝ), W a ∩ W i ⊆ e'.baseSet := by
      obtain ⟨e', he', hi'⟩ := hWe i (Finset.mem_insert_of_mem hi)
      exact ⟨e', he', inter_subset_right.trans hi'⟩
    refine TopCat.bijective_pullbackCupRestrict_union
      (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) M
      hWa_open hs_open u
      (fun q _ ↦ e.bijective_thomMapOver_of_forall_mem M hWa rfl fun b hb ↦ hu b (Or.inl hb))
      (fun q _ ↦ ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi)) rfl fun b hb ↦ hu b (Or.inr hb))
      (fun q _ ↦ by
        rw [inter_iUnion₂]
        exact ih hWo' hWe' rfl fun b hb ↦ by
          rw [← inter_iUnion₂] at hb
          exact hu b (Or.inl hb.1))
      (fun j hj ↦ by
        rw [inter_iUnion₂]
        exact isZero_singularCohomology_thomPairOver_biUnion (ModuleCat.of K K) M s
          hWo' hWe' (by omega))
      h

/-- **The Thom isomorphism over a finite union of trivializing sets**: if each `W i`, `i ∈ s`, lies
in the base set of a linear trivialization of `E`, `F` is finite-dimensional, and
`u ∈ Hʳ(E, E₀; K)` restricts to a generator of `Hʳ(E_b, E_b ∖ {0}; K)` for every
`b ∈ ⋃ i ∈ s, W i`, then `thomMapOver` of `u` over `⋃ i ∈ s, W i` is bijective in every degree `p`
and for every `K`-module `M`. Neither openness of the sets `W i` nor generation outside
`⋃ i ∈ s, W i` is required. -/
theorem bijective_thomMapOver_biUnion [FiniteDimensional ℝ F] {ι : Type*} (s : Finset ι)
    {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective (thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  let Y : Set B := ⋃ i ∈ s, W i
  let f : C(Y, B) := ContinuousMap.subtypeVal Y
  refine (bijective_thomMapOver_iff_pullback F E Y h u).2 ?_
  refine (bijective_thomMapOver_univ_iff F ((⇑f) *ᵖ E) h _).1 ?_
  let U (i : {i // i ∈ s}) : Set Y := ((hWe i.1 i.2).choose.pullback f).baseSet
  have hU_univ : (⋃ i ∈ s.attach, U i) = univ := by
    refine eq_univ_of_forall fun ⟨b, hb⟩ ↦ ?_
    obtain ⟨i, hi, hbi⟩ := mem_iUnion₂.1 hb
    exact mem_iUnion₂.2 ⟨⟨i, hi⟩, Finset.mem_attach s ⟨i, hi⟩,
      (hWe i hi).choose_spec.choose_spec hbi⟩
  rw [← hU_univ]
  refine bijective_thomMapOver_biUnion_of_isOpen (E := (⇑f) *ᵖ E) M s.attach
    (fun i _ ↦ ((hWe i.1 i.2).choose.pullback f).open_baseSet)
    (fun i _ ↦ ?_) h fun y _ ↦ ?_
  · have : (hWe i.1 i.2).choose.IsLinear ℝ := (hWe i.1 i.2).choose_spec.choose
    exact ⟨(hWe i.1 i.2).choose.pullback f, inferInstance, subset_rfl⟩
  · -- On `f *ᵖ E`, the `Zero` instance in `pullbackThomPairMap` and the one from `AddCommMonoid`
    -- agree up to unfolding `Pullback`, so `congrArg` at default transparency identifies the
    -- composite fibre map.
    have hfib : TopPair.singularCohomologyMap (fiberThomPairMap F ((⇑f) *ᵖ E) y) (finrank ℝ F)
        (TopPair.singularCohomologyMap (pullbackThomPairMap F E f) (finrank ℝ F) u) =
        TopPair.singularCohomologyMap (fiberThomPairMap F E y.1) (finrank ℝ F) u :=
      (TopPair.singularCohomologyMap_comp_apply _ _ _ _).symm.trans <|
        congrArg (fun φ ↦ TopPair.singularCohomologyMap φ (finrank ℝ F) u)
          (fiberThomPairMap_comp_pullbackThomPairMap F E f y)
    rw [hfib]
    exact hu y.1 y.2

/-- **The Thom isomorphism over a finite union of trivializing sets** for a Thom class `u`. -/
theorem IsThomClass.bijective_thomMapOver_biUnion {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  obtain ⟨_, hfib⟩ := isThomClass_iff.1 hu
  exact TauCeti.bijective_thomMapOver_biUnion M s hWe h fun b _ ↦ hfib b

/-- **The Thom linear equivalence** `Hᵖ(W; M) ≃ₗ[K] Hᵐ(E|_W, E₀|_W; M)` over a finite union
`W = ⋃ i ∈ s, W i` of trivializing sets. -/
def IsThomClass.thomEquivOverBiUnion {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (TopCat.of ↥(⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPairOver F E (⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u)
    (hu.bijective_thomMapOver_biUnion M s hWe h)

@[simp]
theorem IsThomClass.thomEquivOverBiUnion_apply {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of ↥(⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M p) :
    hu.thomEquivOverBiUnion M s hWe h a =
      thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u a :=
  (rfl)

/-- **The Thom isomorphism for a bundle with a finite trivializing cover**: if finitely many sets
`W i`, `i ∈ s`, cover `B` and each lies in the base set of a linear trivialization of `E`, then
`thomMap` of any Thom class `u` is bijective in every degree `p` and for every `K`-module `M`. -/
theorem IsThomClass.bijective_thomMap_of_biUnion_eq_univ {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hW : ⋃ i ∈ s, W i = univ)
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  refine (bijective_thomMapOver_univ_iff F E h u).1 ?_
  rw [← hW]
  exact hu.bijective_thomMapOver_biUnion M s hWe h

/-- **The Thom linear equivalence** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` for a bundle admitting a finite
trivializing cover `⋃ i ∈ s, W i = Set.univ`. -/
def IsThomClass.thomEquivOfBiUnionEqUniv {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hW : ⋃ i ∈ s, W i = univ)
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u)
    (hu.bijective_thomMap_of_biUnion_eq_univ M s hW hWe h)

@[simp]
theorem IsThomClass.thomEquivOfBiUnionEqUniv_apply {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hW : ⋃ i ∈ s, W i = univ)
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu.thomEquivOfBiUnionEqUniv M s hW hWe h a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

/-- **The Thom isomorphism over a compact base**: for a real vector bundle `E → B` over a compact
space `B` and a Thom class `u ∈ Hʳ(E, E₀; K)`, the Thom map `Hᵖ(B; M) ⟶ Hᵐ(E, E₀; M)` is bijective
in every degree `p` and for every `K`-module `M`. -/
theorem IsThomClass.bijective_thomMap_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet) (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
  exact hu.bijective_thomMap_of_biUnion_eq_univ M t (univ_subset_iff.1 ht)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) h

/-- **The Thom linear equivalence** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` over a compact base `B`. -/
def IsThomClass.thomEquivOfCompactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u)
    (hu.bijective_thomMap_of_compactSpace M h)

@[simp]
theorem IsThomClass.thomEquivOfCompactSpace_apply [CompactSpace B] [VectorBundle ℝ F E]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu.thomEquivOfCompactSpace M h a = thomMap F E M (finrank ℝ F) p m h u a :=
  (rfl)

end FiniteCover

/-! ### Unoriented mod-2, oriented, and homological specializations -/

section SubsingletonUnits

variable {B : Type w} [TopologicalSpace B] (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  (K : Type w) [CommRing K] [Subsingleton Kˣ]

/-- **The canonical Thom class** of a real vector bundle over a commutative ring `K` whose group of
units is a subsingleton (for example `ZMod 2`), selected by
`TauCeti.existsUnique_isThomClass_of_subsingleton_units`. No orientation of `E` is needed. -/
def thomClassOfSubsingletonUnits :
    (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F) :=
  (existsUnique_isThomClass_of_subsingleton_units (F := F) (E := E) K).exists.choose

/-- `thomClassOfSubsingletonUnits` is a Thom class of `E`. -/
theorem isThomClass_thomClassOfSubsingletonUnits :
    IsThomClass F E (thomClassOfSubsingletonUnits F E K) :=
  (existsUnique_isThomClass_of_subsingleton_units (F := F) (E := E) K).exists.choose_spec

/-- When `Kˣ` is a subsingleton, every Thom class of `E` equals `thomClassOfSubsingletonUnits`. -/
theorem eq_thomClassOfSubsingletonUnits_of_isThomClass
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    u = thomClassOfSubsingletonUnits F E K :=
  (existsUnique_isThomClass_of_subsingleton_units (F := F) (E := E) K).unique hu
    (isThomClass_thomClassOfSubsingletonUnits F E K)

variable {K}

/-- **Canonical unoriented Thom linear equivalence** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` over a compact
base when `Kˣ` is a subsingleton (such as `ZMod 2`). -/
def thomEquivOfSubsingletonUnitsOfCompactSpace [CompactSpace B] (M : ModuleCat.{w} K) {p m : ℕ}
    (h : p + finrank ℝ F = m) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  (isThomClass_thomClassOfSubsingletonUnits F E K).thomEquivOfCompactSpace M h

@[simp]
theorem thomEquivOfSubsingletonUnitsOfCompactSpace_apply [CompactSpace B] (M : ModuleCat.{w} K)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOfSubsingletonUnitsOfCompactSpace F E M h a =
      thomMap F E M (finrank ℝ F) p m h (thomClassOfSubsingletonUnits F E K) a :=
  (rfl)

end SubsingletonUnits

section Oriented

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E] {ι : Type*} [Fintype ι]
  {K : Type w} [CommRing K]

/-- **The oriented Thom isomorphism over a compact base**: for an oriented real vector bundle
`o : VectorBundleOrientation F E ι` over a compact space `B`, an orientation `ω` of `F`, and a
generator `g` of `Hʳ(F, F ∖ {0}; K)`, the Thom map of `o.thomClassOfModel hι ω g` is bijective in
every degree. -/
theorem VectorBundleOrientation.bijective_thomMap_thomClassOfModel_of_compactSpace [CompactSpace B]
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) :
    Function.Bijective
      (thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g)) :=
  (o.isThomClass_thomClassOfModel hι ω hg).bijective_thomMap_of_compactSpace M h

/-- **The oriented Thom linear equivalence** `Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` over a compact base `B`
associated to `o.thomClassOfModel hι ω g`. -/
def VectorBundleOrientation.thomEquivOfModelOfCompactSpace [CompactSpace B]
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  (o.isThomClass_thomClassOfModel hι ω hg).thomEquivOfCompactSpace M h

@[simp]
theorem VectorBundleOrientation.thomEquivOfModelOfCompactSpace_apply [CompactSpace B]
    (o : VectorBundleOrientation F E ι) (hι : Fintype.card ι = finrank ℝ F)
    (ω : Orientation ℝ F ι) (M : ModuleCat.{w} K) {p m : ℕ} (h : p + finrank ℝ F = m)
    {g : (TopPair.ofSubset (X := TopCat.of F) ({0}ᶜ : Set F)).singularCohomology
      (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hg : Submodule.span K {g} = ⊤)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    o.thomEquivOfModelOfCompactSpace hι ω M h hg a =
      thomMap F E M (finrank ℝ F) p m h (o.thomClassOfModel hι ω g) a :=
  (rfl)

end Oriented

section Homology

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [Field K]

/-- **The homological Thom isomorphism over a finite trivializing cover** with coefficients in a
field `K`: `x ↦ π_*(x ⌢ u)` (`TauCeti.homologyThomMap`) is bijective in every degree. -/
theorem IsThomClass.bijective_homologyThomMap_of_biUnion_eq_univ {ι : Type*} (s : Finset ι)
    {W : ι → Set B} (hW : ⋃ i ∈ s, W i = univ)
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective
      (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (bijective_homologyThomMap_iff F E h u).2
    (hu.bijective_thomMap_of_biUnion_eq_univ (ModuleCat.of K K) s hW hWe (by omega))

/-- **The homological Thom isomorphism over a compact base** with coefficients in a field `K`:
`Hₘ(E, E₀; K) ⟶ Hₚ(B; K)`, `x ↦ π_*(x ⌢ u)`, is bijective whenever `finrank ℝ F + p = m`. -/
theorem IsThomClass.bijective_homologyThomMap_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective
      (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (bijective_homologyThomMap_iff F E h u).2
    (hu.bijective_thomMap_of_compactSpace (ModuleCat.of K K) (by omega))

/-- **The homological Thom isomorphism** `Hₘ(E, E₀; K) ≅ Hₚ(B; K)` in `ModuleCat K` over a compact
base with coefficients in a field `K`. -/
def IsThomClass.homologyThomIsoOfCompactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (thomPair F E).singularHomology (ModuleCat.of K K) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{w} K) p).obj
        (ModuleCat.of K K)).obj (TopCat.of B) :=
  have : IsIso (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) :=
    (ConcreteCategory.isIso_iff_bijective _).2 (hu.bijective_homologyThomMap_of_compactSpace h)
  asIso (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u)

@[simp]
theorem IsThomClass.homologyThomIsoOfCompactSpace_hom [CompactSpace B] [VectorBundle ℝ F E]
    {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (hu.homologyThomIsoOfCompactSpace h).hom =
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u :=
  (rfl)

end Homology

end TauCeti
