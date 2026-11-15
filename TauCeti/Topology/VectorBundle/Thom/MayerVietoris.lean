/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.PullbackCup
public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Thom.Homology

/-!
# The Thom isomorphism of a real vector bundle

Let `E → B` be a real vector bundle with model fibre `F` of rank `r = finrank ℝ F` and Thom pair
`(E, E₀)`, `E₀` the complement of the zero section, and let `u ∈ Hʳ(E, E₀; K)` be a Thom class
(`TauCeti.IsThomClass`) with coefficients in a commutative ring `K`. This file proves that the
Thom map `Φ_u : Hᵖ(B; M) ⟶ Hᵖ⁺ʳ(E, E₀; M)`, `a ↦ π^*a ⌣ u` (`TauCeti.thomMap`), is bijective:

* Over any subset `W` contained in the base set of a linear trivialization, the restricted map
  `TopCat.pullbackCupRestrict` is transported by `Bundle.Trivialization.thomPairOverIso` to the
  product bundle `W × F`, where it is bijective by `TauCeti.bijective_pullbackCup_prodThomPair`
  (`Bundle.Trivialization.bijective_pullbackCupRestrict_thomPairProj`).
* By induction on a finite family of trivializing open sets, using the Mayer–Vietoris step
  `TopCat.bijective_pullbackCupRestrict_union` and the vanishing of relative cohomology below the
  rank (`TauCeti.isZero_singularCohomology_thomPairOver_biUnion`), the restricted map is bijective
  over any finite union of trivializing open sets
  (`TauCeti.bijective_pullbackCupRestrict_thomPairProj_biUnion`).
* Consequently, for **any commutative ring `K` and any `K`-module `M`**, `Φ_u` is bijective whenever
  `B` is covered by finitely many trivializing open sets
  (`TauCeti.IsThomClass.bijective_thomMap_of_biUnion_eq_univ`) — in particular for any
  trivializable bundle (`Bundle.Trivialization.bijective_thomMap`,
  `TauCeti.IsThomClass.bijective_thomMap_trivial`) and over any compact base
  (`TauCeti.IsThomClass.bijective_thomMap_of_compactSpace`,
  `TauCeti.IsThomClass.thomEquivOfCompactSpace`).
* Over **any field `K` and an arbitrary base `B`** (with no compactness assumption), the homology
  Thom maps over the finite unions of `trivializationAt F E b` are isomorphisms by Kronecker
  duality, and passing to the filtered colimit (`TauCeti.isColimitMapCoconeSingularHomology` and
  `TauCeti.isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion`) shows that the
  homology Thom map `Hₘ(E, E₀; K) ⟶ Hₚ(B; K)` is an isomorphism
  (`TauCeti.IsThomClass.homologyThomIso`); by `TauCeti.bijective_homologyThomMap_iff`, the
  cohomology Thom map `Hᵖ(B; K) ⟶ Hᵐ(E, E₀; K)` is likewise an isomorphism
  (`TauCeti.IsThomClass.thomEquivOfField`).
* When `K` has `Subsingleton Kˣ` (for instance `ZMod 2`), every finite-rank real vector bundle has a
  canonical Thom class `TauCeti.thomClassOfSubsingletonUnits` without any orientation assumption,
  yielding the unoriented mod-`2` Thom isomorphism over an arbitrary base.

## Main definitions and results

* `Bundle.Trivialization.bijective_pullbackCupRestrict_thomPairProj`: local bijectivity over a
  subset of a trivializing set.
* `TauCeti.bijective_pullbackCupRestrict_thomPairProj_biUnion`: bijectivity over a finite union of
  trivializing open sets.
* `TauCeti.IsThomClass.bijective_thomMap_of_biUnion_eq_univ`,
  `Bundle.Trivialization.bijective_thomMap`, `TauCeti.IsThomClass.bijective_thomMap_trivial`,
  `TauCeti.IsThomClass.bijective_thomMap_of_compactSpace`,
  `TauCeti.IsThomClass.thomEquivOfCompactSpace`: the Thom isomorphism for arbitrary ring and module
  coefficients.
* `TauCeti.IsThomClass.isIso_homologyThomMap`, `TauCeti.IsThomClass.homologyThomIso`,
  `TauCeti.IsThomClass.bijective_homologyThomMap`, `TauCeti.IsThomClass.bijective_thomMap_of_field`,
  `TauCeti.IsThomClass.thomEquivOfField`: the homology and cohomology Thom isomorphisms over a field
  and an arbitrary base.
* `TauCeti.thomClassOfSubsingletonUnits`, `TauCeti.isThomClass_thomClassOfSubsingletonUnits`,
  `TauCeti.eq_thomClassOfSubsingletonUnits_of_isThomClass`,
  `TauCeti.homologyThomIsoOfSubsingletonUnits`, `TauCeti.thomEquivOfSubsingletonUnits`: the
  canonical unoriented Thom class and Thom isomorphisms when `Subsingleton Kˣ` (e.g. `ZMod 2`).

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), §4.D, Theorem 4D.10.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits MonoidalCategory Set Module AlgebraicTopology

universe w

namespace Bundle.Trivialization

open TauCeti

section Local

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  (e : Trivialization F (π F E)) [e.IsLinear ℝ]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

include e in
/-- **Local Thom isomorphism over a trivializing set.** For `W ⊆ e.baseSet` and a class
`u ∈ Hʳ(E, E₀; K)`, `r = finrank ℝ F`, whose restriction to the fibre pair `(E_b, E_b ∖ {0})` over
every `b ∈ W` generates `Hʳ(E_b, E_b ∖ {0}; K)`, the restricted map `TopCat.pullbackCupRestrict`
from `Hᵖ(W; M)` to `Hᵐ(E|_W, E₀|_W; M)` (`p + r = m`) is bijective. -/
theorem bijective_pullbackCupRestrict_thomPairProj [FiniteDimensional ℝ F] {W : Set B}
    (hW : W ⊆ e.baseSet) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ W, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective (TopCat.pullbackCupRestrict
      (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) M W
      (finrank ℝ F) p m h u) := by
  let π₀ : TopCat.of (TotalSpace F E) ⟶ TopCat.of B :=
    TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩
  let φ := e.thomPairOverIso ℝ hW
  have hproj : TopPair.Hom.fst φ.inv ≫ TopCat.ofHom (π₀.hom.restrictPreimage W) =
      prodThomPairProj W F ≫ 𝟙 (TopCat.of ↥W) :=
    TopCat.ext fun p ↦ by
      have hp : TopPair.Hom.fst φ.hom (TopPair.Hom.fst φ.inv p) = p :=
        (TopPair.proj₁.mapIso φ).inv_hom_id_apply p
      have hp1 : (⟨(TopPair.Hom.fst φ.inv p).1.proj, (TopPair.Hom.fst φ.inv p).2⟩ : W) = p.1 :=
        congrArg Prod.fst ((e.thomPairOverIso_hom_fst_apply ℝ hW _).symm.trans hp)
      exact hp1.trans (prodThomPairProj_apply F p).symm
  rw [TopCat.pullbackCupRestrict_apply]
  refine (TopPair.bijective_pullbackCup_iff_of_isIso φ.inv (𝟙 (TopCat.of ↥W)) hproj h _).1 ?_
  refine bijective_pullbackCup_prodThomPair M h fun b ↦ ?_
  have hφb : prodThomPairFiberMap F b ≫ φ.inv =
      (e.continuousLinearEquivAt ℝ b (hW b.2)).complZeroPairIso.inv ≫
        fiberThomPairOverMap F E b.2 := by
    rw [Iso.comp_inv_eq, Category.assoc, Iso.eq_inv_comp,
      e.fiberThomPairOverMap_comp_thomPairOverIso_hom ℝ hW b.2]
  have hfib : prodThomPairFiberMap F b ≫ φ.inv ≫
      TopCat.restrictPreimagePairMap π₀ (zeroSectionCompl F E) W =
        (e.continuousLinearEquivAt ℝ b (hW b.2)).complZeroPairIso.inv ≫
          fiberThomPairMap F E b.1 :=
    (Category.assoc _ _ _).symm.trans ((congrArg
      (· ≫ TopCat.restrictPreimagePairMap π₀ (zeroSectionCompl F E) W) hφb).trans
      ((Category.assoc _ _ _).trans (congrArg _
        (fiberThomPairOverMap_comp_restrictPreimagePairMap F E b.2))))
  have hmap : TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F)
      (TopPair.singularCohomologyMap φ.inv (finrank ℝ F)
        (TopPair.singularCohomologyMap
          (TopCat.restrictPreimagePairMap π₀ (zeroSectionCompl F E) W) (finrank ℝ F) u)) =
    TopPair.singularCohomologyMap
      (e.continuousLinearEquivAt ℝ b (hW b.2)).complZeroPairIso.inv (finrank ℝ F)
        (TopPair.singularCohomologyMap (fiberThomPairMap F E b.1) (finrank ℝ F) u) := by
    have h₁ := (TopPair.singularCohomologyMap_comp_apply φ.inv
      (TopCat.restrictPreimagePairMap π₀ (zeroSectionCompl F E) W) (finrank ℝ F) u).symm
    have h₂ := (TopPair.singularCohomologyMap_comp_apply (prodThomPairFiberMap F b)
      (φ.inv ≫ TopCat.restrictPreimagePairMap π₀ (zeroSectionCompl F E) W) (finrank ℝ F) u).symm
    exact (congrArg (TopPair.singularCohomologyMap (prodThomPairFiberMap F b) (finrank ℝ F))
      h₁).trans (h₂.trans ((congrArg (fun f ↦ TopPair.singularCohomologyMap f (finrank ℝ F) u)
        hfib).trans (TopPair.singularCohomologyMap_comp_apply _ _ (finrank ℝ F) u)))
  rw [hmap]
  let L := ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K (ModuleCat.of K K)
    (finrank ℝ F)).mapIso
      (e.continuousLinearEquivAt ℝ b (hW b.2)).complZeroPairIso.symm.op).toLinearEquiv
  exact L.span_singleton_apply_eq_top_iff.2 (hu b.1 b.2)

include e in
/-- **The Thom isomorphism for a globally trivializable bundle.** -/
theorem bijective_thomMap (he : e.baseSet = univ) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu'⟩ := isThomClass_iff.1 hu
  rw [thomMap_def, thomPairProj_def, ← TopCat.bijective_pullbackCupRestrict_univ_iff]
  exact e.bijective_pullbackCupRestrict_thomPairProj M (he ▸ subset_rfl) h fun b _ ↦ hu' b

end Local

end Bundle.Trivialization

namespace TauCeti

section FiniteUnion

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

/-- **The Thom isomorphism over a finite union of trivializing open sets.** If each `W i`, `i ∈ s`,
is open and contained in the base set of a linear trivialization of `E`, and `u ∈ Hʳ(E, E₀; K)`
(`r = finrank ℝ F`) restricts to a generator on every fibre over `⋃ i ∈ s, W i`, then the restricted
Thom map `TopCat.pullbackCupRestrict` over `⋃ i ∈ s, W i` is bijective in every degree. -/
theorem bijective_pullbackCupRestrict_thomPairProj_biUnion [FiniteDimensional ℝ F] {ι : Type*}
    (s : Finset ι) {W : ι → Set B} (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    Function.Bijective (TopCat.pullbackCupRestrict
      (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) M
      (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  classical
  let π₀ : TopCat.of (TotalSpace F E) ⟶ TopCat.of B :=
    TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩
  induction s using Finset.induction_on generalizing W p m with
  | empty =>
    have hemp : (⋃ i ∈ (∅ : Finset ι), W i) = ∅ := by simp
    rw [hemp]
    have hdom : Subsingleton ((TopCat.of ↥(∅ : Set B)).singularCohomology
        (ModuleCat.of K K) K M p) :=
      ModuleCat.subsingleton_of_isZero
        (isZero_singularCohomology_of_isEmpty (ModuleCat.of K K) K M (TopCat.of ↥(∅ : Set B)) p)
    have hcod : Subsingleton ((TopPair.ofInclusion (inter_subset_left :
        π₀ ⁻¹' (∅ : Set B) ∩ zeroSectionCompl F E ⊆ π₀ ⁻¹' (∅ : Set B))).singularCohomology
          (ModuleCat.of K K) K M m) := by
      refine ModuleCat.subsingleton_of_isZero
        (TopPair.isZero_singularCohomology_of_isZero_singularHomology _ (ModuleCat.of K K) M m
          fun j _ ↦ ?_)
      exact isZero_singularHomology_thomPairOver_empty (F := F) (E := E) (ModuleCat.of K K) j
    exact Function.bijective_iff_has_inverse.2
      ⟨0, fun x ↦ hdom.elim _ x, fun y ↦ hcod.elim _ y⟩
  | insert i₀ s _ ih =>
    rw [Finset.set_biUnion_insert] at hu ⊢
    have hs (i : ι) (hi : i ∈ s) : i ∈ insert i₀ s := Finset.mem_insert_of_mem hi
    obtain ⟨e, _, he⟩ := hWe i₀ (Finset.mem_insert_self i₀ s)
    refine TopCat.bijective_pullbackCupRestrict_union π₀ (zeroSectionCompl F E) M
      (hWo i₀ (Finset.mem_insert_self i₀ s))
      (isOpen_biUnion fun i hi ↦ hWo i (hs i hi)) u
      (fun q _ ↦ e.bijective_pullbackCupRestrict_thomPairProj M he rfl
        fun b hb ↦ hu b (mem_union_left _ hb))
      (fun q _ ↦ ih (fun i hi ↦ hWo i (hs i hi)) (fun i hi ↦ hWe i (hs i hi)) rfl
        fun b hb ↦ hu b (mem_union_right _ hb))
      (fun q _ ↦ ?_) (fun j hj ↦ ?_) h
    · rw [inter_iUnion₂]
      refine ih (fun i hi ↦ (hWo i₀ (Finset.mem_insert_self i₀ s)).inter (hWo i (hs i hi)))
        (fun i _ ↦ ⟨e, inferInstance, inter_subset_left.trans he⟩) rfl fun b hb ↦ ?_
      rcases mem_iUnion₂.1 hb with ⟨_, _, hb'⟩
      exact hu b (mem_union_left _ hb'.1)
    · -- `π₀ ⁻¹' _` is definitionally `π F E ⁻¹' _`, so the inclusion pair is `thomPairOver`.
      change IsZero ((thomPairOver F E (W i₀ ∩ ⋃ i ∈ s, W i)).singularCohomology
        (ModuleCat.of K K) K M j)
      rw [inter_iUnion₂]
      exact isZero_singularCohomology_thomPairOver_biUnion (ModuleCat.of K K) M s
        (fun i hi ↦ (hWo i₀ (Finset.mem_insert_self i₀ s)).inter (hWo i (hs i hi)))
        (fun i _ ↦ ⟨e, inferInstance, inter_subset_left.trans he⟩) (by omega)

/-- **The Thom isomorphism over a finite trivializing open cover.** If `B` is covered by finitely
many open sets, each contained in the base set of a linear trivialization of `E`, then for any Thom
class `u ∈ Hʳ(E, E₀; K)` and any `K`-module `M` the Thom map `Hᵖ(B; M) ⟶ Hᵐ(E, E₀; M)` (`p + r = m`)
is bijective. -/
theorem IsThomClass.bijective_thomMap_of_biUnion_eq_univ {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWcov : ⋃ i ∈ s, W i = univ) (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu'⟩ := isThomClass_iff.1 hu
  rw [thomMap_def, thomPairProj_def, ← TopCat.bijective_pullbackCupRestrict_univ_iff, ← hWcov]
  exact bijective_pullbackCupRestrict_thomPairProj_biUnion M s hWo hWe h fun b _ ↦ hu' b

/-- **The Thom isomorphism for a trivial bundle.** -/
theorem IsThomClass.bijective_thomMap_trivial {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F (Bundle.Trivial B F)).singularCohomology (ModuleCat.of K K) K
      (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F (Bundle.Trivial B F) u) :
    Function.Bijective (thomMap F (Bundle.Trivial B F) M (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu'⟩ := isThomClass_iff.1 hu
  have hproj : TopPair.Hom.fst (trivialThomPairIso B F).inv ≫
      thomPairProj F (Bundle.Trivial B F) = prodThomPairProj B F ≫ 𝟙 (TopCat.of B) := by
    rw [Category.comp_id, thomPairProj_def]
    exact TopCat.ext fun p ↦ (congrArg TotalSpace.proj
      (trivialThomPairIso_inv_fst_apply B F p)).trans (prodThomPairProj_apply F p).symm
  rw [thomMap_def]
  refine (TopPair.bijective_pullbackCup_iff_of_isIso (trivialThomPairIso B F).inv
    (𝟙 (TopCat.of B)) hproj h u).1 ?_
  refine bijective_pullbackCup_prodThomPair M h fun b ↦ ?_
  have hfib : prodThomPairFiberMap F b ≫ (trivialThomPairIso B F).inv =
      fiberThomPairMap F (Bundle.Trivial B F) b := by
    rw [Iso.comp_inv_eq, fiberThomPairMap_comp_trivialThomPairIso_hom]
  rw [← TopPair.singularCohomologyMap_comp_apply, hfib]
  exact hu' b

/-- **The Thom isomorphism over a compact base**, for any commutative ring `K` and any `K`-module
`M`. -/
theorem IsThomClass.bijective_thomMap_of_compactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet)
    (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
  exact hu.bijective_thomMap_of_biUnion_eq_univ M s (univ_subset_iff.1 hs)
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) h

/-- **The Thom isomorphism over a compact base**, bundled as a `K`-linear equivalence
`Hᵖ(B; M) ≃ₗ[K] Hᵐ(E, E₀; M)` (`p + finrank ℝ F = m`). -/
def IsThomClass.thomEquivOfCompactSpace [CompactSpace B] [VectorBundle ℝ F E]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMap F E M (finrank ℝ F) p m h u)
    (hu.bijective_thomMap_of_compactSpace M h)

/-- `TauCeti.IsThomClass.thomEquivOfCompactSpace` evaluates as `TauCeti.thomMap`. -/
@[simp]
theorem IsThomClass.thomEquivOfCompactSpace_apply [CompactSpace B] [VectorBundle ℝ F E]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    hu.thomEquivOfCompactSpace M h a = thomMap F E M (finrank ℝ F) p m h u a :=
  -- `thomEquivOfCompactSpace` is `LinearEquiv.ofBijective` of `thomMap`.
  (rfl)

/-- Left inverse law for `TauCeti.IsThomClass.thomEquivOfCompactSpace` applied to
`TauCeti.thomMap`. -/
@[simp]
theorem IsThomClass.thomEquivOfCompactSpace_symm_apply_thomMap [CompactSpace B] [VectorBundle ℝ F E]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K M p) :
    (hu.thomEquivOfCompactSpace M h).symm (thomMap F E M (finrank ℝ F) p m h u a) = a :=
  (hu.thomEquivOfCompactSpace M h).symm_apply_apply a

end FiniteUnion

section FieldDirectedUnion

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommMonoid (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-- Over a field, if `P.pullbackCup (ModuleCat.of K K) g n p m _ v` is bijective, then its
Kronecker-transpose cap-and-pushforward morphism `Hₘ(P; K) ⟶ Hₚ(Z; K)` is an isomorphism. -/
private theorem isIso_singularCap_comp_map_of_bijective_pullbackCup {K : Type w} [Field K]
    {P : TopPair.{w}} {Z : TopCat.{w}} (g : P.fst ⟶ Z) {n p m : ℕ} (h : n + p = m)
    {v : P.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n}
    (hv : Function.Bijective (P.pullbackCup (ModuleCat.of K K) g n p m (by omega) v)) :
    IsIso (P.singularCap K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom n p m h v ≫
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map g) := by
  set T := P.singularCap K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom n p m h v ≫
    ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map g
  have hc : ((-1 : K) ^ (n * p)) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hkr : ∀ a : Z.singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p,
      T ≫ Z.singularKronecker K p a =
        ((-1 : ℤ) ^ (n * p)) • P.singularKronecker K m
          (P.pullbackCup (ModuleCat.of K K) g n p m (by omega) v a) := fun a ↦ by
    rw [Category.assoc, ← TopCat.singularKronecker_naturality,
      TopPair.singularCap_comp_singularKronecker, TopPair.pullbackCup_apply,
      TopPair.singularCup_gradedComm K P (u := (λ_ (𝟙_ (ModuleCat.{w} K))).inv)
        (u' := (λ_ (ModuleCat.of K K)).inv) (μ' := (λ_ (ModuleCat.of K K)).hom)
        (μ := (ρ_ (ModuleCat.of K K)).hom) ?_ ?_ (by omega), map_zsmul, mul_comm]
    -- `pullbackCup` uses `𝟙_ (ModuleCat K)`, while `singularCap` uses `ModuleCat.of K K`.
    · rfl
    · rw [braiding_tensorUnit_left, Iso.inv_hom_id_assoc, ← unitors_inv_equal]
      rfl
    · exact braiding_leftUnitor _
  have key : ∀ a, P.singularCohomologyDualEquiv m
      (P.pullbackCup (ModuleCat.of K K) g n p m (by omega) v a) =
        LinearEquiv.smulOfNeZero K _ _ hc (T.hom.dualMap (Z.singularCohomologyDualEquiv p a)) := by
    intro a
    ext x
    have hx := congrArg (fun φ ↦ φ.hom x) (hkr a)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zsmul,
      LinearMap.smul_apply] at hx
    rw [LinearEquiv.smulOfNeZero_apply, LinearMap.smul_apply, LinearMap.dualMap_apply,
      TopPair.singularCohomologyDualEquiv_apply, TopCat.singularCohomologyDualEquiv_apply, hx]
    simp [← Int.cast_smul_eq_zsmul K, ← mul_assoc, ← mul_pow]
  have heq : ⇑(P.pullbackCup (ModuleCat.of K K) g n p m (by omega) v) =
      ⇑(P.singularCohomologyDualEquiv m).symm ∘ ⇑(LinearEquiv.smulOfNeZero K _ _ hc) ∘
        ⇑T.hom.dualMap ∘ ⇑(Z.singularCohomologyDualEquiv p) := by
    funext a
    simp only [Function.comp_apply, ← key, LinearEquiv.symm_apply_apply]
  rw [heq, EquivLike.comp_bijective, EquivLike.comp_bijective, EquivLike.bijective_comp,
    LinearMap.dualMap_bijective_iff] at hv
  have hTeq : T = (LinearEquiv.ofBijective T.hom hv).toModuleIso.hom :=
    ModuleCat.hom_ext rfl
  rw [hTeq]
  infer_instance

variable (F E) in
/-- The projection `(E|_W, E₀|_W).fst ⟶ W` of the restricted Thom pair. -/
private def thomPairOverProj (W : Set B) : (thomPairOver F E W).fst ⟶ TopCat.of ↥W :=
  TopCat.ofHom (ContinuousMap.restrictPreimage ⟨π F E, FiberBundle.continuous_proj F E⟩ W)

variable (F E) in
/-- The local homology Thom map `(E|_W, E₀|_W) ⟶ W` associated to `u ∈ Hⁿ(E, E₀; K)`. -/
private def thomPairOverHomologyMap {K : Type w} [CommRing K] (W : Set B) {n p m : ℕ}
    (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    (thomPairOver F E W).singularHomology (ModuleCat.of K K) m ⟶
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj
        (TopCat.of ↥W) :=
  (thomPairOver F E W).singularCap K (λ_ (ModuleCat.of K K)).inv (λ_ (ModuleCat.of K K)).hom
      n p m h (TopPair.singularCohomologyMap (TopCat.restrictPreimagePairMap
        (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) n u) ≫
    ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
      (thomPairOverProj F E W)

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
private theorem thomPairOverHomologyMap_naturality {K : Type w} [CommRing K]
    {W W' : Set B} (hWW' : W ⊆ W') {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    TopPair.singularHomologyMap (thomPairOverMap F E hWW') (ModuleCat.of K K) m ≫
        thomPairOverHomologyMap F E W' h u =
      thomPairOverHomologyMap F E W h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
          (TopCat.ofHom (ContinuousMap.inclusion hWW')) := by
  have hg : TopPair.Hom.fst (thomPairOverMap F E hWW') ≫ thomPairOverProj F E W' =
      thomPairOverProj F E W ≫ TopCat.ofHom (ContinuousMap.inclusion hWW') := by
    rw [thomPairOverMap_fst]
    exact TopCat.ext fun _ ↦ rfl
  dsimp only [thomPairOverHomologyMap]
  rw [← Category.assoc, ← TopPair.singularCap_naturality,
    ← TopPair.singularCohomologyMap_comp_apply, thomPairOverMap_comp_restrictPreimagePairMap,
    Category.assoc, Category.assoc, ← Functor.map_comp, hg, Functor.map_comp]

omit [NormedSpace ℝ F] [∀ b, Module ℝ (E b)] in
private theorem thomPairOverHomologyMap_comp_subtypeVal {K : Type w} [CommRing K]
    (W : Set B) {n p m : ℕ} (h : n + p = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    thomPairOverHomologyMap F E W h u ≫
        ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).map
          (TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) =
      TopPair.singularHomologyMap
          (thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom)
          (ModuleCat.of K K) m ≫
        homologyThomMap F E (ModuleCat.of K K) n p m h u := by
  have hpair : thomPairOverMap F E (subset_univ W) ≫ (thomPairOverUnivIso F E).hom =
      TopCat.restrictPreimagePairMap (X := TopCat.of (TotalSpace F E)) (π F E)
        (zeroSectionCompl F E) W := by
    rw [thomPairOverUnivIso_hom, thomPairOverMap_comp_restrictPreimagePairMap]
  have hg : TopPair.Hom.fst (TopCat.restrictPreimagePairMap
      (X := TopCat.of (TotalSpace F E)) (π F E) (zeroSectionCompl F E) W) ≫
        thomPairProj F E =
      thomPairOverProj F E W ≫ TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ := by
    rw [TopCat.restrictPreimagePairMap_fst, thomPairProj_def]
    exact TopCat.ext fun _ ↦ rfl
  rw [hpair, homologyThomMap_apply]
  dsimp only [thomPairOverHomologyMap]
  rw [Category.assoc, ← Functor.map_comp, ← hg, Functor.map_comp, ← Category.assoc,
    TopPair.singularCap_naturality, Category.assoc]

variable (F E) in
/-- The finite unions of the chosen trivializing open sets, as subspaces of the base. -/
private def baseFiniteTrivializingUnionDiagram : Finset B ⥤ TopCat.{w} where
  obj s := TopCat.of ↥(⋃ b ∈ s, (trivializationAt F E b).baseSet)
  map f := TopCat.ofHom (ContinuousMap.inclusion (biUnion_subset_biUnion_left f.le))

variable (F E) in
/-- The cocone of inclusions of the finite unions of the chosen trivializing open sets into `B`. -/
private def baseFiniteTrivializingUnionCocone :
    Cocone (baseFiniteTrivializingUnionDiagram F E) where
  pt := TopCat.of B
  ι := { app _ := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩ }

/-- **Over any field, the homology Thom map of a Thom class is an isomorphism in every degree, over
an arbitrary base.** -/
theorem IsThomClass.isIso_homologyThomMap [VectorBundle ℝ F E] {K : Type w} [Field K]
    {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    IsIso (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
  obtain ⟨_, hu'⟩ := isThomClass_iff.1 hu
  have hiso (s : Finset B) : IsIso (thomPairOverHomologyMap F E
      (⋃ b ∈ s, (trivializationAt F E b).baseSet) h u) := by
    refine isIso_singularCap_comp_map_of_bijective_pullbackCup _ h ?_
    have hbij := bijective_pullbackCupRestrict_thomPairProj_biUnion (ModuleCat.of K K) s
      (fun b _ ↦ (trivializationAt F E b).open_baseSet)
      (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) (by omega : p + _ = m)
      fun b _ ↦ hu' b
    dsimp only [thomPairOverProj]
    exact (congrArg Function.Bijective (congrArg DFunLike.coe
      (TopCat.pullbackCupRestrict_apply
        (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E)
        (ModuleCat.of K K) (⋃ b ∈ s, (trivializationAt F E b).baseSet) (by omega) u))).mp hbij
  have hobj (s : Finset B) :
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
          ((thomPairFiniteTrivializingUnionDiagram (F := F) (E := E)).obj s) =
        (thomPairOver F E (⋃ b ∈ s, (trivializationAt F E b).baseSet)).singularHomology
          (ModuleCat.of K K) m := by
    rw [thomPairFiniteTrivializingUnionDiagram_obj, TopPair.singularHomologyFunctor_obj]
  have hpt :
      (TopPair.singularHomologyFunctor (ModuleCat.of K K) m).obj
          (thomPairFiniteTrivializingUnionCocone (F := F) (E := E)).pt =
        (thomPair F E).singularHomology (ModuleCat.of K K) m := by
    rw [thomPairFiniteTrivializingUnionCocone_pt, TopPair.singularHomologyFunctor_obj]
  let P₁ : IsColimit (((singularHomologyFunctor (ModuleCat.{w} K) p).obj
      (ModuleCat.of K K)).mapCocone (baseFiniteTrivializingUnionCocone F E)) :=
    isColimitMapCoconeSingularHomology (ModuleCat.of K K) p
      (baseFiniteTrivializingUnionCocone F E) (fun _ ↦ Topology.IsEmbedding.subtypeVal)
      fun L hL ↦ by
        obtain ⟨s, hs⟩ := hL.elim_finite_subcover _
          (fun b ↦ (trivializationAt F E b).open_baseSet) fun b _ ↦
            mem_iUnion.2 ⟨b, mem_baseSet_trivializationAt F E b⟩
        exact ⟨s, fun b hb ↦ ⟨⟨b, hs hb⟩, rfl⟩⟩
  let P₂ := isColimitMapCoconeSingularHomologyThomPairFiniteTrivializingUnion (F := F) (E := E)
    (ModuleCat.of K K) m
  let α : thomPairFiniteTrivializingUnionDiagram (F := F) (E := E) ⋙
        TopPair.singularHomologyFunctor (ModuleCat.of K K) m ≅
      baseFiniteTrivializingUnionDiagram F E ⋙
        (singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K) :=
    NatIso.ofComponents
      (fun s ↦ eqToIso (hobj s) ≪≫ @asIso _ _ _ _
        (thomPairOverHomologyMap F E (⋃ b ∈ s, (trivializationAt F E b).baseSet) h u) (hiso s))
      fun {s t} f ↦ by
        have := hiso s
        have := hiso t
        dsimp only [Functor.comp_obj, Functor.comp_map, baseFiniteTrivializingUnionDiagram]
        simp only [thomPairFiniteTrivializingUnionDiagram_map,
          TopPair.singularHomologyFunctor_map, Iso.trans_hom, eqToIso.hom, asIso_hom,
          Category.assoc, TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom,
          eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
        exact congrArg (eqToHom (hobj s) ≫ ·)
          (thomPairOverHomologyMap_naturality (biUnion_subset_biUnion_left f.le) h u)
  have hcocone : eqToHom hpt ≫ homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u =
      (P₂.coconePointsIsoOfNatIso P₁ α).hom :=
    P₂.hom_ext fun s ↦ by
      refine (?_ : _ = _).trans (P₂.comp_coconePointsIsoOfNatIso_hom P₁ α s).symm
      dsimp only [Functor.mapCocone_ι_app, α, NatIso.ofComponents_hom_app, Iso.trans_hom,
        eqToIso.hom, asIso_hom, baseFiniteTrivializingUnionCocone]
      simp only [thomPairFiniteTrivializingUnionCocone_ι_app, TopPair.singularHomologyFunctor_map,
        TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_eqToHom, Category.assoc,
        eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      rw [← TopPair.singularHomologyMap_comp_assoc]
      exact congrArg (eqToHom (hobj s) ≫ ·) (thomPairOverHomologyMap_comp_subtypeVal _ h u).symm
  have : IsIso (eqToHom hpt ≫ homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) := by
    rw [hcocone]
    exact (P₂.coconePointsIsoOfNatIso P₁ α).isIso_hom
  exact IsIso.of_isIso_comp_left (eqToHom hpt) _

/-- **The homology Thom isomorphism over a field and an arbitrary base**, bundled as an isomorphism
in `ModuleCat K`: `Hₘ(E, E₀; K) ≅ Hₚ(B; K)` for `finrank ℝ F + p = m`. -/
def IsThomClass.homologyThomIso [VectorBundle ℝ F E] {K : Type w} [Field K]
    {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (thomPair F E).singularHomology (ModuleCat.of K K) m ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  @asIso _ _ _ _ (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u)
    (hu.isIso_homologyThomMap h)

/-- The forward morphism of `TauCeti.IsThomClass.homologyThomIso` is `TauCeti.homologyThomMap`. -/
@[simp]
theorem IsThomClass.homologyThomIso_hom [VectorBundle ℝ F E] {K : Type w} [Field K]
    {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (hu.homologyThomIso h).hom = homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u :=
  -- `homologyThomIso` is `asIso` of `homologyThomMap`.
  (rfl)

/-- **Over any field, the homology Thom map of a Thom class is bijective over an arbitrary
base.** -/
theorem IsThomClass.bijective_homologyThomMap [VectorBundle ℝ F E] {K : Type w} [Field K]
    {p m : ℕ} (h : finrank ℝ F + p = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (hu.homologyThomIso h).toLinearEquiv.bijective

/-- **The cohomology Thom isomorphism over any field and an arbitrary base**: for any Thom class
`u ∈ Hʳ(E, E₀; K)`, `r = finrank ℝ F`, the Thom map `Hᵖ(B; K) ⟶ Hᵐ(E, E₀; K)` (`p + r = m`) is
bijective without any compactness hypothesis on `B`. -/
theorem IsThomClass.bijective_thomMap_of_field [VectorBundle ℝ F E] {K : Type w} [Field K]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    Function.Bijective (thomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u) :=
  (bijective_homologyThomMap_iff F E (by omega : finrank ℝ F + p = m) u).1
    (hu.bijective_homologyThomMap (by omega))

/-- **The cohomology Thom isomorphism over a field and an arbitrary base**, bundled as a `K`-linear
equivalence `Hᵖ(B; K) ≃ₗ[K] Hᵐ(E, E₀; K)` (`p + finrank ℝ F = m`). -/
def IsThomClass.thomEquivOfField [VectorBundle ℝ F E] {K : Type w} [Field K]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) m :=
  LinearEquiv.ofBijective (thomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u)
    (hu.bijective_thomMap_of_field h)

/-- `TauCeti.IsThomClass.thomEquivOfField` evaluates as `TauCeti.thomMap`. -/
@[simp]
theorem IsThomClass.thomEquivOfField_apply [VectorBundle ℝ F E] {K : Type w} [Field K]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) :
    hu.thomEquivOfField h a = thomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u a :=
  -- `thomEquivOfField` is `LinearEquiv.ofBijective` of `thomMap`.
  (rfl)

/-- Left inverse law for `TauCeti.IsThomClass.thomEquivOfField` applied to `TauCeti.thomMap`. -/
@[simp]
theorem IsThomClass.thomEquivOfField_symm_apply_thomMap [VectorBundle ℝ F E] {K : Type w} [Field K]
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) :
    (hu.thomEquivOfField h).symm (thomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u a) = a :=
  (hu.thomEquivOfField h).symm_apply_apply a

end FieldDirectedUnion

section SubsingletonUnits

variable {B : Type w} [TopologicalSpace B] (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]

section CommRing

variable (K : Type w) [CommRing K] [Subsingleton Kˣ]

/-- **The canonical unoriented Thom class** of a finite-rank real vector bundle with coefficients in
a commutative ring `K` whose only unit is `1` (such as `ZMod 2`), chosen from
`TauCeti.existsUnique_isThomClass_of_subsingleton_units`. -/
def thomClassOfSubsingletonUnits :
    (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F) :=
  (existsUnique_isThomClass_of_subsingleton_units (K := K) (F := F) (E := E)).exists.choose

/-- `TauCeti.thomClassOfSubsingletonUnits` is a Thom class of `E`. -/
theorem isThomClass_thomClassOfSubsingletonUnits :
    IsThomClass F E (thomClassOfSubsingletonUnits F E K) :=
  (existsUnique_isThomClass_of_subsingleton_units (K := K) (F := F) (E := E)).exists.choose_spec

variable {F E K} in
/-- Uniqueness of `TauCeti.thomClassOfSubsingletonUnits`: every Thom class of `E` over `K` equals
`thomClassOfSubsingletonUnits F E K`. -/
theorem eq_thomClassOfSubsingletonUnits_of_isThomClass
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    u = thomClassOfSubsingletonUnits F E K :=
  (existsUnique_isThomClass_of_subsingleton_units (K := K) (F := F) (E := E)).unique hu
    (isThomClass_thomClassOfSubsingletonUnits F E K)

end CommRing

section Field

variable (K : Type w) [Field K] [Subsingleton Kˣ]

/-- **The unoriented homology Thom isomorphism** over a field `K` with `Subsingleton Kˣ` (such as
`ZMod 2`) and an arbitrary base `B`, requiring neither an orientation of `E` nor compactness of
`B`: `Hₘ(E, E₀; K) ≅ Hₚ(B; K)` for `finrank ℝ F + p = m`. -/
def homologyThomIsoOfSubsingletonUnits {p m : ℕ} (h : finrank ℝ F + p = m) :
    (thomPair F E).singularHomology (ModuleCat.of K K) m ≅
      ((singularHomologyFunctor (ModuleCat.{w} K) p).obj (ModuleCat.of K K)).obj (TopCat.of B) :=
  (isThomClass_thomClassOfSubsingletonUnits F E K).homologyThomIso h

/-- The forward morphism of `TauCeti.homologyThomIsoOfSubsingletonUnits` is the homology Thom map of
`TauCeti.thomClassOfSubsingletonUnits`. -/
@[simp]
theorem homologyThomIsoOfSubsingletonUnits_hom {p m : ℕ} (h : finrank ℝ F + p = m) :
    (homologyThomIsoOfSubsingletonUnits F E K h).hom =
      homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h
        (thomClassOfSubsingletonUnits F E K) :=
  -- `homologyThomIsoOfSubsingletonUnits` is `IsThomClass.homologyThomIso`.
  (rfl)

/-- **The unoriented cohomology Thom isomorphism** over a field `K` with `Subsingleton Kˣ` (such as
`ZMod 2`) and an arbitrary base `B`, requiring neither an orientation of `E` nor compactness of
`B`: `Hᵖ(B; K) ≃ₗ[K] Hᵐ(E, E₀; K)` for `p + finrank ℝ F = m`. -/
def thomEquivOfSubsingletonUnits {p m : ℕ} (h : p + finrank ℝ F = m) :
    (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p ≃ₗ[K]
      (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) m :=
  (isThomClass_thomClassOfSubsingletonUnits F E K).thomEquivOfField h

/-- `TauCeti.thomEquivOfSubsingletonUnits` evaluates as the Thom map of
`TauCeti.thomClassOfSubsingletonUnits`. -/
@[simp]
theorem thomEquivOfSubsingletonUnits_apply {p m : ℕ} (h : p + finrank ℝ F = m)
    (a : (TopCat.of B).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) p) :
    thomEquivOfSubsingletonUnits F E K h a =
      thomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h
        (thomClassOfSubsingletonUnits F E K) a :=
  -- `thomEquivOfSubsingletonUnits` is `IsThomClass.thomEquivOfField`.
  (rfl)

end Field

end SubsingletonUnits

end TauCeti
