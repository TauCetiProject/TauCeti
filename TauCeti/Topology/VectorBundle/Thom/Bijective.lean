/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.PullbackCup
public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
public import TauCeti.Topology.VectorBundle.Thom.Class
public import TauCeti.Topology.VectorBundle.Thom.Homology

/-!
# The Thom isomorphism over a finitely trivialized base

Let `E → B` be a real vector bundle with finite-dimensional model fibre `F` of rank `r ≥ 2`, and let
`u ∈ Hʳ(E, E₀; K)` be a Thom class (`TauCeti.IsThomClass`) with coefficients in a commutative ring
`K`, for instance the class of an orientation with `K = ℤ`, or the unique class with `K = ZMod 2`.
This file proves the **Thom isomorphism**: if `B` is covered by finitely many open sets, each in
the base set of a linear trivialization, then the Thom map `a ↦ π^*a ⌣ u` (`TauCeti.thomMap`) is
bijective from `Hᵖ(B; M)` onto `Hᵖ⁺ʳ(E, E₀; M)`, for every degree `p` and every `K`-module `M`
(`TauCeti.IsThomClass.bijective_thomMap_of_biUnion_eq_univ`). A compact base has such a cover
(`TauCeti.IsThomClass.bijective_thomMap`). Over a field, the homology Thom map
`x ↦ π_*(x ⌢ u)` is the transpose of the Thom map up to sign, so it is bijective as well
(`TauCeti.IsThomClass.bijective_homologyThomMap`): `Hₚ₊ᵣ(E, E₀; K) ≅ Hₚ(B; K)`. This is the
identification of the relative homology of a disc-bundle attachment, such as the attachment of the
negative disc bundle of a critical submanifold of a Morse–Bott function, with the shifted homology
of the base.

The proof is that of Milnor and Stasheff. Over a subset `S` of the base set of a linear
trivialization, the trivialization identifies the Thom pair `(E|_S, E₀|_S)` with that of the
product bundle `S × F` (`Bundle.Trivialization.thomPairOverIso`), and restricted to the fibres it
is a linear isomorphism, so the restriction of `u` still generates the cohomology of every fibre.
The Thom isomorphism for a product bundle (`TauCeti.bijective_pullbackCup_prodThomPair`) then
applies. Over a union `U ∪ V` of open sets, the Mayer–Vietoris step
`TopCat.bijective_pullbackCupRestrict_union` deduces bijectivity from bijectivity over `U`, `V` and
`U ∩ V`, together with the vanishing of the cohomology of the Thom pair over `U ∩ V` in degree
`r - 1`. Induction on the number of open sets gives the Thom isomorphism over any finite union of
trivializing open sets (`TauCeti.IsThomClass.bijective_pullbackCupRestrict_biUnion`).

The ranks `0` and `1` are not treated here, nor are bases without a finite trivializing cover.

## Main results

* `TauCeti.IsThomClass.bijective_pullbackCupRestrict_biUnion`: the Thom isomorphism for the
  restriction of the bundle to a finite union of trivializing open sets.
* `TauCeti.IsThomClass.bijective_thomMap_of_biUnion_eq_univ`: **the Thom isomorphism** over a base
  covered by finitely many trivializing open sets.
* `TauCeti.IsThomClass.bijective_thomMap`: the Thom isomorphism over a compact base.
* `TauCeti.IsThomClass.bijective_homologyThomMap`: the Thom isomorphism in homology over a compact
  base, with coefficients in a field.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4 and its proof.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10 and its proof.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Module

universe w

namespace TauCeti

variable {B : Type w} [TopologicalSpace B] {F : Type w} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] {E : B → Type w} [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]
  {K : Type w} [CommRing K] (M : ModuleCat.{w} K)

variable (F E) in
/-- The bundle projection as a morphism out of `TopCat.of (TotalSpace F E)`: the projection
`TauCeti.thomPairProj`, with its source written so that the pairs over subsets of the base are the
Thom pairs `TauCeti.thomPairOver F E S`. -/
private abbrev proj : TopCat.of (TotalSpace F E) ⟶ TopCat.of B :=
  TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩

/-- **The Thom isomorphism over a trivializing set**: over a subset `S` of the base set of a linear
trivialization, the Thom map of a Thom class `u` is bijective in every degree, for fibres of rank at
least `2`. -/
private theorem bijective_pullbackCupRestrict_of_subset_baseSet
    (e : Trivialization F (π F E)) [e.IsLinear ℝ] {S : Set B} (hS : S ⊆ e.baseSet)
    (hF : 2 ≤ finrank ℝ F)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (TopCat.pullbackCupRestrict (proj F E) (zeroSectionCompl F E) M S
      (finrank ℝ F) p m h u) := by
  rw [TopCat.pullbackCupRestrict_apply]
  -- The pair over `S` that `TopCat.pullbackCupRestrict` builds from `proj F E` is, by definition,
  -- the Thom pair `thomPairOver F E S`, the target of the trivialization's identification.
  let φ : prodThomPair S F ⟶ thomPairOver F E S := (e.thomPairOverIso ℝ hS).inv
  refine (TopPair.bijective_pullbackCup_iff_of_isIso φ (g := prodThomPairProj S F)
    (𝟙 (TopCat.of S)) ?_ h _).1 ?_
  · refine TopCat.ext fun x ↦ Subtype.ext ?_
    have hx : TopPair.Hom.fst (e.thomPairOverIso ℝ hS).hom (TopPair.Hom.fst φ x) = x :=
      (TopPair.proj₁.mapIso (e.thomPairOverIso ℝ hS)).inv_hom_id_apply x
    have key := (congrArg Subtype.val (prodThomPairProj_apply F x)).trans
      (congrArg (fun q : S × F ↦ (q.1 : B))
        (hx.symm.trans (e.thomPairOverIso_hom_fst_apply ℝ hS (TopPair.Hom.fst φ x))))
    exact key.symm
  · refine bijective_pullbackCup_prodThomPair M hF _ (fun b ↦ ?_) h
    have hb : prodThomPairFiberMap F b ≫ φ ≫ TopCat.restrictPreimagePairMap (proj F E)
        (zeroSectionCompl F E) S =
        (e.continuousLinearEquivAt ℝ b (hS b.2)).complZeroPairIso.inv ≫
          fiberThomPairMap F E b := by
      rw [← fiberThomPairOverMap_comp_restrictPreimagePairMap F E b.2, ← Category.assoc,
        ← Category.assoc]
      congr 1
      rw [Iso.eq_inv_comp, ← Trivialization.fiberThomPairOverMap_comp_thomPairOverIso_hom_assoc]
      simp [φ]
    rw [← TopPair.singularCohomologyMap_comp_apply, ← TopPair.singularCohomologyMap_comp_apply,
      Category.assoc, hb, TopPair.singularCohomologyMap_comp_apply]
    have hspan := Submodule.map_span
      (TopPair.singularCohomologyMap (R := ModuleCat.of K K) (k := K) (M := ModuleCat.of K K)
        (e.continuousLinearEquivAt ℝ b (hS b.2)).complZeroPairIso.inv (finrank ℝ F)).hom
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u}
    rw [Set.image_singleton, (isThomClass_iff.1 hu).2 b, Submodule.map_top] at hspan
    rw [← hspan, LinearMap.range_eq_top]
    exact ((TopPair.singularCohomologyFunctor _ K _ _).mapIso
      (e.continuousLinearEquivAt ℝ b (hS b.2)).complZeroPairIso.symm.op).toLinearEquiv.surjective

omit [NormedSpace ℝ F] [FiniteDimensional ℝ F] [∀ b, Module ℝ (E b)] in
/-- Over the empty set the Thom map is bijective, between zero modules. -/
private theorem bijective_pullbackCupRestrict_empty {n p m : ℕ} (h : p + n = m)
    (u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) n) :
    Function.Bijective (TopCat.pullbackCupRestrict (proj F E) (zeroSectionCompl F E) M ∅
      n p m h u) := by
  have h₁ := ModuleCat.subsingleton_of_isZero
    (isZero_singularCohomology_of_isEmpty (R := ModuleCat.of K K) (k := K) (M := M)
      (TopCat.of (∅ : Set B)) p)
  have h₂ := ModuleCat.subsingleton_of_isZero
    (TopPair.isZero_singularCohomology_of_isZero_singularHomology (k := K) (thomPairOver F E ∅)
      (ModuleCat.of K K) M m fun j _ ↦ isZero_singularHomology_thomPairOver_empty _ j)
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨0, Subsingleton.elim _ _⟩⟩

/-- The Thom isomorphism over a finite union of trivializing open sets, in the degrees `p + r`, by
induction on the number of sets, using the Mayer–Vietoris step
`TopCat.bijective_pullbackCupRestrict_union`. -/
private theorem bijective_pullbackCupRestrict_biUnion_aux (hF : 2 ≤ finrank ℝ F)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (p : ℕ) :
    Function.Bijective (TopCat.pullbackCupRestrict (proj F E) (zeroSectionCompl F E) M
      (⋃ i ∈ s, W i) (finrank ℝ F) p (p + finrank ℝ F) rfl u) := by
  classical
  induction s using Finset.induction_on generalizing W p with
  | empty =>
    rw [show (⋃ i ∈ (∅ : Finset ι), W i) = ∅ by simp]
    exact bijective_pullbackCupRestrict_empty M rfl u
  | insert a s _ ih =>
    rw [Finset.set_biUnion_insert]
    obtain ⟨e, _, he⟩ := hWe a (Finset.mem_insert_self a s)
    have hUV : W a ∩ ⋃ i ∈ s, W i ⊆ e.baseSet := inter_subset_left.trans he
    refine TopCat.bijective_pullbackCupRestrict_union _ _ M (hWo a (Finset.mem_insert_self a s))
      (isOpen_iUnion fun i ↦ isOpen_iUnion fun hi ↦ hWo i (Finset.mem_insert_of_mem hi)) u
      (fun q _ ↦ bijective_pullbackCupRestrict_of_subset_baseSet M e he hF hu _)
      (fun q _ ↦ ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi)) q)
      (fun q _ ↦ bijective_pullbackCupRestrict_of_subset_baseSet M e hUV hF hu _)
      (fun j hj ↦ ?_) rfl
    -- The pair over `W a ∩ ⋃ i ∈ s, W i` is `thomPairOver`, whose cohomology vanishes below the
    -- rank, since it lies in the base set of `e`.
    exact (isZero_singularCohomology_prodThomPair (ModuleCat.of K K) M _ F (by omega)).of_iso
      ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K M j).mapIso
        (e.thomPairOverIso ℝ hUV).op).symm

/-- **The Thom isomorphism over a finite union of trivializing open sets.** Let `E → B` be a real
vector bundle of rank `r ≥ 2`, `u ∈ Hʳ(E, E₀; K)` a Thom class and `W` the union of finitely many
open sets, each contained in the base set of a linear trivialization. Then the Thom map of the
restriction of `u` to the Thom pair `(E|_W, E₀|_W)` is bijective from `Hᵖ(W; M)` onto
`Hᵖ⁺ʳ(E|_W, E₀|_W; M)`, for every degree `p` and every `K`-module `M`. -/
theorem IsThomClass.bijective_pullbackCupRestrict_biUnion (hF : 2 ≤ finrank ℝ F)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (TopCat.pullbackCupRestrict
      (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) M
      (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  subst h
  exact bijective_pullbackCupRestrict_biUnion_aux M hF hu s hWo hWe p

/-- **The Thom isomorphism over a finitely trivialized base.** Let `E → B` be a real vector bundle
of rank `r ≥ 2` whose base is covered by finitely many open sets, each contained in the base set of
a linear trivialization, and let `u ∈ Hʳ(E, E₀; K)` be a Thom class. Then the Thom map
`a ↦ π^*a ⌣ u` is bijective from `Hᵖ(B; M)` onto `Hᵖ⁺ʳ(E, E₀; M)`, for every degree `p` and every
`K`-module `M`. -/
theorem IsThomClass.bijective_thomMap_of_biUnion_eq_univ (hF : 2 ≤ finrank ℝ F)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : ⋃ i ∈ s, W i = univ) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  have key := hu.bijective_pullbackCupRestrict_biUnion M hF s hWo hWe h
  rw [hW] at key
  rw [thomMap_def, thomPairProj_def]
  exact (TopCat.bijective_pullbackCupRestrict_univ_iff (proj F E) _ M h u).1 key

/-- **The Thom isomorphism over a compact base.** For a real vector bundle `E → B` of rank `r ≥ 2`
over a compact base and a Thom class `u ∈ Hʳ(E, E₀; K)`, the Thom map `a ↦ π^*a ⌣ u` is bijective
from `Hᵖ(B; M)` onto `Hᵖ⁺ʳ(E, E₀; M)`, for every degree `p` and every `K`-module `M`. -/
theorem IsThomClass.bijective_thomMap [CompactSpace B] [VectorBundle ℝ F E]
    (hF : 2 ≤ finrank ℝ F)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet) (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, FiberBundle.mem_baseSet_trivializationAt' b⟩
  exact hu.bijective_thomMap_of_biUnion_eq_univ M hF t
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) (univ_subset_iff.1 ht) h

/-- **The Thom isomorphism in homology over a compact base.** For a real vector bundle `E → B` of
rank `r ≥ 2` over a compact base and a Thom class `u ∈ Hʳ(E, E₀; K)` with coefficients in a field
`K`, the homology Thom map `x ↦ π_*(x ⌢ u)` is bijective from `Hₚ₊ᵣ(E, E₀; K)` onto `Hₚ(B; K)`, for
every degree `p`. With `K = ZMod 2` every real vector bundle has a unique Thom class
(`TauCeti.existsUnique_isThomClass_of_subsingleton_units`), so no orientation is needed. -/
theorem IsThomClass.bijective_homologyThomMap {K : Type w} [Field K] [CompactSpace B]
    [VectorBundle ℝ F E] (hF : 2 ≤ finrank ℝ F)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (bijective_homologyThomMap_iff F E h u).2 (hu.bijective_thomMap _ hF (by omega))

end TauCeti
