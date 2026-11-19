/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
public import TauCeti.AlgebraicTopology.Cohomology.Point
public import TauCeti.Topology.VectorBundle.MayerVietoris.Basic
public import TauCeti.Topology.VectorBundle.Thom.Class
public import TauCeti.Topology.VectorBundle.Thom.Homology
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism

/-!
# The Thom isomorphism over a finitely trivialized base

Let `E → B` be a real vector bundle with finite-dimensional model fibre `F` of rank `r`, and let
`u ∈ Hʳ(E, E₀; K)` be a Thom class (`TauCeti.IsThomClass`) with coefficients in a commutative ring
`K`, for instance the class of an orientation with `K = ℤ`, or the unique class with `K = ZMod 2`.
This file proves the **Thom isomorphism**: if `B` is covered by finitely many open sets, each in
the base set of a linear trivialization, then the Thom map `a ↦ π^*a ⌣ u` (`TauCeti.thomMap`) is
bijective from `Hᵖ(B; M)` onto `Hᵖ⁺ʳ(E, E₀; M)`, for every degree `p` and every `K`-module `M`
(`TauCeti.IsThomClass.bijective_thomMap_of_biUnion_eq_univ`). A compact base has such a cover
(`TauCeti.IsThomClass.bijective_thomMap`). Over a field, the homology Thom map
`x ↦ π_*(x ⌢ u)` is the transpose of the Thom map up to sign, so it is bijective as well
(`TauCeti.IsThomClass.bijective_homologyThomMap_of_biUnion_eq_univ`, and
`TauCeti.IsThomClass.bijective_homologyThomMap` over a compact base): `Hₚ₊ᵣ(E, E₀; K) ≅ Hₚ(B; K)`.
Composed with the comparison of the disc-sphere pair with the Thom pair, this is the input for
identifying the relative homology of a disc-bundle attachment, such as the attachment of the
negative disc bundle of a critical submanifold of a Morse–Bott function, with the shifted homology
of the base.

The proof is that of Milnor and Stasheff. Over a subset `S` of the base set of a linear
trivialization, the trivialization identifies the Thom pair `(E|_S, E₀|_S)` with that of the
product bundle `S × F` (`Bundle.Trivialization.thomPairOverIso`), and restricted to the fibres it
is a linear isomorphism, so the restriction of `u` still generates the cohomology of every fibre.
The Thom isomorphism for a product bundle (`TauCeti.bijective_pullbackCup_prodThomPair`) then
applies (`TauCeti.IsThomClass.bijective_pullbackCupRestrict_of_subset_baseSet`). Over a union
`U ∪ V` of open sets, the Mayer–Vietoris step
`TopCat.bijective_pullbackCupRestrict_union` deduces bijectivity from bijectivity over `U`, `V` and
`U ∩ V`, together with the vanishing of the cohomology of the Thom pair over `U ∩ V` in degree
`r - 1`. Induction on the number of open sets gives the Thom isomorphism over any finite union of
trivializing open sets (`TauCeti.IsThomClass.bijective_pullbackCupRestrict_biUnion`).

Bases without a finite trivializing cover are not treated here.

## Main results

* `TauCeti.IsThomClass.bijective_pullbackCupRestrict_biUnion`: the Thom isomorphism for the
  restriction of the bundle to a finite union of trivializing open sets.
* `TauCeti.IsThomClass.bijective_thomMap_of_biUnion_eq_univ`: **the Thom isomorphism** over a base
  covered by finitely many trivializing open sets.
* `TauCeti.IsThomClass.bijective_thomMap`: the Thom isomorphism over a compact base.
* `TauCeti.IsThomClass.bijective_homologyThomMap_of_biUnion_eq_univ`: the Thom isomorphism in
  homology over a finitely trivialized base, with coefficients in a field.
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
private theorem bijective_pullbackCupRestrict_biUnion_aux
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
      (fun q _ ↦ by
        have := hu.bijective_pullbackCupRestrict_of_subset_baseSet M e he (p := q) rfl
        rwa [thomPairProj_def] at this)
      (fun q _ ↦ ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
        (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi)) q)
      (fun q _ ↦ by
        have := hu.bijective_pullbackCupRestrict_of_subset_baseSet M e hUV (p := q) rfl
        rwa [thomPairProj_def] at this)
      (fun j hj ↦ ?_) rfl
    -- The pair over `W a ∩ ⋃ i ∈ s, W i` is `thomPairOver`, whose cohomology vanishes below the
    -- rank, since it lies in the base set of `e`.
    exact (isZero_singularCohomology_prodThomPair (ModuleCat.of K K) M _ F (by omega)).of_iso
      ((TopPair.singularCohomologyFunctor (ModuleCat.of K K) K M j).mapIso
        (e.thomPairOverIso ℝ hUV).op).symm

/-- **The Thom isomorphism over a finite union of trivializing open sets.** Let `E → B` be a real
vector bundle of rank `r`, `u ∈ Hʳ(E, E₀; K)` a Thom class and `W` the union of finitely many
open sets, each contained in the base set of a linear trivialization. Then the Thom map of the
restriction of `u` to the Thom pair `(E|_W, E₀|_W)` is bijective from `Hᵖ(W; M)` onto
`Hᵖ⁺ʳ(E|_W, E₀|_W; M)`, for every degree `p` and every `K`-module `M`. -/
theorem IsThomClass.bijective_pullbackCupRestrict_biUnion
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (TopCat.pullbackCupRestrict
      (TopCat.ofHom ⟨π F E, FiberBundle.continuous_proj F E⟩) (zeroSectionCompl F E) M
      (⋃ i ∈ s, W i) (finrank ℝ F) p m h u) := by
  subst h
  exact bijective_pullbackCupRestrict_biUnion_aux M hu s hWo hWe p

/-- **The Thom isomorphism over a finitely trivialized base.** Let `E → B` be a real vector bundle
of rank `r` whose base is covered by finitely many open sets, each contained in the base set of
a linear trivialization, and let `u ∈ Hʳ(E, E₀; K)` be a Thom class. Then the Thom map
`a ↦ π^*a ⌣ u` is bijective from `Hᵖ(B; M)` onto `Hᵖ⁺ʳ(E, E₀; M)`, for every degree `p` and every
`K`-module `M`. -/
theorem IsThomClass.bijective_thomMap_of_biUnion_eq_univ
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : ⋃ i ∈ s, W i = univ) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  have key := hu.bijective_pullbackCupRestrict_biUnion M s hWo hWe h
  rw [hW] at key
  rw [thomMap_def, thomPairProj_def]
  exact (TopCat.bijective_pullbackCupRestrict_univ_iff (proj F E) _ M h u).1 key

/-- **The Thom isomorphism over a compact base.** For a real vector bundle `E → B` of rank `r`
over a compact base and a Thom class `u ∈ Hʳ(E, E₀; K)`, the Thom map `a ↦ π^*a ⌣ u` is bijective
from `Hᵖ(B; M)` onto `Hᵖ⁺ʳ(E, E₀; M)`, for every degree `p` and every `K`-module `M`. -/
theorem IsThomClass.bijective_thomMap [CompactSpace B] [VectorBundle ℝ F E]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : p + finrank ℝ F = m) :
    Function.Bijective (thomMap F E M (finrank ℝ F) p m h u) := by
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun b : B ↦ (trivializationAt F E b).baseSet) (fun b ↦ (trivializationAt F E b).open_baseSet)
    fun b _ ↦ mem_iUnion.2 ⟨b, FiberBundle.mem_baseSet_trivializationAt' b⟩
  exact hu.bijective_thomMap_of_biUnion_eq_univ M t
    (fun b _ ↦ (trivializationAt F E b).open_baseSet)
    (fun b _ ↦ ⟨trivializationAt F E b, inferInstance, subset_rfl⟩) (univ_subset_iff.1 ht) h

/-- **The Thom isomorphism in homology over a finitely trivialized base.** Let `E → B` be a real
vector bundle of rank `r` whose base is covered by finitely many open sets, each contained in
the base set of a linear trivialization, and let `u ∈ Hʳ(E, E₀; K)` be a Thom class with
coefficients in a field `K`. Then the homology Thom map `x ↦ π_*(x ⌢ u)` is bijective from
`Hₚ₊ᵣ(E, E₀; K)` onto `Hₚ(B; K)`, for every degree `p`. -/
theorem IsThomClass.bijective_homologyThomMap_of_biUnion_eq_univ {K : Type w} [Field K]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWo : ∀ i ∈ s, IsOpen (W i))
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    (hW : ⋃ i ∈ s, W i = univ) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (bijective_homologyThomMap_iff F E h u).2
    (hu.bijective_thomMap_of_biUnion_eq_univ _ s hWo hWe hW (by omega))

/-- **The Thom isomorphism in homology over a compact base.** For a real vector bundle `E → B` of
rank `r` over a compact base and a Thom class `u ∈ Hʳ(E, E₀; K)` with coefficients in a field
`K`, the homology Thom map `x ↦ π_*(x ⌢ u)` is bijective from `Hₚ₊ᵣ(E, E₀; K)` onto `Hₚ(B; K)`, for
every degree `p`. With `K = ZMod 2` every real vector bundle has a unique Thom class
(`TauCeti.existsUnique_isThomClass_of_subsingleton_units`), so no orientation is needed. -/
theorem IsThomClass.bijective_homologyThomMap {K : Type w} [Field K] [CompactSpace B]
    [VectorBundle ℝ F E]
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) {p m : ℕ} (h : finrank ℝ F + p = m) :
    Function.Bijective (homologyThomMap F E (ModuleCat.of K K) (finrank ℝ F) p m h u).hom :=
  (bijective_homologyThomMap_iff F E h u).2 (hu.bijective_thomMap _ (by omega))

end TauCeti
