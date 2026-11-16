/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.MayerVietoris.DirectedUnion
public import TauCeti.Topology.VectorBundle.Thom.Isomorphism
import TauCeti.Algebra.Module.Equiv.SpanSingleton
import TauCeti.AlgebraicTopology.Cohomology.MayerVietoris.PullbackCup
import TauCeti.AlgebraicTopology.Cohomology.ProdThomPair.PullbackCup

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

1. **Single trivializing set (`Bundle.Trivialization.bijective_thomMapOver_of_forall_mem`)**: over
   any subset `W ⊆ e.baseSet` of a linear trivialization `e`,
   `Bundle.Trivialization.thomPairOverIso` identifies `(E|_W, E₀|_W)` with
   `TauCeti.prodThomPair W F` compatibly with the bundle projection and fibre inclusions
   (`Bundle.Trivialization.prodThomPairFiberMap_comp_thomPairOverIso_inv`), reducing bijectivity of
   `TauCeti.thomMapOver` to the product-bundle Thom isomorphism
   `TauCeti.bijective_pullbackCup_prodThomPair`.
2. **Finite unions of trivializing sets (`TauCeti.bijective_thomMapOver_biUnion`)**: for open sets
   `W i`, induction on `s : Finset ι` glues bijectivity over `⋃ i ∈ s, W i` via the Mayer–Vietoris
   five-lemma step `TopCat.bijective_pullbackCupRestrict_union` and the below-rank vanishing
   `TauCeti.isZero_singularCohomology_thomPairOver_biUnion` on the intersection
   `W a ∩ ⋃ i ∈ s, W i = ⋃ i ∈ s, (W a ∩ W i)`. For arbitrary sets `W i` contained in linear
   trivializations, pulling `E` back to `Y = ⋃ i ∈ s, W i` via
   `TauCeti.bijective_thomMapOver_iff_pullback` and replacing each pulled-back set by the open base
   set of its pulled-back trivialization reduces to the open-cover case on `Y`.
3. **Global specializations**: when `⋃ i ∈ s, W i = Set.univ`—and hence for any vector bundle over
   a compact space `B` by extracting a finite subcover of `trivializationAt`—`thomMap` is a linear
   equivalence (`TauCeti.IsThomClass.thomEquivOfBiUnionEqUniv`,
   `TauCeti.IsThomClass.thomEquivOfCompactSpace`). Combining this with
   `TauCeti.thomClassOfSubsingletonUnits` gives the canonical unoriented Thom isomorphism over
   rings with `Subsingleton Kˣ` such as `ZMod 2`
   (`TauCeti.thomEquivOfSubsingletonUnitsOfCompactSpace`).

## Main definitions and results

* `Bundle.Trivialization.bijective_thomMapOver_of_forall_mem`,
  `Bundle.Trivialization.bijective_thomMapOver`, `Bundle.Trivialization.thomEquivOver`,
  `Bundle.Trivialization.bijective_thomMap`, `Bundle.Trivialization.thomEquiv`: local and global
  Thom isomorphisms from a single linear trivialization.
* `TauCeti.IsThomClass.thomEquivOver`, `TauCeti.IsThomClass.trivialThomEquiv`: `IsThomClass`
  specializations over a single trivializing set and for `Bundle.Trivial B F`.
* `TauCeti.bijective_thomMapOver_biUnion`, `TauCeti.thomEquivOverBiUnion`,
  `TauCeti.IsThomClass.bijective_thomMapOver_biUnion`,
  `TauCeti.IsThomClass.thomEquivOverBiUnion`: the Thom isomorphism over a finite union of
  trivializing sets under local fibrewise generation or `IsThomClass`.
* `TauCeti.IsThomClass.bijective_thomMap_of_biUnion_eq_univ`,
  `TauCeti.IsThomClass.thomEquivOfBiUnionEqUniv`: the Thom isomorphism for bundles admitting a
  finite trivializing cover.
* `TauCeti.IsThomClass.bijective_thomMap_of_compactSpace`,
  `TauCeti.IsThomClass.thomEquivOfCompactSpace`: the Thom isomorphism over a compact base.
* `TauCeti.thomEquivOfSubsingletonUnitsOfCompactSpace`: the canonical unoriented Thom isomorphism
  over a compact base when `Kˣ` is a subsingleton.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10, Theorem 10.4.
* A. Hatcher, *Algebraic Topology*, Section 4.D, Theorem 4D.10.
* E. H. Spanier, *Algebraic Topology*, McGraw-Hill (1966), Chapter 5, Section 7.
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Module Set

universe w

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
    rw [e.prodThomPairFiberMap_comp_thomPairOverIso_inv_assoc ℝ hW ⟨b, hb⟩]
    exact congrArg _ (fiberThomPairOverMap_comp_restrictPreimagePairMap F E hb)
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

/-- **Local Thom linear equivalence** `Hᵖ(W; M) ≃ₗ[K] Hᵐ(E|_W, E₀|_W; M)` over `W ⊆ e.baseSet` for
a class `u` generating on every fibre over `W`. -/
def thomEquivOver [FiniteDimensional ℝ F] {W : Set B} (hW : W ⊆ e.baseSet) {p m : ℕ}
    (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ W, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    (TopCat.of ↥W).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMapOver F E M W (finrank ℝ F) p m h u)
    (e.bijective_thomMapOver_of_forall_mem M hW h hu)

@[simp]
theorem thomEquivOver_apply [FiniteDimensional ℝ F] {W : Set B} (hW : W ⊆ e.baseSet) {p m : ℕ}
    (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ W, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤)
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

/-- **Local Thom linear equivalence** `Hᵖ(W; M) ≃ₗ[K] Hᵐ(E|_W, E₀|_W; M)` over `W ⊆ e.baseSet`
for a Thom class `u` of `E`. -/
def IsThomClass.thomEquivOver {W : Set B} (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (hW : W ⊆ e.baseSet) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (TopCat.of ↥W).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPairOver F E W).singularCohomology (ModuleCat.of K K) K M m :=
  have := (isThomClass_iff.1 hu).1
  e.thomEquivOver M hW h fun b _ ↦ (isThomClass_iff.1 hu).2 b

@[simp]
theorem IsThomClass.thomEquivOver_apply {W : Set B} (e : Trivialization F (π F E)) [e.IsLinear ℝ]
    (hW : W ⊆ e.baseSet) {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u)
    (a : (TopCat.of ↥W).singularCohomology (ModuleCat.of K K) K M p) :
    hu.thomEquivOver M e hW h a = thomMapOver F E M W (finrank ℝ F) p m h u a :=
  (rfl)

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
    rw [thomMapOver_def]
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
      (fun q _ ↦ by
        rw [← thomMapOver_def]
        exact e.bijective_thomMapOver_of_forall_mem M hWa rfl fun b hb ↦ hu b (Or.inl hb))
      (fun q _ ↦ by
        rw [← thomMapOver_def]
        exact ih (fun i hi ↦ hWo i (Finset.mem_insert_of_mem hi))
          (fun i hi ↦ hWe i (Finset.mem_insert_of_mem hi)) rfl fun b hb ↦ hu b (Or.inr hb))
      (fun q _ ↦ by
        rw [← thomMapOver_def, inter_iUnion₂]
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

/-- **The Thom linear equivalence** `Hᵖ(W; M) ≃ₗ[K] Hᵐ(E|_W, E₀|_W; M)` over a finite union
`W = ⋃ i ∈ s, W i` of trivializing sets, for any class `u` generating on every fibre over `W`. -/
def thomEquivOverBiUnion [FiniteDimensional ℝ F] {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤) :
    (TopCat.of ↥(⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPairOver F E (⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M m :=
  LinearEquiv.ofBijective (thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u)
    (bijective_thomMapOver_biUnion M s hWe h hu)

@[simp]
theorem thomEquivOverBiUnion_apply [FiniteDimensional ℝ F] {ι : Type*} (s : Finset ι)
    {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : ∀ b ∈ ⋃ i ∈ s, W i, Submodule.span K
      {TopPair.singularCohomologyMap (fiberThomPairMap F E b) (finrank ℝ F) u} = ⊤)
    (a : (TopCat.of ↥(⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M p) :
    thomEquivOverBiUnion M s hWe h hu a =
      thomMapOver F E M (⋃ i ∈ s, W i) (finrank ℝ F) p m h u a :=
  (rfl)

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
`W = ⋃ i ∈ s, W i` of trivializing sets for a Thom class `u`. -/
def IsThomClass.thomEquivOverBiUnion {ι : Type*} (s : Finset ι) {W : ι → Set B}
    (hWe : ∀ i ∈ s, ∃ (e : Trivialization F (π F E)) (_ : e.IsLinear ℝ), W i ⊆ e.baseSet)
    {p m : ℕ} (h : p + finrank ℝ F = m)
    {u : (thomPair F E).singularCohomology (ModuleCat.of K K) K (ModuleCat.of K K) (finrank ℝ F)}
    (hu : IsThomClass F E u) :
    (TopCat.of ↥(⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M p ≃ₗ[K]
      (thomPairOver F E (⋃ i ∈ s, W i)).singularCohomology (ModuleCat.of K K) K M m :=
  have := (isThomClass_iff.1 hu).1
  TauCeti.thomEquivOverBiUnion M s hWe h fun b _ ↦ (isThomClass_iff.1 hu).2 b

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

section SubsingletonUnits

variable {B : Type w} [TopologicalSpace B] (F : Type w) [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F] (E : B → Type w) [TopologicalSpace (TotalSpace F E)]
  [∀ b, AddCommMonoid (E b)] [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)]
  [FiberBundle F E] [VectorBundle ℝ F E]
  {K : Type w} [CommRing K] [Subsingleton Kˣ]

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

end TauCeti
