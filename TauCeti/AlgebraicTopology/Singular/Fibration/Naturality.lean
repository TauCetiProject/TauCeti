/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Comparison
public import TauCeti.AlgebraicTopology.Singular.Fibration.FirstPage
public import TauCeti.AlgebraicTopology.Singular.Homotopy.FiberHomotopyEquiv

/-!
# Naturality of the Serre spectral sequence in maps of fibrations

Let `p : E ⟶ B` and `p' : E' ⟶ B'` be maps to spaces carrying relative CW complexes `C ⊆ B` and
`C' ⊆ B'`, and let `f : E ⟶ E'` lie over a map `g : B ⟶ B'`, that is `f ≫ p' = p ≫ g`. If `g` is
cellular, carrying each skeleton of `C` into the skeleton of `C'` of the same dimension, then `f`
carries the preimages of the skeleta of `C` into those of `C'`
(`TauCeti.mapsTo_preimageSkeleton_of_mapsTo_skeletonLT`), and so induces a morphism of Serre
spectral sequences (`TauCeti.TopCat.serreSpectralSequenceMap`). It is by definition the morphism
of spectral sequences of filtered spaces `TauCeti.filteredSpaceSpectralSequenceMap`, so it is
functorial
(`TauCeti.filteredSpaceSpectralSequenceMap_id`, `TauCeti.filteredSpaceSpectralSequenceMap_comp`)
and compatible with morphisms of coefficients
(`TauCeti.filteredSpaceSpectralSequenceMap_comp_filteredSpaceSpectralSequenceCoefficientMap`).

A map `f` over the identity of `B`, that is `f ≫ p' = p`, induces the morphism
`TauCeti.TopCat.serreSpectralSequenceMapOver`. Between Serre fibrations, its first page is described
cell by cell. Through the identifications `E¹_{k,q} ≅ ⨁ⱼ Hq(p⁻¹(χⱼ(0)); R)` of
`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma`, the morphism acts on the summand of the
`k`-cell `j` by the map induced on `Hq` by the restriction `p⁻¹(χⱼ(0)) ⟶ p'⁻¹(χⱼ(0))` of `f` to the
fibres over the centre of the cell
(`TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma_hom_naturality`).

* **Comparison theorem.** If `f` induces isomorphisms on the homology of the fibres over the points
  of `C`, then the morphism of Serre spectral sequences is an isomorphism on every object of every
  page from the first on (`TauCeti.TopCat.isIso_serreSpectralSequenceMapOver_hom_f`).
* **Fibre homotopy equivalences.** A fibre homotopy equivalence over `B`, between any maps to `B`,
  induces an isomorphism of their Serre spectral sequences from the first page on
  (`TauCeti.FiberHomotopyEquiv.isIso_serreSpectralSequenceMapOver_hom_f`), since it is a homology
  isomorphism on each step of the filtrations. This is how the fibration theorem of DG Morse
  homology passes from a Hurewicz fibration to its Moore-path replacement.

## Main definitions

* `TauCeti.TopCat.serreSpectralSequenceMap`: the morphism of Serre spectral sequences induced by a
  map of fibrations over a cellular map of the bases.
* `TauCeti.TopCat.serreSpectralSequenceMapOver`: its special case for a map of fibrations over
  the identity of `B`.

## Main results

* `TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma_hom_naturality`: on the first page, the
  morphism induced by a map over `B` is the sum of the maps of the fibres over the centres of the
  cells.
* `TauCeti.TopCat.isIso_serreSpectralSequenceMapOver_hom_f`: a map of Serre fibrations over `B`
  that is a homology isomorphism on the fibres induces an isomorphism of Serre spectral sequences
  from the first page on.
* `TauCeti.FiberHomotopyEquiv.isIso_serreSpectralSequenceMapOver_hom_f`: so does a fibre homotopy
  equivalence over `B`, with no fibration hypothesis.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  425–505, Chapter II.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Cambridge University Press, 2001,
  Section 5.1 and Theorem 3.5 (the comparison theorem).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 7 (the fibration theorem).
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

section Map

variable {E B E' B' : _root_.TopCat.{u}} [T2Space B] [T2Space B'] {C D : Set B}
  [RelCWComplex C D] {C' D' : Set B'} [RelCWComplex C' D'] {p : E ⟶ B} {p' : E' ⟶ B'}
  {f : E ⟶ E'} {g : B ⟶ B'}

variable (C C') in
/-- **The morphism of Serre spectral sequences induced by a map of fibrations.** A map `f : E ⟶ E'`
over a map `g : B ⟶ B'` that carries each skeleton of `C` into the skeleton of `C'` of the same
dimension induces a morphism from the Serre spectral sequence of `p` over `C` to that of `p'` over
`C'`: the morphism of spectral sequences of the filtrations of `E` and `E'` by the preimages of the
skeleta (`TauCeti.filteredSpaceSpectralSequenceMap`). No fibration hypothesis is needed to define
it. -/
abbrev serreSpectralSequenceMap (R : Type u) [Ring R] (hfg : f ≫ p' = p ≫ g)
    (hg : ∀ n : ℕ, MapsTo g (skeletonLT C n) (skeletonLT C' n)) :
    serreSpectralSequence C p R ⟶ serreSpectralSequence C' p' R :=
  filteredSpaceSpectralSequenceMap (ModuleCat.of R R) (monotone_preimageSkeleton p)
    (monotone_preimageSkeleton p') f
    (mapsTo_preimageSkeleton_of_mapsTo_skeletonLT
      (by rw [← TopCat.coe_comp, hfg, TopCat.coe_comp]) hg)

end Map

section MapOver

variable {E B E' : _root_.TopCat.{u}} [T2Space B] {C D : Set B} [RelCWComplex C D] {p : E ⟶ B}
  {p' : E' ⟶ B} {f : E ⟶ E'}

variable (C) in
/-- **The morphism of Serre spectral sequences induced by a map over `B`.** A map `f : E ⟶ E'`
with `f ≫ p' = p` induces a morphism from the Serre spectral sequence of `p` over `C` to that of
`p'`: the morphism `TauCeti.TopCat.serreSpectralSequenceMap` over the identity of `B`. -/
abbrev serreSpectralSequenceMapOver (R : Type u) [Ring R] (hf : f ≫ p' = p) :
    serreSpectralSequence C p R ⟶ serreSpectralSequence C p' R :=
  serreSpectralSequenceMap C C R (g := 𝟙 B) (hf.trans (Category.comp_id p).symm)
    fun _ ↦ by rw [TopCat.coe_id]; exact mapsTo_id _

/-- On the stage `b = k - 1 ≤ b + 1` of the skeletal filtrations, the map of pairs induced by a map
`f` over `B` is the map `(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹)) ⟶ (p'⁻¹(Xᵏ), p'⁻¹(Xᵏ⁻¹))` of preimages of
consecutive skeleta, through the identifications of the two pairs. -/
@[reassoc]
private lemma singularHomologyMap_preimagePairMap_comp_eqToHom (hf : f ≫ p' = p)
    (R : Type u) [Ring R] (k : ℕ) (b : ℤ) (hb : b = k - 1) (n : ℕ) :
    TopPair.singularHomologyMap
        (TopCat.Hom.preimagePairMap f hf (skeletonLT_subset_skeletonLT_succ C k))
        (ModuleCat.of R R) n ≫
        eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) n)
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair (p := p') k b hb)).symm =
      eqToHom (congrArg (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) n)
          (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair (p := p) k b hb)).symm ≫
        TopPair.singularHomologyMap (filteredSpaceStepMap (monotone_preimageSkeleton (C := C) p)
          (monotone_preimageSkeleton (C := C) p') f
          (mapsTo_preimageSkeleton f fun x ↦ ConcreteCategory.congr_hom hf x)
          (Int.le_add_one le_rfl)) (ModuleCat.of R R) n :=
  TopPair.singularHomologyMap_comp_eqToHom_of_eq _
    (preimageSkeleton_eq_preimage_skeletonLT p k b hb).symm
    (preimageSkeleton_add_one_eq_preimage_skeletonLT p k b hb).symm
    (preimageSkeleton_eq_preimage_skeletonLT p' k b hb).symm
    (preimageSkeleton_add_one_eq_preimage_skeletonLT p' k b hb).symm _ _
    (fun x ↦ by
      rw [TopCat.Hom.preimagePairMap_fst]
      exact (TopCat.Hom.coe_preimageMap_apply f hf _ x).trans
        (filteredSpaceStepMap_fst_apply _ _ f _ _ ⟨x.val, _⟩).symm) n

end MapOver

section OverBase

variable {E B E' : _root_.TopCat.{u}} [T2Space B] {C D : Set B} [RelCWComplex C D] {p : E ⟶ B}
  {p' : E' ⟶ B} {f : E ⟶ E'} (hp : serreFibrations p) (hp' : serreFibrations p')
  (R : Type u) [Ring R]

include hp hp' in
/-- **The first page of the morphism of Serre spectral sequences induced by a map over `B`.** For
a map `f` over `B` between Serre fibrations `p` and `p'`, the identifications
`E¹_{k,q} ≅ ⨁ⱼ Hq(p⁻¹(χⱼ(0)); R)` of `TauCeti.TopCat.serreSpectralSequenceFirstPageXIsoSigma`
intertwine the morphism of Serre spectral sequences with the sum, over the `k`-cells `j`, of the
maps induced on `Hq` by the restrictions `p⁻¹(χⱼ(0)) ⟶ p'⁻¹(χⱼ(0))` of `f` to the fibres over the
centres of the cells. -/
@[reassoc]
theorem serreSpectralSequenceFirstPageXIsoSigma_hom_naturality (hf : f ≫ p' = p) (k q : ℕ)
    (pq : ℤ × ℤ) (hb : pq.2 = k - 1) (ha : pq.1 + pq.2 = -(q + k : ℕ)) :
    ((serreSpectralSequenceMapOver C R hf).hom 2 le_rfl).f pq ≫
        (serreSpectralSequenceFirstPageXIsoSigma C hp' R k q pq hb ha).hom =
      (serreSpectralSequenceFirstPageXIsoSigma C hp R k q pq hb ha).hom ≫
        Limits.Sigma.map fun j ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R)
          q).obj (ModuleCat.of R R)).map (f.preimageMap hf {map k j 0}) := by
  -- Move the morphism past the first-page identification of the filtered spaces, then read the
  -- map of the step `pq.2 ≤ pq.2 + 1` as the map of the pairs of preimages of skeleta.
  rw [serreSpectralSequenceFirstPageXIsoSigma_hom, serreSpectralSequenceFirstPageXIsoSigma_hom,
    filteredSpaceSpectralSequenceFirstPageXIso_hom_naturality_assoc, Category.assoc]
  congr 1
  rw [← cancel_epi (eqToHom (congrArg
      (fun P : TopPair.{u} ↦ P.singularHomology (ModuleCat.of R R) (q + k))
      (ofInclusion_preimageSkeleton_eq_preimageSkeletonPair (p := p) k pq.2 hb)).symm),
    ← singularHomologyMap_preimagePairMap_comp_eqToHom_assoc hf R k pq.2 hb,
    eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Category.assoc, eqToHom_trans_assoc,
    eqToHom_refl, Category.id_comp]
  -- What remains is the naturality of the splitting of the pair into the cells.
  exact preimageSkeletonPairSingularHomologyIsoSigma_hom_naturality hp R hp' hf k q
    (fun j ↦ f.preimageMap hf {map k j 0}) (fun j x ↦ f.coe_preimageMap_apply hf _ x)

include hp hp' in
/-- **The comparison theorem for maps of Serre fibrations.** Let `f` be a map over `B` between
Serre fibrations `p` and `p'`, and let `C ⊆ B` be a relative CW complex. If for every point `b` of
`C` the restriction `p⁻¹(b) ⟶ p'⁻¹(b)` of `f` induces isomorphisms on the singular homology
`Hq(-; R)` of the fibres in every degree `q`, then the morphism of Serre spectral sequences induced
by `f` is an isomorphism on every object of every page `r ≥ 2`, that is, from the first page on. -/
theorem isIso_serreSpectralSequenceMapOver_hom_f (hf : f ≫ p' = p)
    (hfib : ∀ b ∈ C, ∀ q : ℕ, IsIso (((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).map (f.preimageMap hf {b})))
    (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    IsIso (((serreSpectralSequenceMapOver C R hf).hom r hr).f pq) := by
  suffices IsIso (serreSpectralSequenceMapOver C R hf) from inferInstance
  refine isIso_filteredSpaceSpectralSequenceMap _ _ _ _ _ fun b n ↦ ?_
  rcases lt_or_ge b (-1) with hb | hb
  · -- Below the base both stages are the preimage of `D`, so both pairs have no homology.
    have hz {E₀ : _root_.TopCat.{u}} (p₀ : E₀ ⟶ B) :
        IsZero ((TopPair.ofInclusion (monotone_preimageSkeleton (C := C) p₀
          (Int.le_add_one le_rfl : b ≤ b + 1))).singularHomology (ModuleCat.of R R) n) :=
      (TopPair.isZero_singularHomology_ofInclusion_congr _ _ (subset_refl (p₀ ⁻¹' D))
        (preimageSkeleton_of_neg p₀ (by lia)) (preimageSkeleton_of_neg p₀ (by lia)) n).2
        (TopPair.isZero_singularHomology_ofInclusion_self _ _ n)
    exact (hz p).isIso (hz p') _
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, b = k - 1 := ⟨(b + 1).toNat, by lia⟩
  -- On the preimages of consecutive skeleta the map is an isomorphism, since the fibre over the
  -- centre of each cell is a fibre over a point of `C`.
  have hpair := isIso_singularHomologyMap_preimagePairMap hp hp' R hf k n fun j q _ ↦
    hfib _ (closedCell_subset_complex k j ⟨0, Metric.mem_closedBall_self zero_le_one, rfl⟩) q
  have e := singularHomologyMap_preimagePairMap_comp_eqToHom (C := C) hf R k _ rfl n
  rw [(IsIso.eq_inv_comp _).2 e.symm]
  infer_instance

/-- **A fibre homotopy equivalence induces an isomorphism of Serre spectral sequences.** For a
fibre homotopy equivalence `Φ` over `B` between `p` and `p'`, the morphism of Serre spectral
sequences induced by its forward map is an isomorphism on every object of every page `r ≥ 2`. No
fibration hypothesis is needed: on each step `(p⁻¹(Xᵏ), p⁻¹(Xᵏ⁻¹))` of the filtration, the
restriction of `Φ` over `Xᵏ` is a fibre homotopy equivalence, hence a homology isomorphism relative
to the preimages of `Xᵏ⁻¹`. -/
theorem _root_.TauCeti.FiberHomotopyEquiv.isIso_serreSpectralSequenceMapOver_hom_f
    (Φ : FiberHomotopyEquiv p.hom p'.hom) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) :
    IsIso (((serreSpectralSequenceMapOver C R (f := _root_.TopCat.ofHom Φ.toFun)
      (_root_.TopCat.hom_ext Φ.comp_toFun)).hom r hr).f pq) := by
  suffices IsIso (serreSpectralSequenceMapOver C R (f := _root_.TopCat.ofHom Φ.toFun)
      (_root_.TopCat.hom_ext Φ.comp_toFun)) from inferInstance
  refine isIso_filteredSpaceSpectralSequenceMap _ _ _ _ _ fun b n ↦ ?_
  -- The step `b ≤ b + 1` is the pair of preimages of the skeleta `S₀ ⊆ S₁`, and over `S₁` it is
  -- the map of pairs of the restriction of `Φ`, relative to the preimages of `S₀`.
  let S₀ : Set B := skeletonLT C ((b + 1).toNat : ℕ∞)
  let S₁ : Set B := skeletonLT C ((b + 1 + 1).toNat : ℕ∞)
  have hS : S₀ ⊆ S₁ := skeletonLT_mono (by norm_cast; lia)
  -- The preimage of `S₀` under the restriction `p⁻¹(S₁) ⟶ S₁` of `p` is by definition the preimage
  -- of `p⁻¹(S₀)` in `p⁻¹(S₁)`, the form taken by `TopPair.ofSubsetPreimageValIso`.
  let φ : TopPair.ofSubset (X := _root_.TopCat.of (p ⁻¹' S₁)) (Subtype.val ⁻¹' (p ⁻¹' S₀)) ⟶
      TopPair.ofSubset (X := _root_.TopCat.of (p' ⁻¹' S₁)) (Subtype.val ⁻¹' (p' ⁻¹' S₀)) :=
    (Φ.restrictPreimage S₁).preimagePairMap (Subtype.val ⁻¹' S₀)
  have hφ : IsIso (TopPair.singularHomologyMap φ (ModuleCat.of R R) n) :=
    (Φ.restrictPreimage S₁).isIso_singularHomologyMap_preimagePairMap (Subtype.val ⁻¹' S₀)
      (ModuleCat.of R R) n
  refine (TopPair.isIso_singularHomologyMap_ofInclusion_congr (ModuleCat.of R R) Φ.toFun
    (preimageSkeleton_def p b) (preimageSkeleton_def p (b + 1)) (preimageSkeleton_def p' b)
    (preimageSkeleton_def p' (b + 1)) _
    ((TopPair.ofSubsetPreimageValIso (preimage_mono hS)).inv ≫ φ ≫
      (TopPair.ofSubsetPreimageValIso (preimage_mono hS)).hom)
    (filteredSpaceStepMap_fst_apply _ _ _ _ _) (fun x ↦ ?_) n).2 ?_
  · -- The identifications of the pairs are the identity on the ambient spaces.
    have h : TopPair.Hom.fst ((TopPair.ofSubsetPreimageValIso (preimage_mono hS)).inv ≫ φ ≫
        (TopPair.ofSubsetPreimageValIso (preimage_mono hS)).hom) = TopPair.Hom.fst φ := by
      rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopPair.ofSubsetPreimageValIso_inv_fst,
        TopPair.ofSubsetPreimageValIso_hom_fst]
      -- The identities are those of `p⁻¹(S₁)` and `p'⁻¹(S₁)`, the ambient spaces of both pairs.
      exact (Category.id_comp _).trans (Category.comp_id _)
    refine (congrArg Subtype.val (ConcreteCategory.congr_hom h x)).trans ?_
    rw [FiberHomotopyEquiv.preimagePairMap_fst]
    exact Φ.coe_restrictPreimage_toFun_apply S₁ x
  rw [TopPair.singularHomologyMap_comp, TopPair.singularHomologyMap_comp]
  infer_instance

end OverBase

end TopCat

end TauCeti
