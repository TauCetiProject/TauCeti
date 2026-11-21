/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver

/-!
# The skeletal quotient over a top cell and the local homology along a fibre

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta
`Xⁿ = skeletonLT C (n + 1)`. Let `j` be an `n`-cell with centre `b = χⱼ(0)`, and let `F = p⁻¹(b)`.
Since `b` lies off `Xⁿ⁻¹`, the identity of `p⁻¹(Xⁿ)` is a map of pairs

`(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ F)`

(`TauCeti.TopCat.preimageSkeletonPairToComplFiber`), from the pair of consecutive stages of the
skeletal filtration to the pair whose homology is the local homology of `p⁻¹(Xⁿ)` along the fibre
over `b`. This file computes it on relative homology. The source is the direct sum of the
contributions `Hₖ(Pⱼ', ∂Pⱼ')` of the `n`-cells `j'`, where `Pⱼ'` is the pullback of `p` along the
characteristic map of `j'` (`TauCeti.TopCat.isColimitCofanSingularHomologyPreimageSkeletonPair`).

* The contribution of `j` maps isomorphically
  (`isIso_singularHomologyMap_cellDiskPullbackPairMap_comp_preimageSkeletonPairToComplFiber`).
* The contributions of the other `n`-cells map to zero
  (`singularHomologyMap_cellDiskPullbackPairMap_comp_preimageSkeletonPairToComplFiber_eq_zero`),
  because their closed cells miss `b`.

So when `j` is the only `n`-cell, the map is an isomorphism in every degree
(`TauCeti.TopCat.isIso_singularHomologyMap_preimageSkeletonPairToComplFiber`). If moreover `B` is
the `n`-skeleton, as for a closed `n`-manifold with a CW structure having a single top cell, this
says that `Hₖ(E, p⁻¹(Xⁿ⁻¹)) ⟶ Hₖ(E, E ∖ F)` is an isomorphism
(`TauCeti.TopCat.isIso_singularHomologyMap_preimageSkeletonLTToComplFiber`). Barraud, Damian,
Humilière and Oancea read the shriek map of the inclusion of `b` as the composite
`Hₖ(E) ⟶ Hₖ(E, p⁻¹(Xⁿ⁻¹)) ≅ Hₖ₋ₙ(F)` for such a CW structure (their Lemma 2.9), while
`TauCeti.LivesOverFundamentalClass` uses the localization `Hₖ(E) ⟶ Hₖ(E, E ∖ F)` at the fibre. The
isomorphism shows that the two detect the same classes: a class of `Hₖ(E)` lives over the
fundamental class at `b` exactly when its image in `Hₖ(E, p⁻¹(Xⁿ⁻¹))` is nonzero
(`TauCeti.TopCat.livesOverFundamentalClass_iff_singularHomologyπ_ne_zero`), that is, exactly when
it does not come from the part of `E` over the `(n - 1)`-skeleton
(`TauCeti.TopCat.livesOverFundamentalClass_iff_notMem_range`). In the Serre spectral sequence of
the skeletal filtration, this is the condition that the class is not in the filtration step
`Fₙ₋₁ Hₖ(E)`, so that it is detected on the column `E^∞_{n,*}` (their Proposition 2.6).

## The computation over the cell `j`

The map from `(Pⱼ, ∂Pⱼ)` factors through the pullback `Pⱼ` relative to its part off the fibre over
the centre of the disk. Over the disk, the part over the boundary sphere and the part off the
centre have the same relative homology, since the punctured disk deforms radially onto the sphere
(`TauCeti.TopCat.isIso_singularHomologyMap_ofSubsetMap_preimage_sphere`). The remaining map is an
isomorphism by excision: excise the part over the boundary sphere on the left and the part over
`Xⁿ⁻¹` on the right. What remains on both sides is the part over the open ball, respectively over
the open cell, relative to the part off the fibre over the centre, and the characteristic map is a
homeomorphism of the open ball onto the open cell (`TauCeti.openCellHomeomorph`), which is open in
`Xⁿ` (`TauCeti.isOpen_preimage_val_openCell`).

## Main definitions and results

* `TauCeti.TopCat.preimageSkeletonComplFiberPair`: the pair `(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}))`.
* `TauCeti.TopCat.preimageSkeletonPairToComplFiber`: the map of pairs
  `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}))` for `b ∉ Xⁿ⁻¹`.
* `TauCeti.TopCat.isIso_singularHomologyMap_preimageSkeletonPairToComplFiber`: over a single
  `n`-cell it is an isomorphism on relative homology.
* `TauCeti.TopCat.livesOverFundamentalClass_iff_singularHomologyπ_ne_zero`,
  `TauCeti.TopCat.livesOverFundamentalClass_iff_notMem_range`: over an `n`-dimensional complex
  with a single `n`-cell, a class lives over the fundamental class at the centre of the top cell
  exactly when it does not come from the part of `E` over the `(n - 1)`-skeleton.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Proposition 2.6 and Lemma 2.9.
* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex
open Homeomorph (uliftClosedBall coe_uliftClosedBall_apply coe_uliftClosedBall_symm_apply)

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]

/-! ### The pair of the local homology along a fibre -/

variable (p C) in
/-- The pair `(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}))`: the part of `E` over the `n`-skeleton
`Xⁿ = skeletonLT C (n + 1)`, relative to its part off the fibre over `b`. When `b` lies in an open
`n`-cell, its homology is the local homology of `p⁻¹(Xⁿ)` along the fibre over `b`. -/
abbrev preimageSkeletonComplFiberPair (n : ℕ) (b : B) : TopPair.{u} :=
  TopPair.ofInclusion (X := E) (preimage_mono (f := p)
    (sdiff_subset : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) \ {b} ⊆ _))

variable (p C) in
/-- The map of pairs `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}))` given by the identity of
`p⁻¹(Xⁿ)`, for a point `b` off the `(n - 1)`-skeleton. -/
def preimageSkeletonPairToComplFiber (n : ℕ) {b : B} (hb : b ∉ (skeletonLT C n : Set B)) :
    preimageSkeletonPair p C n ⟶ preimageSkeletonComplFiberPair p C n b :=
  TopPair.ofHom (𝟙 _) (_root_.TopCat.ofHom
    ⟨fun x ↦ ⟨x.val, skeletonLT_subset_skeletonLT_succ C n x.property,
      fun h ↦ hb (by rw [← mem_singleton_iff.1 h]; exact x.property)⟩, by fun_prop⟩) rfl

@[simp]
lemma preimageSkeletonPairToComplFiber_fst (n : ℕ) {b : B} (hb : b ∉ (skeletonLT C n : Set B)) :
    TopPair.Hom.fst (preimageSkeletonPairToComplFiber p C n hb) = 𝟙 _ :=
  (rfl)

/-- The identity of `E` sends the part over `skeletonLT C n` off the fibre over the centre of an
`n`-cell: this is the condition for it to be a map of pairs `(E, p⁻¹(Xⁿ⁻¹)) ⟶ (E, E ∖ p⁻¹(b))`. -/
lemma mapsTo_preimage_skeletonLT_compl_fiber (n : ℕ) (j : cell C n) :
    MapsTo (𝟙 E) (p ⁻¹' (skeletonLT C n : Set B)) (p ⁻¹' {map n j 0})ᶜ := fun _ hx ↦
  mem_compl fun h ↦ map_zero_notMem_skeletonLT j (by rw [← mem_singleton_iff.1 h]; exact hx)

variable (p C) in
/-- The map of pairs `(E, p⁻¹(Xⁿ⁻¹)) ⟶ (E, E ∖ p⁻¹(χⱼ(0)))` given by the identity of `E`, for the
centre `χⱼ(0)` of an `n`-cell `j`. -/
abbrev preimageSkeletonLTToComplFiber (n : ℕ) (j : cell C n) :
    TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B)) ⟶
      TopPair.ofSubset (p ⁻¹' {map n j 0})ᶜ :=
  TopPair.ofSubsetMap (𝟙 E) (mapsTo_preimage_skeletonLT_compl_fiber n j)

/-! ### The pullback along the characteristic map of a cell -/

section Cell

variable (n : ℕ) (j : cell C n)

omit [T2Space B] in
/-- A point of the pullback `Pⱼ` of `p` along the characteristic map of `j` lies over the image of
its point of the disk. -/
private lemma apply_cellDiskPullback (x : (cellDiskPullbackPair p C n j).fst) :
    p x.val.2 = map n j (x.val.1 : ULift.{u} (Fin n → ℝ)).down := by
  rw [← x.property, cellULiftMap_apply]

omit [T2Space B] in
private lemma norm_down_cellDiskPullback_le_one (x : (cellDiskPullbackPair p C n j).fst) :
    ‖(x.val.1 : ULift.{u} (Fin n → ℝ)).down‖ ≤ 1 := by
  rw [ULift.norm_down]
  exact mem_closedBall_zero_iff.1 x.val.1.property

private lemma mem_preimage_skeletonLT_succ (x : (cellDiskPullbackPair p C n j).fst) :
    x.val.2 ∈ p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) := by
  rw [mem_preimage, apply_cellDiskPullback]
  exact map_mem_skeletonLT_succ j (norm_down_cellDiskPullback_le_one n j x)

/-- A point of `Pⱼ` off the fibre over the centre of the disk lies off the fibre of `p` over the
centre of the cell. -/
private lemma apply_cellDiskPullback_ne (x : (cellDiskPullbackPair p C n j).fst)
    (hx : (x.val.1 : ULift.{u} (Fin n → ℝ)) ≠ 0) : p x.val.2 ≠ map n j 0 := by
  rw [apply_cellDiskPullback, Ne, map_eq_map_zero_iff j (norm_down_cellDiskPullback_le_one n j x)]
  exact fun h ↦ hx (ULift.ext h)

variable (p C) in
/-- The pullback `Pⱼ` relative to its part off the fibre over the centre of the disk. -/
private abbrev cellDiskPullbackComplFiberPair : TopPair.{u} :=
  TopPair.ofSubset
    (_root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹' {x | (x : ULift.{u} (Fin n → ℝ)) ≠ 0})

variable (p C) in
/-- The inclusion `(Pⱼ, ∂Pⱼ) ⟶ (Pⱼ, Pⱼ ∖ Fⱼ)`. -/
private def cellDiskPullbackPairToComplFiber :
    cellDiskPullbackPair p C n j ⟶ cellDiskPullbackComplFiberPair p C n j :=
  TopPair.ofHom (𝟙 _)
    (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.val, ne_of_mem_sphere x.property one_ne_zero⟩, by fun_prop⟩)
    rfl

omit [T2Space B] in
private lemma cellDiskPullbackPairToComplFiber_eq :
    cellDiskPullbackPairToComplFiber p C n j =
      TopPair.ofSubsetMap
        (B := _root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹'
          {x | (x : ULift.{u} (Fin n → ℝ)) ∈ sphere 0 1})
        (B' := _root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹'
          {x | (x : ULift.{u} (Fin n → ℝ)) ≠ 0})
        (𝟙 _) fun _ hx ↦ ne_of_mem_sphere hx one_ne_zero :=
  TopPair.hom_ext_of_fst _ (TopPair.ofSubsetMap_fst _ _).symm

variable (p C) in
/-- The projection `(Pⱼ, Pⱼ ∖ Fⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {χⱼ(0)}))`. -/
private def cellDiskPullbackComplFiberPairMap :
    cellDiskPullbackComplFiberPair p C n j ⟶ preimageSkeletonComplFiberPair p C n (map n j 0) :=
  TopPair.ofHom (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.val.2, mem_preimage_skeletonLT_succ n j x⟩,
      by fun_prop⟩)
    (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.val.val.2, mem_preimage_skeletonLT_succ n j x.val,
      fun h ↦ apply_cellDiskPullback_ne n j x.val x.property h⟩, by fun_prop⟩)
    rfl

variable (p C) in
/-- The part of `Pⱼ` over the open ball. -/
private abbrev cellDiskPullbackBall :=
  _root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹' {x | ‖(x : ULift.{u} (Fin n → ℝ))‖ < 1}

variable (p C) in
/-- The part of `Pⱼ` over the open ball, relative to its part off the fibre over the centre. -/
private abbrev cellDiskPullbackBallPair : TopPair.{u} :=
  TopPair.ofSubset (X := _root_.TopCat.of (cellDiskPullbackBall p C n j))
    (Subtype.val ⁻¹' (_root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹'
      {x | (x : ULift.{u} (Fin n → ℝ)) ≠ 0}))

variable (p C) in
/-- The inclusion of the part of `Pⱼ` over the open ball, as a map of pairs. -/
private def cellDiskPullbackBallPairι :
    cellDiskPullbackBallPair p C n j ⟶ cellDiskPullbackComplFiberPair p C n j :=
  TopPair.ofHom (_root_.TopCat.ofHom ⟨Subtype.val, continuous_subtypeVal⟩)
    (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.val.val, x.property⟩, by fun_prop⟩) rfl

omit [T2Space B] in
private lemma continuous_cellDiskPullbackFst :
    Continuous fun x : (cellDiskPullbackPair p C n j).fst ↦ (x.val.1 : ULift.{u} (Fin n → ℝ)) :=
  continuous_subtypeVal.comp (_root_.TopCat.pullbackFst (cellULiftMap C n j) p).hom.continuous

omit [T2Space B] in
private lemma norm_down_cellDiskPullbackBall_lt_one (x : cellDiskPullbackBall p C n j) :
    ‖(x.val.val.1 : ULift.{u} (Fin n → ℝ)).down‖ < 1 := by
  rw [ULift.norm_down]
  exact x.property

omit [T2Space B] in
/-- A point of `Pⱼ` over the open ball lies over the open cell. -/
private lemma mem_preimage_openCell (x : cellDiskPullbackBall p C n j) :
    x.val.val.2 ∈ p ⁻¹' openCell n j := by
  rw [mem_preimage, apply_cellDiskPullback n j x.val]
  exact ⟨_, mem_ball_zero_iff.2 (norm_down_cellDiskPullbackBall_lt_one n j x), rfl⟩

/-- The point of `Pⱼ` over the open ball lying over a point of `E` over the open cell. -/
private def cellDiskPullbackBallInv (e : (p ⁻¹' openCell n j : Set E)) :
    cellDiskPullbackBall p C n j :=
  ⟨⟨((uliftClosedBall (0 : ULift.{u} (Fin n → ℝ)) 1).symm
      ⟨(openCellHomeomorph n j).symm ⟨p e, e.property⟩,
        mem_closedBall_zero_iff.2
          (mem_ball_zero_iff.1
            ((openCellHomeomorph n j).symm ⟨p e, e.property⟩).property).le⟩, e.val), by
    rw [cellULiftMap_apply, coe_uliftClosedBall_symm_apply]
    exact (openCellHomeomorph_apply n j _).symm.trans
      (congrArg Subtype.val ((openCellHomeomorph n j).apply_symm_apply ⟨p e, e.property⟩))⟩,
    by
    -- Membership in `cellDiskPullbackBall` is membership of the `pullbackFst` image in the open
    -- ball, which holds by definition; `rw [mem_preimage, pullbackFst_apply]` fails here because
    -- the pullback point also occurs in its proof component, so state the unfolded goal directly.
    change ‖((uliftClosedBall (0 : ULift.{u} (Fin n → ℝ)) 1).symm _ : ULift.{u} (Fin n → ℝ))‖ < 1
    rw [coe_uliftClosedBall_symm_apply, ULift.norm_up]
    exact mem_ball_zero_iff.1 ((openCellHomeomorph n j).symm ⟨p e, e.property⟩).property⟩

omit [T2Space B] in
private lemma continuous_cellDiskPullbackBallInv :
    Continuous (cellDiskPullbackBallInv (p := p) n j) := by
  have hs : Continuous fun e : (p ⁻¹' openCell n j : Set E) ↦
      (openCellHomeomorph n j).symm ⟨p e, e.property⟩ :=
    (openCellHomeomorph n j).symm.continuous.comp
      ((p.hom.continuous.comp continuous_subtypeVal).subtype_mk _)
  refine Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk ?_
    continuous_subtypeVal) _) _
  exact (uliftClosedBall (0 : ULift.{u} (Fin n → ℝ)) 1).symm.continuous.comp
    ((continuous_inclusion ball_subset_closedBall).comp hs)

omit [T2Space B] in
private lemma cellDiskPullbackBallInv_apply (x : cellDiskPullbackBall p C n j) :
    cellDiskPullbackBallInv n j ⟨x.val.val.2, mem_preimage_openCell n j x⟩ = x := by
  have hy := norm_down_cellDiskPullbackBall_lt_one n j x
  -- The inverse of the characteristic map recovers the point of the disk.
  have hs : (openCellHomeomorph n j).symm ⟨p x.val.val.2, mem_preimage_openCell n j x⟩ =
      ⟨_, mem_ball_zero_iff.2 hy⟩ := by
    rw [Homeomorph.symm_apply_eq]
    exact Subtype.ext ((apply_cellDiskPullback n j x.val).trans
      (openCellHomeomorph_apply n j ⟨_, mem_ball_zero_iff.2 hy⟩).symm)
  refine Subtype.ext (Subtype.ext (Prod.ext ?_ rfl))
  simp only [cellDiskPullbackBallInv, hs]
  rw [Homeomorph.symm_apply_eq]
  exact Subtype.ext (coe_uliftClosedBall_apply _ _ _).symm

/-- On the part over the open ball, the projection `Pⱼ ⟶ p⁻¹(Xⁿ)` is an embedding: it is a
homeomorphism onto the part of `E` over the open cell. -/
private lemma isEmbedding_cellDiskPullbackBallPairMap :
    IsEmbedding (TopPair.Hom.fst
      (cellDiskPullbackBallPairι p C n j ≫ cellDiskPullbackComplFiberPairMap p C n j)) := by
  have hsub : (p ⁻¹' openCell n j : Set E) ⊆ p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) :=
    preimage_mono (openCell_subset_skeletonLT n j)
  have hg : IsEmbedding fun x : cellDiskPullbackBall p C n j ↦
      (⟨x.val.val.2, mem_preimage_openCell n j x⟩ : (p ⁻¹' openCell n j : Set E)) :=
    Function.LeftInverse.isEmbedding (cellDiskPullbackBallInv_apply n j)
      (continuous_cellDiskPullbackBallInv n j)
      ((continuous_snd.comp (continuous_subtypeVal.comp continuous_subtypeVal)).subtype_mk _)
  exact (IsEmbedding.inclusion hsub).comp hg

variable (hp : serreFibrations p) (R : Type u) [Ring R]

include hp in
omit [T2Space B] in
/-- Over the disk, the part over the boundary sphere and the part off the centre have the same
relative homology. -/
private lemma isIso_singularHomologyMap_cellDiskPullbackPairToComplFiber (k : ℕ) :
    IsIso ((cellDiskPullbackPair p C n j).singularHomologyMap
      (cellDiskPullbackPairToComplFiber p C n j) (ModuleCat.of R R) k) := by
  rw [cellDiskPullbackPairToComplFiber_eq]
  exact isIso_singularHomologyMap_ofSubsetMap_preimage_sphere R
    (mem_serreFibrations_pullbackFst hp (cellULiftMap C n j)) k

omit [T2Space B] in
/-- **Excision of the part over the boundary sphere** from `(Pⱼ, Pⱼ ∖ Fⱼ)`. -/
private lemma isIso_singularHomologyMap_cellDiskPullbackBallPairι (k : ℕ) :
    IsIso ((cellDiskPullbackBallPair p C n j).singularHomologyMap
      (cellDiskPullbackBallPairι p C n j) (ModuleCat.of R R) k) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover (ModuleCat.of R R)
    (cellDiskPullbackBallPairι p C n j) IsEmbedding.subtypeVal ?_
    (fun b : Bool ↦ bif b then cellDiskPullbackBall p C n j
      else _root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹'
        {x | (x : ULift.{u} (Fin n → ℝ)) ≠ 0})
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · intro x hx
    rw [TopPair.range_ofSubset_map] at hx ⊢
    exact hx
  · cases b
    · exact isOpen_ne_fun (continuous_cellDiskPullbackFst n j) continuous_const
    · exact isOpen_lt (continuous_norm.comp (continuous_cellDiskPullbackFst n j)) continuous_const
  · refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    by_cases hx : (x.val.1 : ULift.{u} (Fin n → ℝ)) = 0
    · exact ⟨true, (by simp [hx] : ‖(x.val.1 : ULift.{u} (Fin n → ℝ))‖ < 1)⟩
    · exact ⟨false, hx⟩
  · cases b
    · exact Or.inl fun x hx ↦ by rw [TopPair.range_ofSubset_map]; exact hx
    · exact Or.inr fun x hx ↦ ⟨⟨x, hx⟩, rfl⟩

/-- **Excision of the part over `Xⁿ⁻¹`** from `(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {χⱼ(0)}))`, read through the
projection of the part of `Pⱼ` over the open ball. -/
private lemma isIso_singularHomologyMap_cellDiskPullbackBallPairMap (k : ℕ) :
    IsIso ((cellDiskPullbackBallPair p C n j).singularHomologyMap
      (cellDiskPullbackBallPairι p C n j ≫ cellDiskPullbackComplFiberPairMap p C n j)
      (ModuleCat.of R R) k) := by
  have hpc : Continuous fun x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) ↦ p x.val :=
    p.hom.continuous.comp continuous_subtypeVal
  refine TopPair.isIso_singularHomologyMap_of_open_cover (ModuleCat.of R R)
    (cellDiskPullbackBallPairι p C n j ≫ cellDiskPullbackComplFiberPairMap p C n j)
    (isEmbedding_cellDiskPullbackBallPairMap n j) ?_
    (fun b : Bool ↦ bif b
      then {x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) | p x.val ∈ openCell n j}
      else {x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) | p x.val ≠ map n j 0})
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · -- A point of the open ball whose image lies off the fibre over `χⱼ(0)` lies off the centre.
    rintro x ⟨a, ha⟩
    rw [TopPair.range_ofSubset_map]
    intro hx
    apply a.property.2
    have hax : (a.val : E) = x.val.val.2 := congrArg Subtype.val ha
    rw [mem_singleton_iff, hax, apply_cellDiskPullback n j x.val]
    exact congrArg (map n j) (congrArg ULift.down hx)
  · cases b
    · exact isOpen_ne_fun hpc continuous_const
    · exact (isOpen_preimage_val_openCell n subset_rfl j).preimage
        (hpc.subtype_mk fun x ↦ x.property)
  · refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    by_cases hx : p x.val = map n j 0
    · exact ⟨true, (hx ▸ map_zero_mem_openCell n j : p x.val ∈ openCell n j)⟩
    · exact ⟨false, hx⟩
  · cases b
    · exact Or.inl fun x hx ↦ ⟨⟨x.val, x.property, hx⟩, rfl⟩
    · exact Or.inr fun x hx ↦ ⟨cellDiskPullbackBallInv n j ⟨x.val, hx⟩, Subtype.ext rfl⟩

include hp in
variable (C) in
/-- **The contribution of the cell `j` to the skeletal quotient is the local homology along the
fibre over its centre.** For a Serre fibration `p : E ⟶ B`, a relative CW complex `C ⊆ B` and an
`n`-cell `j`, the projection `(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the pullback of `p` along the
characteristic map of `j`, followed by `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {χⱼ(0)}))`,
induces isomorphisms on relative singular homology in every degree. -/
theorem isIso_singularHomologyMap_cellDiskPullbackPairMap_comp_preimageSkeletonPairToComplFiber
    (k : ℕ) :
    IsIso ((cellDiskPullbackPair p C n j).singularHomologyMap
      (cellDiskPullbackPairMap p C n j ≫
        preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j))
      (ModuleCat.of R R) k) := by
  have hsq : cellDiskPullbackPairMap p C n j ≫
        preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j) =
      cellDiskPullbackPairToComplFiber p C n j ≫ cellDiskPullbackComplFiberPairMap p C n j :=
    TopPair.hom_ext_of_fst _ <| by
      ext x
      exact Subtype.ext (coe_cellDiskPullbackPairMap_fst_apply n j x)
  have := isIso_singularHomologyMap_cellDiskPullbackBallPairMap (p := p) n j R k
  rw [TopPair.singularHomologyMap_comp] at this
  have := isIso_singularHomologyMap_cellDiskPullbackBallPairι (p := p) n j R k
  have := IsIso.of_isIso_comp_left
    ((cellDiskPullbackBallPair p C n j).singularHomologyMap (cellDiskPullbackBallPairι p C n j)
      (ModuleCat.of R R) k)
    ((cellDiskPullbackComplFiberPair p C n j).singularHomologyMap
      (cellDiskPullbackComplFiberPairMap p C n j) (ModuleCat.of R R) k)
  have := isIso_singularHomologyMap_cellDiskPullbackPairToComplFiber n j hp R k
  rw [hsq, TopPair.singularHomologyMap_comp]
  infer_instance

variable {n} in
/-- **The other cells do not contribute to the local homology along the fibre over the centre of
`j`.** For an `n`-cell `j' ≠ j`, the map `(Pⱼ', ∂Pⱼ') ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {χⱼ(0)}))` is zero on
relative singular homology: the closed cell of `j'` misses the open cell of `j`, so it misses the
centre of `j`. -/
theorem singularHomologyMap_cellDiskPullbackPairMap_comp_preimageSkeletonPairToComplFiber_eq_zero
    {j' : cell C n} (hj : j' ≠ j) (k : ℕ) :
    (cellDiskPullbackPair p C n j').singularHomologyMap
      (cellDiskPullbackPairMap p C n j' ≫
        preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j))
      (ModuleCat.of R R) k = 0 := by
  have hne (x : (cellDiskPullbackPair p C n j').fst) : p x.val.2 ≠ map n j 0 := by
    rw [apply_cellDiskPullback]
    exact (disjoint_closedCell_openCell_of_ne n le_rfl fun h ↦
      hj (eq_of_heq (Sigma.mk.inj_iff.1 h).2)).ne_of_mem
      ⟨_, mem_closedBall_zero_iff.2 (norm_down_cellDiskPullback_le_one n j' x), rfl⟩
      (map_zero_mem_openCell n j)
  refine TopPair.singularHomologyMap_eq_zero_of_fac
    (cellDiskPullbackPairMap p C n j' ≫
      preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j)) (ModuleCat.of R R)
    (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.val.2, mem_preimage_skeletonLT_succ n j' x,
      fun h ↦ hne x h⟩, by fun_prop⟩) ?_ k
  ext x
  exact Subtype.ext (coe_cellDiskPullbackPairMap_fst_apply n j' x).symm

end Cell

/-! ### A single top cell -/

section Single

variable (hp : serreFibrations p) (R : Type u) [Ring R]
include hp

variable (C) in
/-- **Over a single `n`-cell, the skeletal quotient is the local homology along the fibre over its
centre.** For a Serre fibration `p : E ⟶ B` and a relative CW complex `C ⊆ B` with a single
`n`-cell, with centre `b`, the identity of `p⁻¹(Xⁿ)` induces isomorphisms
`Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ≅ Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}); R)` in every degree. -/
theorem isIso_singularHomologyMap_preimageSkeletonPairToComplFiber (n : ℕ) [Unique (cell C n)]
    (k : ℕ) :
    IsIso ((preimageSkeletonPair p C n).singularHomologyMap
      (preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT (default : cell C n)))
      (ModuleCat.of R R) k) := by
  have hc := isColimitCofanSingularHomologyPreimageSkeletonPair C hp R n k
  -- The relative homology of the skeletal pair is the coproduct of a single summand.
  have : IsIso ((cellDiskPullbackPair p C n default).singularHomologyMap
      (cellDiskPullbackPairMap p C n default) (ModuleCat.of R R) k) :=
    isIso_of_comp_hom_eq_id (hc.coconePointUniqueUpToIso (colimitCoconeOfUnique _).isColimit).hom
      (hc.comp_coconePointUniqueUpToIso_hom _ ⟨default⟩)
  have := isIso_singularHomologyMap_cellDiskPullbackPairMap_comp_preimageSkeletonPairToComplFiber
    C n default hp R k
  rw [TopPair.singularHomologyMap_comp] at this
  exact IsIso.of_isIso_comp_left ((cellDiskPullbackPair p C n default).singularHomologyMap
    (cellDiskPullbackPairMap p C n default) (ModuleCat.of R R) k) _

variable {n : ℕ} [Unique (cell C n)]
  (hC : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) = univ)
include hC

/-- **The skeletal quotient of an `n`-dimensional complex with a single `n`-cell is the local
homology along the fibre over its centre.** For a Serre fibration `p : E ⟶ B` and a relative CW
complex `C ⊆ B` whose `n`-skeleton is all of `B` and which has a single `n`-cell, with centre
`b`, the identity of `E` induces isomorphisms `Hₖ(E, p⁻¹(Xⁿ⁻¹); R) ≅ Hₖ(E, E ∖ p⁻¹(b); R)` in every
degree. -/
theorem isIso_singularHomologyMap_preimageSkeletonLTToComplFiber (k : ℕ) :
    IsIso (TopPair.singularHomologyMap
      (preimageSkeletonLTToComplFiber p C n (default : cell C n))
      (ModuleCat.of R R) k) := by
  have ht (x : E) : x ∈ p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) := by
    rw [mem_preimage, hC]
    exact mem_univ _
  let i₁ := TopPair.ofInclusionIsoOfSubset
    (preimage_mono (f := p) (skeletonLT_subset_skeletonLT_succ C n)) ht
    (s₀ := p ⁻¹' (skeletonLT C n : Set B)) fun _ ↦ Iff.rfl
  let i₂ := TopPair.ofInclusionIsoOfSubset
    (preimage_mono (f := p) (sdiff_subset : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) \
      {map n (default : cell C n) 0} ⊆ _)) ht
    (s₀ := (p ⁻¹' {map n (default : cell C n) 0})ᶜ) fun x ↦ ⟨fun h ↦ h.2, fun h ↦ ⟨ht x, h⟩⟩
  -- Over `Xⁿ = B`, both pairs are the corresponding pairs of `E`.
  have hsq : preimageSkeletonPairToComplFiber p C n
        (map_zero_notMem_skeletonLT (default : cell C n)) ≫ i₂.hom =
      i₁.hom ≫ preimageSkeletonLTToComplFiber p C n (default : cell C n) :=
    TopPair.hom_ext_of_fst _ <| by
      rw [TopPair.Hom.fst_comp, TopPair.Hom.fst_comp, TopPair.ofSubsetMap_fst]
      ext x
      exact (TopPair.ofInclusionIsoOfSubset_hom_fst_apply ht _ _).trans
        (TopPair.ofInclusionIsoOfSubset_hom_fst_apply ht _ x).symm
  have := isIso_singularHomologyMap_preimageSkeletonPairToComplFiber C hp R n k
  have h := congrArg (fun f ↦ TopPair.singularHomologyMap f (ModuleCat.of R R) k) hsq
  simp only [TopPair.singularHomologyMap_comp] at h
  have : IsIso (TopPair.singularHomologyMap i₁.hom (ModuleCat.of R R) k ≫
      TopPair.singularHomologyMap (preimageSkeletonLTToComplFiber p C n (default : cell C n))
        (ModuleCat.of R R) k) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_left (TopPair.singularHomologyMap i₁.hom (ModuleCat.of R R) k) _

/-- **Living over the fundamental class through the skeletal quotient**: the untwisted nonvanishing
criterion corresponding to Lemma 2.9 of Barraud–Damian–Humilière–Oancea. For a Serre fibration
`p : E ⟶ B` and a relative CW complex `C ⊆ B` whose `n`-skeleton is all of `B` and which has a
single `n`-cell, with centre `b`, a class `α ∈ Hₖ(E; R)` lives over the fundamental class at `b`
exactly when its image in `Hₖ(E, p⁻¹(Xⁿ⁻¹); R)` is nonzero. -/
theorem livesOverFundamentalClass_iff_singularHomologyπ_ne_zero {k : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) k : ModuleCat.{u} R)) :
    LivesOverFundamentalClass (ModuleCat.of R R) p (map n (default : cell C n) 0) α ↔
      ((TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B))).singularHomologyπ
        (ModuleCat.of R R) k).hom α ≠ 0 := by
  have := isIso_singularHomologyMap_preimageSkeletonLTToComplFiber hp R hC k
  -- The localization at the fibre factors through the skeletal quotient.
  have key := congrArg (fun f ↦ f.hom α)
    (TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id (ModuleCat.of R R)
      (mapsTo_preimage_skeletonLT_compl_fiber (p := p) n (default : cell C n)) k)
  simp only [ModuleCat.hom_comp] at key
  have hinj := LinearMap.ker_eq_bot.1 (ModuleCat.ker_eq_bot_of_mono (TopPair.singularHomologyMap
    (preimageSkeletonLTToComplFiber p C n (default : cell C n)) (ModuleCat.of R R) k))
  exact (livesOverFundamentalClass_iff _ _ _ _).trans ((congrArg (· ≠ 0) key).symm.to_iff.trans
    (map_eq_zero_iff _ hinj).not)

/-- **Living over the fundamental class and the skeletal filtration**: the skeletal-filtration form
of Proposition 2.6 of Barraud–Damian–Humilière–Oancea. For a Serre fibration `p : E ⟶ B` and a
relative CW complex `C ⊆ B` whose `n`-skeleton is all of `B` and which has a single `n`-cell, with
centre `b`, a class `α ∈ Hₖ(E; R)` lives over the fundamental class at `b` exactly when it does not
come from the homology of the part of `E` over the `(n - 1)`-skeleton. -/
theorem livesOverFundamentalClass_iff_notMem_range {k : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology (ModuleCat.of R R) k : ModuleCat.{u} R)) :
    LivesOverFundamentalClass (ModuleCat.of R R) p (map n (default : cell C n) 0) α ↔
      α ∉ LinearMap.range (SSet.homologyMap (_root_.TopCat.toSSet.map
        (TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B))).map)
          (ModuleCat.of R R) k).hom := by
  -- By exactness of the sequence of the pair, the image is the kernel of the map to the
  -- skeletal quotient.
  have hex : LinearMap.range (SSet.homologyMap (_root_.TopCat.toSSet.map
        (TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B))).map)
          (ModuleCat.of R R) k).hom =
      LinearMap.ker ((TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B))).singularHomologyπ
        (ModuleCat.of R R) k).hom :=
    ((TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B))).singularHomology_exact_space
      (ModuleCat.of R R) k).moduleCat_range_eq_ker
  have hmem : α ∈ LinearMap.range (SSet.homologyMap (_root_.TopCat.toSSet.map
        (TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B))).map)
          (ModuleCat.of R R) k).hom ↔
      ((TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B))).singularHomologyπ
        (ModuleCat.of R R) k).hom α = 0 := by
    rw [hex]
    exact LinearMap.mem_ker (f := ((TopPair.ofSubset (X := E)
      (p ⁻¹' (skeletonLT C n : Set B))).singularHomologyπ (ModuleCat.of R R) k).hom)
  exact (livesOverFundamentalClass_iff_singularHomologyπ_ne_zero hp R hC α).trans hmem.not.symm

end Single

end TopCat

end TauCeti
