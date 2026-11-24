/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.CWComplex.Classical.Skeleton.Puncture

/-!
# The skeletal quotient over a top cell and the local homology along a fibre

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta
`Xⁿ = skeletonLT C (n + 1)`. Let `j` be an `n`-cell with centre `b = χⱼ(0)`, and let `F = p⁻¹(b)`.
Since `b` lies off `Xⁿ⁻¹`, the identity of `p⁻¹(Xⁿ)` is a map of pairs

`(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ F)`

(`TauCeti.TopCat.preimageSkeletonPairToComplFiber`), from the pair of consecutive stages of the
skeletal filtration to the pair whose homology is the local homology of `p⁻¹(Xⁿ)` along the fibre
over `b`. This file computes it on relative homology. On the pullback `(Pⱼ', ∂Pⱼ')` of `p` along
the characteristic map of each `n`-cell `j'`:

* the contribution of `j` maps isomorphically with coefficients in any module `M`
  (`isIso_singularHomologyMap_cellDiskPullbackPairMap_comp_preimageSkeletonPairToComplFiber`);
* the contributions of the other `n`-cells map to zero in any abelian category with coproducts
  (`singularHomologyMap_cellDiskPullbackPairMap_comp_preimageSkeletonPairToComplFiber_eq_zero`),
  because their closed cells miss `b`.

When `j` is the only `n`-cell, the pair `(p⁻¹(Xⁿ ∖ {b}), p⁻¹(Xⁿ⁻¹))` is acyclic with coefficients
in any module `M` (`TauCeti.TopCat.isZero_singularHomology_preimage_skeletonDiffCenter`), so the
map `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}))` is an isomorphism in every degree
(`TauCeti.TopCat.isIso_singularHomologyMap_preimageSkeletonPairToComplFiber`). If moreover `B` is
the `n`-skeleton, as for a closed `n`-manifold with a CW structure having a single top cell, this
says that `Hₖ(E, p⁻¹(Xⁿ⁻¹); M) ⟶ Hₖ(E, E ∖ F; M)` is an isomorphism
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

## A single top cell, with any coefficients

When `j` is the only `n`-cell, the acyclicity of `(p⁻¹(Xⁿ ∖ {b}), p⁻¹(Xⁿ⁻¹))` holds for every
module `M` of coefficients (`TauCeti.TopCat.isZero_singularHomology_preimage_skeletonDiffCenter`).
It is filtered by the part of `E` over the neighbourhood `N = TauCeti.skeletonNeighborhood C n` of
`Xⁿ⁻¹`, and both steps are acyclic because a Serre fibration pulls back a pair that deforms into
its subspace relative to that subspace to an acyclic pair
(`TauCeti.TopCat.isZero_singularHomology_preimage_of_homotopyRel`):

* `Xⁿ ∖ {b}` deforms into `N` relative to `N`, by pushing the punctured inner half of the cell
  radially outwards (`TauCeti.skeletonDiffCenterHomotopyRel`; with a single `n`-cell the
  complement of the inner half of `j` is `N`, `TauCeti.skeletonDiffCore_eq_skeletonNeighborhood`);
* `N` deforms onto `Xⁿ⁻¹` relative to `Xⁿ⁻¹` (`TauCeti.skeletonNeighborhoodHomotopyRel`).

The long exact sequence of the triple `(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}), p⁻¹(Xⁿ⁻¹))` then yields
`Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M) ≅ Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}); M)`, and when `B = Xⁿ`, the triple
`(E, E ∖ F, p⁻¹(Xⁿ⁻¹))` yields `Hₖ(E, p⁻¹(Xⁿ⁻¹); M) ≅ Hₖ(E, E ∖ F; M)`.

## Main definitions and results

* `TauCeti.TopCat.preimageSkeletonComplFiberPair`: the pair `(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}))`.
* `TauCeti.TopCat.preimageSkeletonPairToComplFiber`: the map of pairs
  `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}))` for `b ∉ Xⁿ⁻¹`.
* `TauCeti.TopCat.isZero_singularHomology_preimage_skeletonDiffCenter`: with a single `n`-cell,
  the pair `(p⁻¹(Xⁿ ∖ {b}), p⁻¹(Xⁿ⁻¹))` is acyclic with any coefficients.
* `TauCeti.TopCat.isIso_singularHomologyMap_preimageSkeletonPairToComplFiber`: over a single
  `n`-cell, `Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M) ≅ Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}); M)` with any coefficients.
* `TauCeti.TopCat.isIso_singularHomologyMap_preimageSkeletonLTToComplFiber`: over an
  `n`-dimensional complex with a single `n`-cell, `Hₖ(E, p⁻¹(Xⁿ⁻¹); M) ≅ Hₖ(E, E ∖ F; M)`.
* `TauCeti.TopCat.livesOverFundamentalClass_iff_singularHomologyπ_ne_zero`,
  `TauCeti.TopCat.livesOverFundamentalClass_iff_notMem_range`: over an `n`-dimensional complex
  with a single `n`-cell, a class lives over the fundamental class at the centre of the top cell
  exactly when it does not come from the part of `E` over the `(n - 1)`-skeleton.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Definition 2.3, Proposition 2.6 and
  Lemma 2.9.
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

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} {C D : Set B} [RelCWComplex C D]

/-! ### The pair of the local homology along a fibre -/

section Pairs

variable [T2Space B]

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
      fun h ↦ hb (mem_singleton_iff.1 h ▸ x.property)⟩, by fun_prop⟩) rfl

@[simp]
lemma preimageSkeletonPairToComplFiber_fst (n : ℕ) {b : B} (hb : b ∉ (skeletonLT C n : Set B)) :
    TopPair.Hom.fst (preimageSkeletonPairToComplFiber p C n hb) = 𝟙 _ :=
  (rfl)

/-- The identity of `E` sends the part over `skeletonLT C n` off the fibre over the centre of an
`n`-cell: this is the condition for it to be a map of pairs `(E, p⁻¹(Xⁿ⁻¹)) ⟶ (E, E ∖ p⁻¹(b))`. -/
lemma mapsTo_preimage_skeletonLT_compl_fiber (n : ℕ) (j : cell C n) :
    MapsTo (𝟙 E) (p ⁻¹' (skeletonLT C n : Set B)) (p ⁻¹' {map n j 0})ᶜ :=
  fun _ hx h ↦ map_zero_notMem_skeletonLT j (mem_singleton_iff.1 h ▸ hx)

variable (p C) in
/-- The map of pairs `(E, p⁻¹(Xⁿ⁻¹)) ⟶ (E, E ∖ p⁻¹(χⱼ(0)))` given by the identity of `E`, for the
centre `χⱼ(0)` of an `n`-cell `j`. -/
abbrev preimageSkeletonLTToComplFiber (n : ℕ) (j : cell C n) :
    TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B)) ⟶
      TopPair.ofSubset (p ⁻¹' {map n j 0})ᶜ :=
  TopPair.ofSubsetMap (𝟙 E) (mapsTo_preimage_skeletonLT_compl_fiber n j)

end Pairs

/-! ### The pullback along the characteristic map of a cell -/

section CellPullback

variable (n : ℕ) (j : cell C n)

/-- A point of the pullback `Pⱼ` of `p` along the characteristic map of `j` lies over the image of
its point of the disk. -/
private lemma apply_cellDiskPullback (x : (cellDiskPullbackPair p C n j).fst) :
    p x.val.2 = map n j (x.val.1 : ULift.{u} (Fin n → ℝ)).down := by
  rw [← x.property, cellULiftMap_apply]

private lemma norm_down_cellDiskPullback_le_one (x : (cellDiskPullbackPair p C n j).fst) :
    ‖(x.val.1 : ULift.{u} (Fin n → ℝ)).down‖ ≤ 1 := by
  rw [ULift.norm_down]
  exact mem_closedBall_zero_iff.1 x.val.1.property

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

private lemma continuous_cellDiskPullbackFst :
    Continuous fun x : (cellDiskPullbackPair p C n j).fst ↦ (x.val.1 : ULift.{u} (Fin n → ℝ)) :=
  continuous_subtypeVal.comp (_root_.TopCat.pullbackFst (cellULiftMap C n j) p).hom.continuous

private lemma norm_down_cellDiskPullbackBall_lt_one (x : cellDiskPullbackBall p C n j) :
    ‖(x.val.val.1 : ULift.{u} (Fin n → ℝ)).down‖ < 1 := by
  rw [ULift.norm_down]
  exact x.property

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

/-- Over the disk, the part over the boundary sphere and the part off the centre have the same
relative homology. -/
private lemma isIso_singularHomologyMap_cellDiskPullbackPairToComplFiber (hp : serreFibrations p)
    {R : Type*} [Ring R] (M : ModuleCat.{u} R) (k : ℕ) :
    IsIso ((cellDiskPullbackPair p C n j).singularHomologyMap
      (cellDiskPullbackPairToComplFiber p C n j) M k) := by
  rw [cellDiskPullbackPairToComplFiber_eq]
  exact isIso_singularHomologyMap_ofSubsetMap_preimage_sphere M
    (mem_serreFibrations_pullbackFst hp (cellULiftMap C n j)) k

/-- **Excision of the part over the boundary sphere** from `(Pⱼ, Pⱼ ∖ Fⱼ)`. -/
private lemma isIso_singularHomologyMap_cellDiskPullbackBallPairι
    {A : Type*} [Category* A] [HasCoproducts.{u} A] [Abelian A] (M : A) (k : ℕ) :
    IsIso ((cellDiskPullbackBallPair p C n j).singularHomologyMap
      (cellDiskPullbackBallPairι p C n j) M k) := by
  refine TopPair.isIso_singularHomologyMap_of_open_cover M
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

end CellPullback

section Cell

variable [T2Space B] (n : ℕ) (j : cell C n)

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
/-- The projection `(Pⱼ, Pⱼ ∖ Fⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {χⱼ(0)}))`. -/
private def cellDiskPullbackComplFiberPairMap :
    cellDiskPullbackComplFiberPair p C n j ⟶ preimageSkeletonComplFiberPair p C n (map n j 0) :=
  TopPair.ofHom (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.val.2, mem_preimage_skeletonLT_succ n j x⟩,
      by fun_prop⟩)
    (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.val.val.2, mem_preimage_skeletonLT_succ n j x.val,
      fun h ↦ apply_cellDiskPullback_ne n j x.val x.property h⟩, by fun_prop⟩)
    rfl

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

/-- **Excision of the part over `Xⁿ⁻¹`** from `(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {χⱼ(0)}))`, read through the
projection of the part of `Pⱼ` over the open ball. -/
private lemma isIso_singularHomologyMap_cellDiskPullbackBallPairMap
    {A : Type*} [Category* A] [HasCoproducts.{u} A] [Abelian A] (M : A) (k : ℕ) :
    IsIso ((cellDiskPullbackBallPair p C n j).singularHomologyMap
      (cellDiskPullbackBallPairι p C n j ≫ cellDiskPullbackComplFiberPairMap p C n j) M k) := by
  have hpc : Continuous fun x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) ↦ p x.val :=
    p.hom.continuous.comp continuous_subtypeVal
  refine TopPair.isIso_singularHomologyMap_of_open_cover M
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

variable {n}

/-- **The contribution of the cell `j` to the skeletal quotient is the local homology along the
fibre over its centre.** For a Serre fibration `p : E ⟶ B`, a relative CW complex `C ⊆ B` and an
`n`-cell `j`, the projection `(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the pullback of `p` along the
characteristic map of `j`, followed by `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {χⱼ(0)}))`,
induces isomorphisms on relative singular homology in every degree, with coefficients in any
module `M`. -/
theorem isIso_singularHomologyMap_cellDiskPullbackPairMap_comp_preimageSkeletonPairToComplFiber
    (hp : serreFibrations p) {R : Type*} [Ring R] (M : ModuleCat.{u} R) (k : ℕ) :
    IsIso ((cellDiskPullbackPair p C n j).singularHomologyMap
      (cellDiskPullbackPairMap p C n j ≫
        preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j)) M k) := by
  have hsq : cellDiskPullbackPairMap p C n j ≫
        preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j) =
      cellDiskPullbackPairToComplFiber p C n j ≫ cellDiskPullbackComplFiberPairMap p C n j :=
    TopPair.hom_ext_of_fst _ <| by
      ext x
      exact Subtype.ext (coe_cellDiskPullbackPairMap_fst_apply n j x)
  have := isIso_singularHomologyMap_cellDiskPullbackBallPairMap (p := p) n j M k
  rw [TopPair.singularHomologyMap_comp] at this
  have := isIso_singularHomologyMap_cellDiskPullbackBallPairι (p := p) n j M k
  have := IsIso.of_isIso_comp_left
    ((cellDiskPullbackBallPair p C n j).singularHomologyMap (cellDiskPullbackBallPairι p C n j)
      M k)
    ((cellDiskPullbackComplFiberPair p C n j).singularHomologyMap
      (cellDiskPullbackComplFiberPairMap p C n j) M k)
  have := isIso_singularHomologyMap_cellDiskPullbackPairToComplFiber n j hp M k
  rw [hsq, TopPair.singularHomologyMap_comp]
  infer_instance

variable {j} in
/-- **The other cells do not contribute to the local homology along the fibre over the centre of
`j`.** For an `n`-cell `j' ≠ j`, the map `(Pⱼ', ∂Pⱼ') ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {χⱼ(0)}))` is zero on
relative singular homology with coefficients in any abelian category with coproducts: the closed
cell of `j'` misses the open cell of `j`, so it misses the centre of `j`. -/
theorem singularHomologyMap_cellDiskPullbackPairMap_comp_preimageSkeletonPairToComplFiber_eq_zero
    {j' : cell C n} (hj : j' ≠ j)
    {A : Type*} [Category* A] [HasCoproducts.{u} A] [Abelian A] (M : A) (k : ℕ) :
    (cellDiskPullbackPair p C n j').singularHomologyMap
      (cellDiskPullbackPairMap p C n j' ≫
        preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j)) M k = 0 := by
  have hne (x : (cellDiskPullbackPair p C n j').fst) : p x.val.2 ≠ map n j 0 := by
    rw [apply_cellDiskPullback]
    exact (disjoint_closedCell_openCell_of_ne n le_rfl fun h ↦
      hj (eq_of_heq (Sigma.mk.inj_iff.1 h).2)).ne_of_mem
      ⟨_, mem_closedBall_zero_iff.2 (norm_down_cellDiskPullback_le_one n j' x), rfl⟩
      (map_zero_mem_openCell n j)
  refine TopPair.singularHomologyMap_eq_zero_of_fac
    (cellDiskPullbackPairMap p C n j' ≫
      preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j)) M
    (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.val.2, mem_preimage_skeletonLT_succ n j' x,
      fun h ↦ hne x h⟩, by fun_prop⟩) ?_ k
  ext x
  exact Subtype.ext (coe_cellDiskPullbackPairMap_fst_apply n j' x).symm

end Cell

/-! ### A single top cell, with any coefficients -/

section SingleTopCell

variable [T2Space B] {n : ℕ}

/-- Over the `n`-skeleton, the complement of the fibre over the centre of the `n`-cell `j` is the
part over the punctured skeleton. -/
private lemma preimage_skeletonDiffCenter_eq {j : cell C n}
    (hB : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) = univ) :
    p ⁻¹' skeletonDiffCenter j = (p ⁻¹' {map n j 0})ᶜ := by
  ext x
  rw [mem_preimage, mem_skeletonDiffCenter, hB, mem_compl_iff, mem_preimage, mem_singleton_iff]
  exact and_iff_right (mem_univ _)

variable [Subsingleton (cell C n)] (j : cell C n) (hp : serreFibrations p)
  {R : Type*} [Ring R] (M : ModuleCat.{u} R)

include hp

/-- **The part of a Serre fibration over the skeleton punctured at the centre of its only top cell
is acyclic modulo the part over the lower skeleton.** Let `p : E ⟶ B` be a Serre fibration and
`C ⊆ B` a relative CW complex with a single `n`-cell `j`. Then
`Hₘ(p⁻¹(Xⁿ ∖ {χⱼ(0)}), p⁻¹(Xⁿ⁻¹); M) = 0` for every `m` and every module `M`. -/
theorem isZero_singularHomology_preimage_skeletonDiffCenter (m : ℕ) :
    IsZero ((TopPair.ofInclusion (X := E)
      (preimage_mono (f := p) (skeletonLT_subset_skeletonDiffCenter j))).singularHomology M m) := by
  have hNS : skeletonNeighborhood C n ⊆ skeletonDiffCenter j :=
    skeletonDiffCore_eq_skeletonNeighborhood j ▸ skeletonDiffCore_subset_skeletonDiffCenter j
  -- The part over `N` is acyclic modulo the part over `Xⁿ⁻¹`.
  have hinner := isZero_singularHomology_preimage_of_homotopyRel hp
    (skeletonLT_subset_skeletonNeighborhood (C := C) n) (skeletonNeighborhoodHomotopyRel C n)
    (fun x ↦ skeletonNeighborhoodEndpoint_mem _ x.property) M m
  -- The part over `Xⁿ ∖ {b}` is acyclic modulo the part over `N`.
  have houter := (TopPair.isZero_singularHomology_ofInclusion_congr M
    (preimage_mono (f := p) (skeletonDiffCore_subset_skeletonDiffCenter j))
    (preimage_mono (f := p) hNS) rfl
    (by rw [skeletonDiffCore_eq_skeletonNeighborhood j]) m).1
    (isZero_singularHomology_preimage_of_homotopyRel hp
      (skeletonDiffCore_subset_skeletonDiffCenter j) (skeletonDiffCenterHomotopyRel j)
      (skeletonDiffCenterEndpoint_mem j) M m)
  exact TopTriple.isZero_singularHomology_totalPair
    (TopTriple.ofInclusions (X := E)
      (preimage_mono (f := p) (skeletonLT_subset_skeletonNeighborhood (C := C) n))
      (preimage_mono (f := p) hNS)) M m hinner houter

/-- **Over a single `n`-cell, the skeletal quotient is the local homology along the fibre over its
centre.** For a Serre fibration `p : E ⟶ B` and a relative CW complex `C ⊆ B` with a single
`n`-cell `j`, with centre `b = χⱼ(0)`, the identity of `p⁻¹(Xⁿ)` induces isomorphisms
`Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); M) ≅ Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ ∖ {b}); M)` in every degree, with coefficients in
every module `M`. -/
theorem isIso_singularHomologyMap_preimageSkeletonPairToComplFiber (k : ℕ) :
    IsIso ((preimageSkeletonPair p C n).singularHomologyMap
      (preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j)) M k) := by
  have hsdiff : skeletonDiffCenter j =
      (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) \ {map n j 0} :=
    Set.ext fun _ ↦ mem_skeletonDiffCenter j
  have hsub : (skeletonLT C n : Set B) ⊆
      (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) \ {map n j 0} :=
    hsdiff ▸ skeletonLT_subset_skeletonDiffCenter j
  let T := TopTriple.ofInclusions (X := E) (preimage_mono (f := p) hsub)
    (preimage_mono (f := p)
      (sdiff_subset : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) \ {map n j 0} ⊆ _))
  have hz (m : ℕ) := (TopPair.isZero_singularHomology_ofInclusion_congr M
    (preimage_mono (f := p) (skeletonLT_subset_skeletonDiffCenter j))
    (preimage_mono (f := p) hsub) (congrArg (p ⁻¹' ·) hsdiff) rfl m).1
    (isZero_singularHomology_preimage_skeletonDiffCenter j hp M m)
  have h := TopTriple.isIso_singularHomologyMap_totalToOuter_of_isZero T M k (hz k)
    fun m _ ↦ hz m
  have hmap : TopTriple.totalToOuter.app T =
      preimageSkeletonPairToComplFiber p C n (map_zero_notMem_skeletonLT j) :=
    TopPair.hom_ext_of_fst _ rfl
  rwa [hmap] at h

variable {j} (hB : (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) = univ)
include hB

/-- **The skeletal quotient of an `n`-dimensional complex with a single `n`-cell is the local
homology along the fibre over its centre.** For a Serre fibration `p : E ⟶ B` and a relative CW
complex `C ⊆ B` whose `n`-skeleton `Xⁿ = skeletonLT C (n + 1)` is all of `B` and which has a single
`n`-cell `j`, with centre `b = χⱼ(0)`, the identity of `E` induces isomorphisms
`Hₖ(E, p⁻¹(Xⁿ⁻¹); M) ≅ Hₖ(E, E ∖ p⁻¹(b); M)` in every degree, with coefficients in every
module `M`. -/
theorem isIso_singularHomologyMap_preimageSkeletonLTToComplFiber (k : ℕ) :
    IsIso (TopPair.singularHomologyMap (preimageSkeletonLTToComplFiber p C n j) M k) := by
  have hsub : p ⁻¹' (skeletonLT C n : Set B) ⊆ (p ⁻¹' {map n j 0})ᶜ :=
    mapsTo_preimage_skeletonLT_compl_fiber n j
  have hz (m : ℕ) := (TopPair.isZero_singularHomology_ofInclusion_congr M
    (preimage_mono (f := p) (skeletonLT_subset_skeletonDiffCenter j)) hsub
    (preimage_skeletonDiffCenter_eq hB) rfl m).1
    (isZero_singularHomology_preimage_skeletonDiffCenter j hp M m)
  -- The pair `(E ∖ p⁻¹(b), p⁻¹(Xⁿ⁻¹))` is acyclic, so the triple's outer map is an isomorphism.
  have := TopTriple.isIso_singularHomologyMap_totalToOuter_of_isZero
    (TopTriple.ofSubset (X := E) hsub) M k (hz k) fun m _ ↦ hz m
  rw [TopTriple.totalToOuter_app_ofSubset] at this
  exact this

/-- **Living over the fundamental class through the skeletal quotient**: the nonvanishing
criterion corresponding to Lemma 2.9 of Barraud–Damian–Humilière–Oancea, and the equivalence of
conditions (i) and (iii) in their Proposition 2.6. For a Serre fibration `p : E ⟶ B` and a
relative CW complex `C ⊆ B` whose `n`-skeleton is all of `B` and which has a single `n`-cell `j`,
with centre `b = χⱼ(0)`, a class `α ∈ Hₖ(E; M)` lives over the fundamental class at `b` exactly
when its image in `Hₖ(E, p⁻¹(Xⁿ⁻¹); M)` is nonzero. -/
theorem livesOverFundamentalClass_iff_singularHomologyπ_ne_zero {k : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology M k : ModuleCat.{u} R)) :
    LivesOverFundamentalClass M p (map n j 0) α ↔
      ((TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B))).singularHomologyπ M k).hom α ≠
        0 := by
  have := isIso_singularHomologyMap_preimageSkeletonLTToComplFiber (j := j) hp M hB k
  -- The localization at the fibre factors through the skeletal quotient.
  have h' : (TopPair.singularHomologyMap (preimageSkeletonLTToComplFiber p C n j) M k).hom
        (((TopPair.ofSubset (p ⁻¹' (skeletonLT C n : Set B))).singularHomologyπ M k).hom α) =
      (fiberLocalization M p (map n j 0) k).hom α :=
    congrArg (fun g ↦ g.hom α) (TopPair.singularHomologyπ_comp_singularHomologyMap_ofSubsetMap_id M
      (mapsTo_preimage_skeletonLT_compl_fiber (p := p) n j) k)
  rw [livesOverFundamentalClass_iff, ← h', not_iff_not]
  exact ((ModuleCat.mono_iff_injective _).1 inferInstance).eq_iff' (map_zero _)

/-- **Living over the fundamental class and the skeletal filtration**: the skeletal-filtration form
of Proposition 2.6 of Barraud–Damian–Humilière–Oancea. For a Serre fibration `p : E ⟶ B` and a
relative CW complex `C ⊆ B` whose `n`-skeleton is all of `B` and which has a single `n`-cell `j`,
with centre `b = χⱼ(0)`, a class `α ∈ Hₖ(E; M)` lives over the fundamental class at `b` exactly
when it does not come from the homology of the part of `E` over the `(n - 1)`-skeleton. -/
theorem livesOverFundamentalClass_iff_notMem_range {k : ℕ}
    (α : ((_root_.TopCat.toSSet.obj E).homology M k : ModuleCat.{u} R)) :
    LivesOverFundamentalClass M p (map n j 0) α ↔
      α ∉ LinearMap.range (SSet.homologyMap (_root_.TopCat.toSSet.map
        (TopPair.ofSubset (X := E) (p ⁻¹' (skeletonLT C n : Set B))).map) M k).hom := by
  -- By exactness of the sequence of the pair, the image is the kernel of the map to the
  -- skeletal quotient.
  rw [livesOverFundamentalClass_iff_singularHomologyπ_ne_zero (j := j) hp M hB, not_iff_not,
    ((TopPair.ofSubset (p ⁻¹' (skeletonLT C n : Set B))).singularHomology_exact_space
      M k).moduleCat_range_eq_ker]
  exact LinearMap.mem_ker.symm

end SingleTopCell

end TopCat

end TauCeti
