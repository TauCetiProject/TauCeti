/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Excision
public import TauCeti.AlgebraicTopology.Singular.Fibration.CellFiber
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.LivesOver
public import TauCeti.Topology.CWComplex.Classical.OpenCells

/-!
# Localizing the skeletal filtration of a Serre fibration at the fibre over a cell

Let `p : E ⟶ B` be a Serre fibration, `C ⊆ B` a relative CW complex with skeleta
`Xⁿ = skeletonLT C (n + 1)`, and `j` an `n`-cell with centre `bⱼ = χⱼ(0)` and fibre
`Fⱼ = p⁻¹(bⱼ)`. The centre does not lie in `Xⁿ⁻¹`, so the identity of `p⁻¹(Xⁿ)` is a map of pairs

`(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)`

(`TauCeti.TopCat.preimageSkeletonPairToComplFiber`). On relative homology its source is the
direct sum `⨁ᵢ Hq(Fᵢ)` over the `n`-cells
(`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma`), and its target is the homology
of `p⁻¹(Xⁿ)` localized at the fibre `Fⱼ`. This file shows that the map is the projection onto
the summand of `j`:

* on the summand of a cell `i ≠ j` it vanishes, because the closed cell of `i` misses the open
  cell of `j`, so the whole part of `E` over it lies in `p⁻¹(Xⁿ) ∖ Fⱼ`
  (`TauCeti.TopCat.ι_preimageSkeletonPairSingularHomologyIsoSigma_inv_comp_toComplFiber_of_ne`);
* on the summand of `j` it is an isomorphism
  (`TauCeti.TopCat.isIso_singularHomologyMap_cellDiskPullbackPairMap_comp_toComplFiber`). Over
  the disk of `j`, the part of the pullback over the boundary sphere may be replaced by the part
  over the punctured disk, by the radial deformation; excising the boundary sphere and then the
  part of `E` away from the open cell of `j` identifies the result with
  `(p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)`, because the characteristic map is a homeomorphism from the open
  ball onto the open cell, and the open cell is open in `Xⁿ`.

Hence `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ) ≅ Hq(Fⱼ)`
(`TauCeti.TopCat.preimageSkeletonComplFiberPairSingularHomologyIso`), and through it the
localization is the projection `⨁ᵢ Hq(Fᵢ) ⟶ Hq(Fⱼ)`
(`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma_inv_comp_toComplFiber`).

This compares the two descriptions of the shriek map `j_!` of the inclusion of a point used by
Barraud–Damian–Humilière–Oancea. Their Lemma 2.9 reads it through a lower skeleton,
`Hₖ(E) ⟶ Hₖ(E, E|_{Xⁿ⁻¹}) ≅ Hₖ₋ₙ(F)`, for a CW structure on an `n`-manifold base with a single
`n`-cell (their Proposition 2.6); the chart-free predicate `TauCeti.LivesOverFundamentalClass`
reads it through the localization
`Hₖ(E) ⟶ Hₖ(E, E ∖ F)`. For a class `α` of the part of `E` over `Xⁿ`, the two agree: `α` lives
over the fundamental class at `bⱼ` exactly when its image in
`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ≅ ⨁ᵢ Hq(Fᵢ)` has a nonzero component at `j`
(`TauCeti.TopCat.livesOverFundamentalClass_iff_π_preimageSkeletonPairSingularHomologyIsoSigma`).

## Main definitions

* `TauCeti.TopCat.preimageSkeletonComplFiberPair`: the pair `(p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)`.
* `TauCeti.TopCat.preimageSkeletonPairToComplFiber`: the map of pairs from the skeletal pair.
* `TauCeti.TopCat.preimageSkeletonComplFiberPairSingularHomologyIso`:
  `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ) ≅ Hq(Fⱼ)`.

## Main results

* `TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma_inv_comp_toComplFiber`: the
  localization at `Fⱼ` is the projection onto the summand of `j`.
* `TauCeti.TopCat.livesOverFundamentalClass_iff_π_preimageSkeletonPairSingularHomologyIsoSigma`:
  living over the fundamental class at the centre of a cell, read on the first page.
* `TauCeti.TopCat.isIso_singularHomologyMap_preimageSkeletonPairToComplFiber`,
  `TauCeti.TopCat.livesOverFundamentalClass_iff_singularHomologyπ_preimageSkeletonPair_ne_zero`:
  with a single `n`-cell, localizing at its fibre is the quotient by `p⁻¹(Xⁿ⁻¹)`, and a class lives
  over the fundamental class exactly when its image modulo `p⁻¹(Xⁿ⁻¹)` is nonzero.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §2.4, Definition 2.3, Proposition 2.6
  and Lemma 2.9.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, Lemma 2.34, and Section 5.1, the proof of Theorem 5.15.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]

section Pair

variable (p C) in
/-- The pair `(p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)`: the part of `E` over the `n`-skeleton
`Xⁿ = skeletonLT C (n + 1)`, relative to the complement of the fibre `Fⱼ` over the centre `χⱼ(0)`
of the `n`-cell `j`. Its relative homology is the target of the localization of the homology of
`p⁻¹(Xⁿ)` at `Fⱼ` (`TauCeti.fiberLocalization`). -/
abbrev preimageSkeletonComplFiberPair (n : ℕ) (j : cell C n) : TopPair.{u} :=
  TopPair.ofSubset (X := _root_.TopCat.of (p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)))
    (((fun x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) ↦ p x.1) ⁻¹' {map n j 0})ᶜ)

/-- The fibre over the centre of an `n`-cell misses the part of `E` over `Xⁿ⁻¹`. -/
private lemma map_ne_of_mem_preimage_skeletonLT {n : ℕ} (j : cell C n) {x : E}
    (hx : x ∈ p ⁻¹' (skeletonLT C n : Set B)) : p x ≠ map n j 0 := fun h ↦
  map_notMem_skeletonLT j (y := 0) (by simp) (by rw [← h]; exact hx)

variable (p C) in
/-- The identity of `p⁻¹(Xⁿ)` as a map of pairs `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)`,
for the fibre `Fⱼ` over the centre of the `n`-cell `j`. -/
def preimageSkeletonPairToComplFiber (n : ℕ) (j : cell C n) :
    preimageSkeletonPair p C n ⟶ preimageSkeletonComplFiberPair p C n j :=
  TopPair.ofHom (𝟙 _) (_root_.TopCat.ofHom
    ⟨fun x ↦ ⟨⟨x.1, preimage_mono (f := p) (skeletonLT_subset_skeletonLT_succ C n) x.2⟩,
      map_ne_of_mem_preimage_skeletonLT j x.2⟩, by fun_prop⟩) rfl

@[simp]
lemma preimageSkeletonPairToComplFiber_fst (n : ℕ) (j : cell C n) :
    TopPair.Hom.fst (preimageSkeletonPairToComplFiber p C n j) = 𝟙 _ :=
  (rfl)

end Pair

section CellDisk

variable (p C) in
/-- The projection `Pⱼ ⟶ Dⁿ` of the pullback of `p` along the characteristic map of `j`. -/
private abbrev diskProj (n : ℕ) (j : cell C n) :=
  _root_.TopCat.pullbackFst (cellULiftMap C n j) p

/-- A point of `Pⱼ` lies over the image of its point of the disk under the characteristic map. -/
private lemma apply_fst_cellDiskPullbackPairMap {n : ℕ} {j : cell C n}
    (x : (cellDiskPullbackPair p C n j).fst) :
    p (TopPair.Hom.fst (cellDiskPullbackPairMap p C n j) x).1 =
      map n j (diskProj p C n j x : ULift.{u} (Fin n → ℝ)).down := by
  have h : (TopPair.Hom.fst (cellDiskPullbackPairMap p C n j) x).1 = x.1.2 :=
    coe_cellDiskPullbackPairMap_fst_apply n j x
  rw [h, ← x.2, cellULiftMap_apply]
  rfl

omit [T2Space B] in
/-- The point of the disk of a point of `Pⱼ` has norm at most one. -/
private lemma norm_diskProj_le {n : ℕ} {j : cell C n} (x : (cellDiskPullbackPair p C n j).fst) :
    ‖(diskProj p C n j x : ULift.{u} (Fin n → ℝ)).down‖ ≤ 1 := by
  rw [ULift.norm_down]
  exact mem_closedBall_zero_iff.1 (diskProj p C n j x).2

end CellDisk

section OtherCells

/-- The part of `E` over the closed cell of `i` misses the fibre over the centre of the open cell
of `j ≠ i`. -/
private lemma map_ne_of_mem_cellDiskPullbackPair {n : ℕ} {i j : cell C n} (hij : i ≠ j)
    (x : (cellDiskPullbackPair p C n i).fst) :
    p (TopPair.Hom.fst (cellDiskPullbackPairMap p C n i) x).1 ≠ map n j 0 := by
  rw [apply_fst_cellDiskPullbackPairMap]
  exact (disjoint_closedCell_openCell_of_ne n le_rfl (by simpa using hij)).ne_of_mem
    ⟨_, mem_closedBall_zero_iff.2 (norm_diskProj_le x), rfl⟩ (map_zero_mem_openCell n j)

/-- **On the summand of a cell `i ≠ j` the localization at the fibre over the centre of `j`
vanishes.** The map `(Pᵢ, ∂Pᵢ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)` lands in the subspace. -/
theorem singularHomologyMap_cellDiskPullbackPairMap_comp_toComplFiber_of_ne (R : Type u) [Ring R]
    {n : ℕ} {i j : cell C n} (hij : i ≠ j) (k : ℕ) :
    (cellDiskPullbackPair p C n i).singularHomologyMap
      (cellDiskPullbackPairMap p C n i ≫ preimageSkeletonPairToComplFiber p C n j)
      (ModuleCat.of R R) k = 0 :=
  TopPair.singularHomologyMap_eq_zero_of_fac
    (cellDiskPullbackPairMap p C n i ≫ preimageSkeletonPairToComplFiber p C n j) (ModuleCat.of R R)
    (_root_.TopCat.ofHom ⟨fun x ↦ (⟨TopPair.Hom.fst (cellDiskPullbackPairMap p C n i) x,
      map_ne_of_mem_cellDiskPullbackPair hij x⟩ : (preimageSkeletonComplFiberPair p C n j).snd),
      (TopPair.Hom.fst (cellDiskPullbackPairMap p C n i)).hom.continuous.subtype_mk _⟩) rfl k

end OtherCells

section OwnCell

variable (p C)

/-- The pair `(Pⱼ, Pⱼ ∖ P⁰ⱼ)` of the pullback relative to its part over the punctured disk. -/
private abbrev puncturedPair (n : ℕ) (j : cell C n) : TopPair.{u} :=
  TopPair.ofSubset (diskProj p C n j ⁻¹' {x | (x : ULift.{u} (Fin n → ℝ)) ≠ 0})

/-- The part of the pullback over the open disk. -/
private abbrev openDiskPullback (n : ℕ) (j : cell C n) : Type u :=
  {x : (cellDiskPullbackPair p C n j).fst // ‖(diskProj p C n j x : ULift.{u} (Fin n → ℝ))‖ < 1}

/-- The part of the pullback over the open disk, relative to its part over the punctured open
disk. -/
private abbrev openPuncturedPair (n : ℕ) (j : cell C n) : TopPair.{u} :=
  TopPair.ofSubset (X := _root_.TopCat.of (openDiskPullback p C n j))
    {x | (diskProj p C n j x.1 : ULift.{u} (Fin n → ℝ)) ≠ 0}

/-- `(Pⱼ, ∂Pⱼ) ⟶ (Pⱼ, Pⱼ ∖ P⁰ⱼ)`. -/
private def toPuncturedPair (n : ℕ) (j : cell C n) :
    cellDiskPullbackPair p C n j ⟶ puncturedPair p C n j :=
  TopPair.ofSubsetMap (𝟙 _) fun x (hx : (diskProj p C n j x : ULift.{u} (Fin n → ℝ)) ∈ sphere 0 1)
    (h : (diskProj p C n j x : ULift.{u} (Fin n → ℝ)) = 0) ↦ by
      rw [mem_sphere_zero_iff_norm, h, norm_zero] at hx
      exact zero_ne_one hx

/-- The inclusion of the part over the open disk. -/
private def openToPuncturedPair (n : ℕ) (j : cell C n) :
    openPuncturedPair p C n j ⟶ puncturedPair p C n j :=
  TopPair.ofSubsetMap (_root_.TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩) fun _ hx ↦ hx

/-- `(Pⱼ, Pⱼ ∖ P⁰ⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)`. -/
private def puncturedToComplFiber (n : ℕ) (j : cell C n) :
    puncturedPair p C n j ⟶ preimageSkeletonComplFiberPair p C n j :=
  TopPair.ofSubsetMap (TopPair.Hom.fst (cellDiskPullbackPairMap p C n j)) fun x hx h ↦ by
    refine map_ne_map_zero j (norm_diskProj_le x) (fun h' ↦ hx ?_) ?_
    · exact congrArg ULift.up h'
    · rw [← apply_fst_cellDiskPullbackPairMap]
      exact h

omit [T2Space B] in
variable {p C} in
/-- A point of the pullback over the open disk lies over the open cell. -/
private lemma mem_openCell_of_openDiskPullback {n : ℕ} {j : cell C n}
    (x : openDiskPullback p C n j) : p x.1.1.2 ∈ openCell (C := C) n j := by
  rw [← x.1.2, cellULiftMap_apply]
  exact ⟨_, mem_ball_zero_iff.2 (by rw [ULift.norm_down]; exact x.2), rfl⟩

omit [T2Space B] in
variable {p C} in
/-- A point of `E` over the open cell lies over the image of a point of the open disk. -/
private lemma cellULiftMap_openCellHomeomorph_symm {n : ℕ} {j : cell C n}
    (e : (p ⁻¹' openCell (C := C) n j : Set E)) :
    cellULiftMap C n j ⟨ULift.up ((openCellHomeomorph n j).symm ⟨p e.1, e.2⟩ : Fin n → ℝ),
      mem_closedBall_zero_iff.2 (by
        rw [ULift.norm_up]
        exact (mem_ball_zero_iff.1 ((openCellHomeomorph n j).symm ⟨p e.1, e.2⟩).2).le)⟩ =
      p e.1 := by
  have h := congrArg Subtype.val ((openCellHomeomorph n j).apply_symm_apply ⟨p e.1, e.2⟩)
  rw [openCellHomeomorph_apply] at h
  rw [cellULiftMap_apply]
  exact h

/-- The projection `(y, e) ↦ e` is a homeomorphism from the part of `Pⱼ` over the open disk onto
the part of `E` over the open cell of `j`. -/
private def openDiskPullbackHomeomorph (n : ℕ) (j : cell C n) :
    openDiskPullback p C n j ≃ₜ (p ⁻¹' openCell (C := C) n j : Set E) where
  toFun x := ⟨x.1.1.2, mem_openCell_of_openDiskPullback x⟩
  invFun e := ⟨⟨(⟨ULift.up ((openCellHomeomorph n j).symm ⟨p e.1, e.2⟩ : Fin n → ℝ), _⟩, e.1),
    cellULiftMap_openCellHomeomorph_symm e⟩, by
      rw [ULift.norm_up]
      exact mem_ball_zero_iff.1 ((openCellHomeomorph n j).symm ⟨p e.1, e.2⟩).2⟩
  left_inv := by
    rintro ⟨⟨⟨⟨y, hy⟩, e⟩, hye⟩, hy₁⟩
    have hy₁' : ‖y.down‖ < 1 := by rwa [ULift.norm_down]
    have hs : (openCellHomeomorph n j).symm ⟨p e, mem_openCell_of_openDiskPullback
        ⟨⟨⟨⟨y, hy⟩, e⟩, hye⟩, hy₁⟩⟩ = ⟨y.down, mem_ball_zero_iff.2 hy₁'⟩ := by
      rw [Homeomorph.symm_apply_eq]
      refine Subtype.ext ?_
      rw [openCellHomeomorph_apply]
      exact hye.symm.trans (cellULiftMap_apply n j _)
    refine Subtype.ext (Subtype.ext (Prod.ext (Subtype.ext ?_) rfl))
    simp only
    rw [hs]
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    have hs : Continuous fun e : (p ⁻¹' openCell (C := C) n j : Set E) ↦
        ((openCellHomeomorph n j).symm ⟨p e.1, e.2⟩ : Fin n → ℝ) :=
      continuous_subtype_val.comp ((openCellHomeomorph n j).symm.continuous.comp
        ((p.hom.continuous.comp continuous_subtype_val).subtype_mk _))
    exact Continuous.subtype_mk (Continuous.subtype_mk (Continuous.prodMk
      ((continuous_uliftUp.comp hs).subtype_mk _) continuous_subtype_val) _) _

omit [T2Space B] in
/-- `(Pⱼ, ∂Pⱼ) ⟶ (Pⱼ, Pⱼ ∖ P⁰ⱼ)` is the identity of `Pⱼ`. -/
private lemma fst_toPuncturedPair_apply (n : ℕ) (j : cell C n)
    (x : (cellDiskPullbackPair p C n j).fst) :
    TopPair.Hom.fst (toPuncturedPair p C n j) x = x :=
  TopPair.ofSubsetMap_fst_apply _ _ x

omit [T2Space B] in
/-- The part of `Pⱼ` over the open disk is included in `Pⱼ`. -/
private lemma fst_openToPuncturedPair_apply (n : ℕ) (j : cell C n)
    (x : (openPuncturedPair p C n j).fst) :
    TopPair.Hom.fst (openToPuncturedPair p C n j) x = x.1 :=
  TopPair.ofSubsetMap_fst_apply _ _ x

/-- `(Pⱼ, Pⱼ ∖ P⁰ⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)` is the projection of `Pⱼ`. -/
private lemma fst_puncturedToComplFiber_apply (n : ℕ) (j : cell C n)
    (x : (puncturedPair p C n j).fst) :
    TopPair.Hom.fst (puncturedToComplFiber p C n j) x =
      TopPair.Hom.fst (cellDiskPullbackPairMap p C n j) x :=
  TopPair.ofSubsetMap_fst_apply _ _ x

variable (R : Type u) [Ring R]

omit [T2Space B] in
/-- **Excision of the part over the boundary sphere** from `(Pⱼ, Pⱼ ∖ P⁰ⱼ)`. -/
private lemma isIso_singularHomologyMap_openToPuncturedPair (n : ℕ) (j : cell C n) (k : ℕ) :
    IsIso ((openPuncturedPair p C n j).singularHomologyMap (openToPuncturedPair p C n j)
      (ModuleCat.of R R) k) := by
  have hc : Continuous fun x : (cellDiskPullbackPair p C n j).fst ↦
      (diskProj p C n j x : ULift.{u} (Fin n → ℝ)) :=
    continuous_subtype_val.comp (diskProj p C n j).hom.continuous
  have hval : ⇑(ConcreteCategory.hom (TopPair.Hom.fst (openToPuncturedPair p C n j))) =
      Subtype.val :=
    funext (fst_openToPuncturedPair_apply p C n j)
  refine TopPair.isIso_singularHomologyMap_of_open_cover _ _
    (by rw [hval]; exact IsEmbedding.subtypeVal) ?_
    (fun b : Bool ↦ bif b
      then {x | ‖(diskProj p C n j x : ULift.{u} (Fin n → ℝ))‖ < 1}
      else {x | (diskProj p C n j x : ULift.{u} (Fin n → ℝ)) ≠ 0})
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · intro x hx
    rw [TopPair.range_ofSubset_map, fst_openToPuncturedPair_apply] at hx
    rw [TopPair.range_ofSubset_map]
    exact hx
  · cases b
    · exact isOpen_ne_fun hc continuous_const
    · exact isOpen_lt (continuous_norm.comp hc) continuous_const
  · refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    by_cases hx : ‖(diskProj p C n j x : ULift.{u} (Fin n → ℝ))‖ < 1
    · exact ⟨true, hx⟩
    · refine ⟨false, fun (h : (diskProj p C n j x : ULift.{u} (Fin n → ℝ)) = 0) ↦ hx ?_⟩
      rw [h, norm_zero]
      exact one_pos
  · cases b
    · exact Or.inl (by rw [TopPair.range_ofSubset_map]; exact subset_rfl)
    · exact Or.inr fun x hx ↦ ⟨⟨x, hx⟩, fst_openToPuncturedPair_apply p C n j _⟩

/-- On the part of `Pⱼ` over the open disk, the map to `p⁻¹(Xⁿ)` is the projection of `Pⱼ`. -/
private lemma fst_openToPuncturedPair_comp_puncturedToComplFiber_apply (n : ℕ) (j : cell C n)
    (x : (openPuncturedPair p C n j).fst) :
    TopPair.Hom.fst (openToPuncturedPair p C n j ≫ puncturedToComplFiber p C n j) x =
      TopPair.Hom.fst (cellDiskPullbackPairMap p C n j) x.1 := by
  rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply, fst_puncturedToComplFiber_apply,
    fst_openToPuncturedPair_apply]

/-- Read in `E`, the part of `Pⱼ` over the open disk maps to `p⁻¹(Xⁿ)` by the homeomorphism onto
the part of `E` over the open cell. -/
private lemma coe_fst_openToPuncturedPair_comp_puncturedToComplFiber (n : ℕ) (j : cell C n)
    (x : (openPuncturedPair p C n j).fst) :
    (TopPair.Hom.fst (openToPuncturedPair p C n j ≫ puncturedToComplFiber p C n j) x).1 =
      (openDiskPullbackHomeomorph p C n j x).1 := by
  rw [fst_openToPuncturedPair_comp_puncturedToComplFiber_apply]
  exact coe_cellDiskPullbackPairMap_fst_apply n j x.1

/-- **Excision of the part away from the open cell** from `(p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)`, read through
the projection of the part of `Pⱼ` over the open disk. -/
private lemma isIso_singularHomologyMap_openToPuncturedPair_comp_puncturedToComplFiber (n : ℕ)
    (j : cell C n) (k : ℕ) :
    IsIso ((openPuncturedPair p C n j).singularHomologyMap
      (openToPuncturedPair p C n j ≫ puncturedToComplFiber p C n j) (ModuleCat.of R R) k) := by
  have hpc : Continuous fun x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) ↦ p x.1 :=
    p.hom.continuous.comp continuous_subtype_val
  have hf : IsEmbedding (TopPair.Hom.fst
      (openToPuncturedPair p C n j ≫ puncturedToComplFiber p C n j)) := by
    refine (IsEmbedding.of_comp_iff (IsEmbedding.subtypeVal
      (p := (· ∈ p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B))))).1 ?_
    have hval : Subtype.val ∘ ⇑(ConcreteCategory.hom (TopPair.Hom.fst
        (openToPuncturedPair p C n j ≫ puncturedToComplFiber p C n j))) =
        Subtype.val ∘ openDiskPullbackHomeomorph p C n j :=
      funext (coe_fst_openToPuncturedPair_comp_puncturedToComplFiber p C n j)
    rw [hval]
    exact IsEmbedding.subtypeVal.comp (openDiskPullbackHomeomorph p C n j).isEmbedding
  refine TopPair.isIso_singularHomologyMap_of_open_cover _ _ hf ?_
    (fun b : Bool ↦ bif b
      then {x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) | p x.1 ∈ openCell (C := C) n j}
      else {x | p x.1 ≠ map n j 0})
    (fun b ↦ ?_) ?_ (fun b ↦ ?_) k
  · -- A point over the punctured open disk lies outside the fibre over the centre.
    intro x hx
    rw [TopPair.range_ofSubset_map] at hx ⊢
    intro h
    apply hx
    exact (congrArg (fun y : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) ↦ p y.1)
      (fst_openToPuncturedPair_comp_puncturedToComplFiber_apply p C n j x)).trans
      ((apply_fst_cellDiskPullbackPairMap x.1).trans (congrArg (map n j) (congrArg ULift.down h)))
  · cases b
    · exact isOpen_ne_fun hpc continuous_const
    · exact (isOpen_preimage_val_openCell n (subset_refl _) j).preimage
        (hpc.subtype_mk fun x ↦ x.2)
  · refine eq_univ_of_forall fun x ↦ mem_iUnion.2 ?_
    by_cases hx : p x.1 = map n j 0
    · exact ⟨true, hx ▸ map_zero_mem_openCell n j⟩
    · exact ⟨false, hx⟩
  · cases b
    · exact Or.inl (by rw [TopPair.range_ofSubset_map]; exact fun x hx h ↦ hx h)
    · refine Or.inr fun x hx ↦ ?_
      obtain ⟨y, hy⟩ := (openDiskPullbackHomeomorph p C n j).surjective ⟨x.1, hx⟩
      exact ⟨y, Subtype.ext ((coe_fst_openToPuncturedPair_comp_puncturedToComplFiber p C n j
        y).trans (congrArg Subtype.val hy))⟩

/-- `(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)` factors through
`(Pⱼ, Pⱼ ∖ P⁰ⱼ)`. -/
private lemma cellDiskPullbackPairMap_comp_toComplFiber (n : ℕ) (j : cell C n) :
    cellDiskPullbackPairMap p C n j ≫ preimageSkeletonPairToComplFiber p C n j =
      toPuncturedPair p C n j ≫ puncturedToComplFiber p C n j := by
  have hfst (x : (cellDiskPullbackPair p C n j).fst) :
      TopPair.Hom.fst (cellDiskPullbackPairMap p C n j ≫ preimageSkeletonPairToComplFiber p C n j)
        x = TopPair.Hom.fst (toPuncturedPair p C n j ≫ puncturedToComplFiber p C n j) x := by
    have h : TopPair.Hom.fst (toPuncturedPair p C n j ≫ puncturedToComplFiber p C n j) x =
        TopPair.Hom.fst (cellDiskPullbackPairMap p C n j) x := by
      rw [TopPair.Hom.fst_comp, ConcreteCategory.comp_apply, fst_puncturedToComplFiber_apply,
        fst_toPuncturedPair_apply]
    -- The map `p⁻¹(Xⁿ) ⟶ p⁻¹(Xⁿ)` of `preimageSkeletonPairToComplFiber` is the identity.
    rw [h]
    rfl
  ext x : 2
  · apply (preimageSkeletonComplFiberPair p C n j).isEmbedding_map.injective
    rw [TopPair.Hom.w_apply, TopPair.Hom.w_apply]
    exact hfst _
  · exact hfst x

variable {p C} in
/-- **On the summand of `j` the localization at the fibre over its centre is an isomorphism.**
For a Serre fibration `p`, the map `(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)` induces isomorphisms on
relative singular homology. -/
theorem isIso_singularHomologyMap_cellDiskPullbackPairMap_comp_toComplFiber
    (hp : serreFibrations p) (n : ℕ) (j : cell C n) (k : ℕ) :
    IsIso ((cellDiskPullbackPair p C n j).singularHomologyMap
      (cellDiskPullbackPairMap p C n j ≫ preimageSkeletonPairToComplFiber p C n j)
      (ModuleCat.of R R) k) := by
  -- Replace the part over the boundary sphere by the part over the punctured disk.
  have h₁ : IsIso ((cellDiskPullbackPair p C n j).singularHomologyMap (toPuncturedPair p C n j)
      (ModuleCat.of R R) k) :=
    isIso_singularHomologyMap_ofSubsetMap_preimage_sphere R
      (mem_serreFibrations_pullbackFst hp (cellULiftMap C n j)) k
  -- Both excisions together identify `(Pⱼ, Pⱼ ∖ P⁰ⱼ)` with `(p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)`.
  have h₂ := isIso_singularHomologyMap_openToPuncturedPair p C R n j k
  have h₃ := isIso_singularHomologyMap_openToPuncturedPair_comp_puncturedToComplFiber p C R n j k
  rw [TopPair.singularHomologyMap_comp] at h₃
  have h₄ := IsIso.of_isIso_comp_left
    ((openPuncturedPair p C n j).singularHomologyMap (openToPuncturedPair p C n j)
      (ModuleCat.of R R) k)
    ((puncturedPair p C n j).singularHomologyMap (puncturedToComplFiber p C n j)
      (ModuleCat.of R R) k)
  rw [cellDiskPullbackPairMap_comp_toComplFiber, TopPair.singularHomologyMap_comp]
  infer_instance

end OwnCell

section Summand

variable (hp : serreFibrations p) (R : Type u) [Ring R]

/-- **The localization of the `n`-skeleton at the fibre over the centre of an `n`-cell.** For a
Serre fibration `p`, `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ; R) ≅ Hq(Fⱼ; R)`, where `Fⱼ = p⁻¹(χⱼ(0))`. Its
inverse is `Hq(Fⱼ) ≅ Hq+n(Pⱼ, ∂Pⱼ) ⟶ Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)`. -/
def preimageSkeletonComplFiberPairSingularHomologyIso (n q : ℕ) (j : cell C n) :
    (preimageSkeletonComplFiberPair p C n j).singularHomology (ModuleCat.of R R) (q + n) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {map n j 0} : Set E)) :=
  (@asIso _ _ _ _ _ (isIso_singularHomologyMap_cellDiskPullbackPairMap_comp_toComplFiber R hp n j
    (q + n))).symm ≪≫ cellDiskPullbackPairSingularHomologyIso hp R n q j

/-- The inverse of `TauCeti.TopCat.preimageSkeletonComplFiberPairSingularHomologyIso` passes
through the pullback along the characteristic map of the cell. -/
lemma preimageSkeletonComplFiberPairSingularHomologyIso_inv (n q : ℕ) (j : cell C n) :
    (preimageSkeletonComplFiberPairSingularHomologyIso hp R n q j).inv =
      (cellDiskPullbackPairSingularHomologyIso hp R n q j).inv ≫
        (cellDiskPullbackPair p C n j).singularHomologyMap
          (cellDiskPullbackPairMap p C n j ≫ preimageSkeletonPairToComplFiber p C n j)
          (ModuleCat.of R R) (q + n) :=
  (rfl)

/-- **On the summand of the cell `j`, the localization at its fibre is the identity** of
`Hq(Fⱼ)`, read through `TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma` and
`TauCeti.TopCat.preimageSkeletonComplFiberPairSingularHomologyIso`. -/
@[reassoc]
lemma ι_preimageSkeletonPairSingularHomologyIsoSigma_inv_comp_toComplFiber_self (n q : ℕ)
    (j : cell C n) :
    Sigma.ι _ j ≫ (preimageSkeletonPairSingularHomologyIsoSigma C hp R n q).inv ≫
      (preimageSkeletonPair p C n).singularHomologyMap (preimageSkeletonPairToComplFiber p C n j)
        (ModuleCat.of R R) (q + n) ≫
      (preimageSkeletonComplFiberPairSingularHomologyIso hp R n q j).hom = 𝟙 _ := by
  rw [ι_preimageSkeletonPairSingularHomologyIsoSigma_inv_assoc,
    ← TopPair.singularHomologyMap_comp_assoc, preimageSkeletonComplFiberPairSingularHomologyIso,
    Iso.trans_hom, Iso.symm_hom, asIso_inv, IsIso.hom_inv_id_assoc, Iso.inv_hom_id]

/-- **On the summand of a cell `i ≠ j`, the localization at the fibre over the centre of `j`
vanishes.** -/
@[reassoc]
lemma ι_preimageSkeletonPairSingularHomologyIsoSigma_inv_comp_toComplFiber_of_ne {n : ℕ}
    (q : ℕ) {i j : cell C n} (hij : i ≠ j) :
    Sigma.ι _ i ≫ (preimageSkeletonPairSingularHomologyIsoSigma C hp R n q).inv ≫
      (preimageSkeletonPair p C n).singularHomologyMap (preimageSkeletonPairToComplFiber p C n j)
        (ModuleCat.of R R) (q + n) = 0 := by
  rw [ι_preimageSkeletonPairSingularHomologyIsoSigma_inv_assoc,
    ← TopPair.singularHomologyMap_comp,
    singularHomologyMap_cellDiskPullbackPairMap_comp_toComplFiber_of_ne R hij, comp_zero]

/-- **The localization at the fibre over the centre of a cell is the projection onto its
summand** (Barraud–Damian–Humilière–Oancea, Lemma 2.9). Under
`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ≅ ⨁ᵢ Hq(Fᵢ)` and `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ) ≅ Hq(Fⱼ)`, the map
induced by `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)` is the projection
`⨁ᵢ Hq(Fᵢ) ⟶ Hq(Fⱼ)`. -/
theorem preimageSkeletonPairSingularHomologyIsoSigma_inv_comp_toComplFiber {n : ℕ}
    [DecidableEq (cell C n)] (q : ℕ) (j : cell C n) :
    (preimageSkeletonPairSingularHomologyIsoSigma C hp R n q).inv ≫
      (preimageSkeletonPair p C n).singularHomologyMap (preimageSkeletonPairToComplFiber p C n j)
        (ModuleCat.of R R) (q + n) ≫
      (preimageSkeletonComplFiberPairSingularHomologyIso hp R n q j).hom = Sigma.π _ j := by
  refine Sigma.hom_ext _ _ fun i ↦ ?_
  by_cases hij : i = j
  · subst hij
    rw [ι_preimageSkeletonPairSingularHomologyIsoSigma_inv_comp_toComplFiber_self]
    simp
  · rw [Sigma.ι_π_of_ne _ hij,
      ι_preimageSkeletonPairSingularHomologyIsoSigma_inv_comp_toComplFiber_of_ne_assoc hp R q hij,
      zero_comp]

/-- **The localization of `p⁻¹(Xⁿ)` at the fibre over the centre of an `n`-cell factors through
the skeletal pair** `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))`. -/
@[reassoc]
theorem singularHomologyπ_comp_singularHomologyMap_preimageSkeletonPairToComplFiber {n : ℕ}
    (k : ℕ) (j : cell C n) :
    (preimageSkeletonPair p C n).singularHomologyπ (ModuleCat.of R R) k ≫
      (preimageSkeletonPair p C n).singularHomologyMap (preimageSkeletonPairToComplFiber p C n j)
        (ModuleCat.of R R) k =
      fiberLocalization (ModuleCat.of R R)
        (fun x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) ↦ p x.1) (map n j 0) k := by
  rw [← TopPair.singularHomologyπ_naturality, preimageSkeletonPairToComplFiber_fst]
  -- The identity is that of the ambient space of the skeletal pair, which is the ambient space of
  -- the target pair only after unfolding the two `TopPair` constructors, so `erw` is needed.
  erw [_root_.TopCat.toSSet.map_id, SSet.homologyMap_id, Category.id_comp]

/-- **Living over the fundamental class, read on the first page of the skeletal filtration**
(Barraud–Damian–Humilière–Oancea, Lemma 2.9). A class
`α ∈ Hq+n(p⁻¹(Xⁿ); R)` lives over the fundamental class at the centre `χⱼ(0)` of an `n`-cell `j`
exactly when the component at `j` of its image in `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ≅ ⨁ᵢ Hq(Fᵢ; R)`
is nonzero. -/
theorem livesOverFundamentalClass_iff_π_preimageSkeletonPairSingularHomologyIsoSigma {n : ℕ}
    [DecidableEq (cell C n)] (q : ℕ) (j : cell C n)
    (α : ((_root_.TopCat.toSSet.obj (_root_.TopCat.of
      (p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)))).homology (ModuleCat.of R R) (q + n) :
        ModuleCat.{u} R)) :
    LivesOverFundamentalClass (ModuleCat.of R R)
        (fun x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) ↦ p x.1) (map n j 0) α ↔
      (Sigma.π (fun i : cell C n ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R)
        q).obj (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {map n i 0} : Set E))) j).hom
        ((preimageSkeletonPairSingularHomologyIsoSigma C hp R n q).hom
        (((preimageSkeletonPair p C n).singularHomologyπ (ModuleCat.of R R) (q + n)).hom α)) ≠
        0 := by
  have hπ := singularHomologyπ_comp_singularHomologyMap_preimageSkeletonPairToComplFiber (p := p) R
    (q + n) j
  have key : (preimageSkeletonPair p C n).singularHomologyMap
      (preimageSkeletonPairToComplFiber p C n j) (ModuleCat.of R R) (q + n) ≫
      (preimageSkeletonComplFiberPairSingularHomologyIso hp R n q j).hom =
      (preimageSkeletonPairSingularHomologyIsoSigma C hp R n q).hom ≫ Sigma.π _ j := by
    rw [← preimageSkeletonPairSingularHomologyIsoSigma_inv_comp_toComplFiber hp R q j,
      Iso.hom_inv_id_assoc]
  have hinj : Function.Injective
      (preimageSkeletonComplFiberPairSingularHomologyIso hp R n q j).hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  set y := ((preimageSkeletonPair p C n).singularHomologyπ (ModuleCat.of R R) (q + n)).hom α
  have e₁ : (fiberLocalization (ModuleCat.of R R)
      (fun x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) ↦ p x.1) (map n j 0) (q + n)).hom α =
      ((preimageSkeletonPair p C n).singularHomologyMap (preimageSkeletonPairToComplFiber p C n j)
        (ModuleCat.of R R) (q + n)).hom y := by
    rw [← hπ]
    rfl
  have e₂ : (preimageSkeletonComplFiberPairSingularHomologyIso hp R n q j).hom.hom
      (((preimageSkeletonPair p C n).singularHomologyMap (preimageSkeletonPairToComplFiber p C n j)
        (ModuleCat.of R R) (q + n)).hom y) =
      (Sigma.π (fun i : cell C n ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R)
        q).obj (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {map n i 0} : Set E))) j).hom
        ((preimageSkeletonPairSingularHomologyIsoSigma C hp R n q).hom.hom y) :=
    congrArg (fun f ↦ ModuleCat.Hom.hom f y) key
  rw [livesOverFundamentalClass_iff, e₁, ← map_ne_zero_iff _ hinj, e₂]

include hp in
/-- **With a single `n`-cell, the localization at its fibre is the quotient by `Xⁿ⁻¹`**
(Barraud–Damian–Humilière–Oancea, Lemma 2.9). If `j` is the only `n`-cell, the map
`(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ) ∖ Fⱼ)` induces isomorphisms on relative homology. -/
theorem isIso_singularHomologyMap_preimageSkeletonPairToComplFiber {n : ℕ}
    [Subsingleton (cell C n)] (q : ℕ) (j : cell C n) :
    IsIso ((preimageSkeletonPair p C n).singularHomologyMap
      (preimageSkeletonPairToComplFiber p C n j) (ModuleCat.of R R) (q + n)) := by
  classical
  -- Through the identifications with `⨁ᵢ Hq(Fᵢ)` and `Hq(Fⱼ)`, the map is the projection onto the
  -- only summand, which is inverse to its inclusion.
  have h : IsIso ((preimageSkeletonPairSingularHomologyIsoSigma C hp R n q).inv ≫
      (preimageSkeletonPair p C n).singularHomologyMap (preimageSkeletonPairToComplFiber p C n j)
        (ModuleCat.of R R) (q + n) ≫
      (preimageSkeletonComplFiberPairSingularHomologyIso hp R n q j).hom) := by
    rw [preimageSkeletonPairSingularHomologyIsoSigma_inv_comp_toComplFiber]
    refine ⟨⟨Sigma.ι (fun i : cell C n ↦ ((AlgebraicTopology.singularHomologyFunctor
      (ModuleCat.{u} R) q).obj (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {map n i 0} :
        Set E))) j, Sigma.hom_ext _ _ fun i ↦ ?_, by simp⟩⟩
    obtain rfl := Subsingleton.elim i j
    simp
  have h' := IsIso.of_isIso_comp_left (preimageSkeletonPairSingularHomologyIsoSigma C hp R n q).inv
    ((preimageSkeletonPair p C n).singularHomologyMap (preimageSkeletonPairToComplFiber p C n j)
        (ModuleCat.of R R) (q + n) ≫
      (preimageSkeletonComplFiberPairSingularHomologyIso hp R n q j).hom)
  exact IsIso.of_isIso_comp_right ((preimageSkeletonPair p C n).singularHomologyMap
    (preimageSkeletonPairToComplFiber p C n j) (ModuleCat.of R R) (q + n))
    (preimageSkeletonComplFiberPairSingularHomologyIso hp R n q j).hom

include hp in
/-- **Living over the fundamental class through the lower skeleton** (Barraud–Damian–Humilière–
Oancea, Proposition 2.6, (i) ⇔ (iii)). If `j` is the only `n`-cell, a class
`α ∈ Hk(p⁻¹(Xⁿ); R)` lives over the fundamental class at the centre of `j` exactly when its image in
`Hk(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R)` is nonzero. -/
theorem livesOverFundamentalClass_iff_singularHomologyπ_preimageSkeletonPair_ne_zero {n : ℕ}
    [Subsingleton (cell C n)] (q : ℕ) (j : cell C n)
    (α : ((_root_.TopCat.toSSet.obj (_root_.TopCat.of
      (p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)))).homology (ModuleCat.of R R) (q + n) :
        ModuleCat.{u} R)) :
    LivesOverFundamentalClass (ModuleCat.of R R)
        (fun x : p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B) ↦ p x.1) (map n j 0) α ↔
      ((preimageSkeletonPair p C n).singularHomologyπ (ModuleCat.of R R) (q + n)).hom α ≠ 0 := by
  have := isIso_singularHomologyMap_preimageSkeletonPairToComplFiber hp R q j
  have hinj : Function.Injective ((preimageSkeletonPair p C n).singularHomologyMap
      (preimageSkeletonPairToComplFiber p C n j) (ModuleCat.of R R) (q + n)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  rw [livesOverFundamentalClass_iff,
    ← singularHomologyπ_comp_singularHomologyMap_preimageSkeletonPairToComplFiber (p := p) R
      (q + n) j,
    ← map_ne_zero_iff _ hinj]
  rfl

end Summand

end TopCat

end TauCeti
