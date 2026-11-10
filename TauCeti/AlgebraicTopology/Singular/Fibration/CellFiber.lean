/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.AB
public import TauCeti.AlgebraicTopology.Singular.Additivity
public import TauCeti.AlgebraicTopology.Singular.Fibration.Cells
public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk
public import TauCeti.Topology.MetricSpace.Pseudo.ULift

/-!
# The skeletal filtration of a Serre fibration and the fibres over the cells

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta
`Xⁿ = skeletonLT C (n + 1)`. The relative homology of consecutive stages of the filtration
`Eₙ = p⁻¹(Xⁿ)` is the direct sum, over the `n`-cells `j`, of the homology of the fibre
`Fⱼ = p⁻¹(χⱼ(0))` over the centre of the cell, shifted by `n`:

`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ≅ ⨁ⱼ Hq(Fⱼ; R)`

(`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma`). These are the terms of the first
page of the spectral sequence of the filtration; for the identity fibration they are the cellular
chain groups.

The computation has three steps.

* `TauCeti.TopCat.preimageSkeletonPairSingularHomologyIso` identifies the left side with the
  relative homology of the pullback `(P, ∂P)` of `p` to the disjoint union of the disks of the
  `n`-cells, relative to its part over their boundary spheres.
* That pair is the coproduct in `TopPair` of the pullbacks `(Pⱼ, ∂Pⱼ)` of `p` along the
  characteristic maps of the single cells (`TauCeti.TopCat.isColimitCofanCellDiskPullbackPairι`),
  and relative singular homology is additive
  (`TopPair.isColimitCofanSingularHomologyOfIsColimit`).
* Each `Pⱼ ⟶ Dⁿ` is a Serre fibration over a disk, so `Hq+n(Pⱼ, ∂Pⱼ) ≅ Hq(Fⱼ)`
  (`TauCeti.TopCat.singularHomologyPreimageSphereIso`), and the fibre of `Pⱼ` over the centre of the
  disk is the fibre `Fⱼ` of `p` (`TauCeti.TopCat.cellDiskPullbackFiberHomeomorph`).

The disks of the single cells are lifted to the universe of `E` and `B`, so that the pullbacks
are Serre fibrations in `TopCat.{u}`.

## Main definitions and results

* `TauCeti.TopCat.cellDiskPullbackPair`: the pair `(Pⱼ, ∂Pⱼ)` of the pullback of `p` along the
  characteristic map of the cell `j`, relative to its part over the boundary sphere.
* `TauCeti.TopCat.cellDiskPullbackPairMap`: the projection
  `(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))`.
* `TauCeti.TopCat.isColimitCofanSingularHomologyPreimageSkeletonPair`: the maps it induces on
  relative homology exhibit `Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` as the coproduct of the `Hₖ(Pⱼ, ∂Pⱼ)`.
* `TauCeti.TopCat.cellDiskPullbackPairSingularHomologyIso`: `Hq+n(Pⱼ, ∂Pⱼ) ≅ Hq(Fⱼ)`.
* `TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma`:
  `Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹)) ≅ ⨁ⱼ Hq(Fⱼ)`, characterized on the summands by
  `TauCeti.TopCat.ι_preimageSkeletonPairSingularHomologyIsoSigma_inv`.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 5.1, the proof of Theorem 5.15.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Section 5.1.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex
open Homeomorph (uliftClosedBall coe_uliftClosedBall_apply)

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]

section CellDisk

variable (C) in
/-- The characteristic map of the `n`-cell `j` on the closed unit ball of `ℝⁿ`, with the ball lifted
to the universe of `B`. -/
def cellULiftMap (n : ℕ) (j : cell C n) :
    _root_.TopCat.of (closedBall (0 : ULift.{u} (Fin n → ℝ)) 1) ⟶ B :=
  _root_.TopCat.ofHom ⟨fun x ↦ map n j (uliftClosedBall 0 1 x : Fin n → ℝ),
    (continuousOn n j).comp_continuous
      (continuous_subtype_val.comp (uliftClosedBall (0 : ULift.{u} (Fin n → ℝ)) 1).continuous)
      fun x ↦ (uliftClosedBall 0 1 x).2⟩

omit [T2Space B] in
@[simp]
lemma cellULiftMap_apply (n : ℕ) (j : cell C n) (x : closedBall (0 : ULift.{u} (Fin n → ℝ)) 1) :
    cellULiftMap C n j x = map n j (x : ULift.{u} (Fin n → ℝ)).down :=
  congrArg (map n j) (coe_uliftClosedBall_apply 0 1 x)

variable (p C) in
/-- The pair `(Pⱼ, ∂Pⱼ)`: the pullback `Pⱼ` of `p` along the characteristic map of the `n`-cell
`j`, relative to its part `∂Pⱼ` over the boundary sphere of the disk. -/
abbrev cellDiskPullbackPair (n : ℕ) (j : cell C n) : TopPair.{u} :=
  TopPair.ofSubset (_root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹'
    {x | (x : ULift.{u} (Fin n → ℝ)) ∈ sphere 0 1})

variable (p C) in
/-- The inclusion `Pⱼ ⟶ P` of the pullback of `p` along the characteristic map of `j` into the
pullback of `p` to the disks of all `n`-cells. -/
private def cellDiskPullbackι (n : ℕ) (j : cell C n) :
    (cellDiskPullbackPair p C n j).fst ⟶ cellPullback p C n :=
  _root_.TopCat.ofHom ⟨fun x ↦ ⟨(⟨j, uliftClosedBall 0 1 x.1.1⟩, x.1.2),
      (sigmaCellMap_apply C n _).trans x.2⟩,
    (((continuous_sigmaMk (σ := fun _ : cell C n ↦ closedBall (0 : Fin n → ℝ) 1)).comp
      ((uliftClosedBall (0 : ULift.{u} (Fin n → ℝ)) 1).continuous.comp
        (continuous_fst.comp continuous_subtype_val))).prodMk
        (continuous_snd.comp continuous_subtype_val)).subtype_mk _⟩

omit [T2Space B] in
@[simp]
private lemma coe_cellDiskPullbackι_apply (n : ℕ) (j : cell C n)
    (x : (cellDiskPullbackPair p C n j).fst) :
    (cellDiskPullbackι p C n j x).1 = (⟨j, uliftClosedBall 0 1 x.1.1⟩, x.1.2) :=
  (rfl)

variable (p C) in
/-- The inclusion `(Pⱼ, ∂Pⱼ) ⟶ (P, ∂P)` of the pullback of `p` along the characteristic map of `j`
into the pullback of `p` to the disks of all `n`-cells, as a map of pairs. -/
def cellDiskPullbackPairι (n : ℕ) (j : cell C n) :
    cellDiskPullbackPair p C n j ⟶ cellPullbackPair p C n :=
  TopPair.ofSubsetMap (cellDiskPullbackι p C n j) fun x hx ↦ by
    rw [mem_ofPred_eq, coe_cellDiskPullbackι_apply, coe_uliftClosedBall_apply, ULift.norm_down]
    exact mem_sphere_zero_iff_norm.1 hx

omit [T2Space B] in
private lemma cellDiskPullbackPairι_fst_apply (n : ℕ) (j : cell C n)
    (x : (cellDiskPullbackPair p C n j).fst) :
    TopPair.Hom.fst (cellDiskPullbackPairι p C n j) x = cellDiskPullbackι p C n j x :=
  TopPair.ofSubsetMap_fst_apply _ _ x

omit [T2Space B] in
/-- The inclusion of `Pⱼ` lands over the disk of `j`. -/
@[simp]
lemma cellDiskPullbackPairι_fst_apply_fst_fst (n : ℕ) (j : cell C n)
    (x : (cellDiskPullbackPair p C n j).fst) :
    (TopPair.Hom.fst (cellDiskPullbackPairι p C n j) x).1.1.1 = j := by
  rw [cellDiskPullbackPairι_fst_apply, coe_cellDiskPullbackι_apply]

omit [T2Space B] in
/-- The inclusion of `Pⱼ` keeps the point of the disk. -/
@[simp]
lemma coe_cellDiskPullbackPairι_fst_apply_fst_snd (n : ℕ) (j : cell C n)
    (x : (cellDiskPullbackPair p C n j).fst) :
    ((TopPair.Hom.fst (cellDiskPullbackPairι p C n j) x).1.1.2 : Fin n → ℝ) =
      (x.1.1 : ULift.{u} (Fin n → ℝ)).down := by
  rw [cellDiskPullbackPairι_fst_apply, coe_cellDiskPullbackι_apply, coe_uliftClosedBall_apply]

omit [T2Space B] in
/-- The inclusion of `Pⱼ` keeps the point of the total space. -/
@[simp]
lemma cellDiskPullbackPairι_fst_apply_snd (n : ℕ) (j : cell C n)
    (x : (cellDiskPullbackPair p C n j).fst) :
    (TopPair.Hom.fst (cellDiskPullbackPairι p C n j) x).1.2 = x.1.2 := by
  rw [cellDiskPullbackPairι_fst_apply, coe_cellDiskPullbackι_apply]

omit [T2Space B] in
/-- The point of `Pⱼ` over the point of the disk of `j` that a point of `P` over that disk lies
over. -/
private lemma cellULiftMap_uliftClosedBall_symm (n : ℕ) (j : cell C n)
    (b : closedBall (0 : Fin n → ℝ) 1) (e : E) (h : sigmaCellMap C n ⟨j, b⟩ = p e) :
    cellULiftMap C n j ((uliftClosedBall (0 : ULift.{u} (Fin n → ℝ)) 1).symm b) = p e := by
  rw [← h, sigmaCellMap_apply, cellULiftMap_apply, ← coe_uliftClosedBall_apply,
    Homeomorph.apply_symm_apply]

omit [T2Space B] in
/-- `Pⱼ ⟶ P` is an open embedding onto the part of `P` over the disk of `j`. -/
private lemma isOpenEmbedding_cellDiskPullbackι (n : ℕ) (j : cell C n) :
    IsOpenEmbedding (cellDiskPullbackι p C n j) := by
  have hφ : IsEmbedding (Prod.map (fun b ↦ (⟨j, uliftClosedBall 0 1 b⟩ :
      Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1)) (id : E → E)) :=
    (((IsOpenEmbedding.sigmaMk (σ := fun _ : cell C n ↦ closedBall (0 : Fin n → ℝ) 1)
      (i := j)).comp (uliftClosedBall (0 : ULift.{u} (Fin n → ℝ)) 1).isOpenEmbedding).prodMap
        IsOpenEmbedding.id).isEmbedding
  refine ⟨IsEmbedding.subtypeVal.of_comp_iff.1 (hφ.comp IsEmbedding.subtypeVal), ?_⟩
  -- The range is the part of `P` over the disk of `j`.
  have : range (cellDiskPullbackι p C n j) =
      (fun y : cellPullback p C n ↦ y.1.1) ⁻¹' range (Sigma.mk j) := by
    ext ⟨⟨⟨k, b⟩, e⟩, h⟩
    constructor
    · rintro ⟨x, hx⟩
      rw [Subtype.ext_iff, coe_cellDiskPullbackι_apply] at hx
      exact ⟨_, congrArg Prod.fst hx⟩
    · rintro ⟨b', hb'⟩
      obtain ⟨rfl, hb⟩ := Sigma.mk.inj_iff.1 hb'
      obtain rfl := eq_of_heq hb
      exact ⟨⟨((uliftClosedBall (0 : ULift.{u} (Fin n → ℝ)) 1).symm b', e),
        cellULiftMap_uliftClosedBall_symm n j b' e h⟩, Subtype.ext <|
          (coe_cellDiskPullbackι_apply n j _).trans (by rw [Homeomorph.apply_symm_apply])⟩
  rw [this]
  exact isOpen_range_sigmaMk.preimage (continuous_fst.comp continuous_subtype_val)

omit [T2Space B] in
/-- The disjoint union of the `Pⱼ` maps homeomorphically onto `P`. -/
private lemma isHomeomorph_sigmaCellDiskPullbackι (n : ℕ) :
    IsHomeomorph fun x : Σ j : cell C n, (cellDiskPullbackPair p C n j).fst ↦
      cellDiskPullbackι p C n x.1 x.2 := by
  refine ⟨continuous_sigma fun j ↦ (cellDiskPullbackι p C n j).hom.continuous,
    isOpenMap_sigma.2 fun j ↦ (isOpenEmbedding_cellDiskPullbackι n j).isOpenMap, ?_⟩
  -- The inverse reads off the cell from the first coordinate.
  refine Function.bijective_iff_has_inverse.2
    ⟨fun y ↦ ⟨y.1.1.1, ⟨((uliftClosedBall (0 : ULift.{u} (Fin n → ℝ)) 1).symm y.1.1.2, y.1.2),
      cellULiftMap_uliftClosedBall_symm n _ _ _ y.2⟩⟩, fun x ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨j, ⟨⟨b, e⟩, h⟩⟩ := x
    exact Sigma.ext rfl <| heq_of_eq <| Subtype.ext <|
      Prod.ext ((uliftClosedBall (0 : ULift.{u} (Fin n → ℝ)) 1).symm_apply_apply b) rfl
  · obtain ⟨⟨⟨j, b⟩, e⟩, h⟩ := y
    exact Subtype.ext <|
      (coe_cellDiskPullbackι_apply n j _).trans (by rw [Homeomorph.apply_symm_apply])

variable (p C) in
/-- **The pullback to the disks of the `n`-cells is the disjoint union of the pullbacks to the
single cells.** The inclusions `(Pⱼ, ∂Pⱼ) ⟶ (P, ∂P)` exhibit `(P, ∂P)` as the coproduct of the
pairs `(Pⱼ, ∂Pⱼ)` in `TopPair`. -/
def isColimitCofanCellDiskPullbackPairι (n : ℕ) :
    IsColimit (Cofan.mk (cellPullbackPair p C n) (cellDiskPullbackPairι p C n)) :=
  let hσ := TopPair.sigmaCofanIsColimit (cellDiskPullbackPair p C n)
  let σ := hσ.desc (Cofan.mk (cellPullbackPair p C n) (cellDiskPullbackPairι p C n))
  -- On the summand of `j`, `σ` is the inclusion of `Pⱼ`.
  have hσ_fst (x : Σ j : cell C n, (cellDiskPullbackPair p C n j).fst) :
      TopPair.Hom.fst σ x = cellDiskPullbackι p C n x.1 x.2 :=
    (ConcreteCategory.congr_hom (congrArg TopPair.Hom.fst (hσ.fac _ ⟨x.1⟩)) x.2).trans
      (cellDiskPullbackPairι_fst_apply n x.1 x.2)
  have : IsIso (TopPair.Hom.fst σ) := by
    rw [_root_.TopCat.isIso_iff_isHomeomorph, (funext hσ_fst : ⇑(TopPair.Hom.fst σ) = _)]
    exact isHomeomorph_sigmaCellDiskPullbackι n
  have : IsIso σ := TopPair.isIso_of_isIso_fst_of_surjective_snd σ fun y ↦ by
    -- A point over a boundary sphere comes from the pullback to its cell, over the sphere.
    obtain ⟨x, hx⟩ := (isHomeomorph_sigmaCellDiskPullbackι (p := p) n).bijective.2 y.1
    have hy : ‖(y.1.1.1.2 : Fin n → ℝ)‖ = 1 := y.2
    rw [← hx, coe_cellDiskPullbackι_apply, coe_uliftClosedBall_apply] at hy
    -- Membership in `∂Pⱼ` is membership of the point of the disk in the sphere.
    refine ⟨⟨x.1, x.2, (by simpa using hy : (x.2.1.1 : ULift.{u} (Fin n → ℝ)) ∈ sphere 0 1)⟩,
      Subtype.ext ?_⟩
    exact (TopPair.Hom.w_apply σ _).trans ((hσ_fst _).trans hx)
  IsColimit.ofIsoColimit hσ (Cofan.ext (asIso σ) fun j ↦ hσ.fac _ ⟨j⟩)

omit [T2Space B] in
variable (p C) in
/-- The fibre of `Pⱼ ⟶ Dⁿ` over the centre of the disk is the fibre of `p` over the centre
`χⱼ(0)` of the cell. -/
def cellDiskPullbackFiberHomeomorph (n : ℕ) (j : cell C n) :
    (_root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹'
        {x | (x : ULift.{u} (Fin n → ℝ)) = 0} : Set (cellDiskPullbackPair p C n j).fst) ≃ₜ
      (p ⁻¹' {map n j 0} : Set E) where
  toFun x := ⟨x.1.1.2, by
    have hx : (x.1.1.1 : ULift.{u} (Fin n → ℝ)) = 0 := x.2
    rw [mem_preimage, mem_singleton_iff, ← x.1.2, cellULiftMap_apply, hx, ULift.zero_down]⟩
  invFun e := ⟨⟨(⟨0, mem_closedBall_self zero_le_one⟩, e.1), by
    rw [cellULiftMap_apply, ULift.zero_down]
    exact e.2.symm⟩, rfl⟩
  left_inv x := by
    obtain ⟨⟨⟨⟨b, hb⟩, e⟩, h⟩, hx⟩ := x
    have hb0 : b = 0 := hx
    subst hb0
    rfl
  right_inv e := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [T2Space B] in
/-- The identification of the fibres keeps the point of the total space. -/
lemma coe_cellDiskPullbackFiberHomeomorph_apply (n : ℕ) (j : cell C n)
    (x : (_root_.TopCat.pullbackFst (cellULiftMap C n j) p ⁻¹'
        {x | (x : ULift.{u} (Fin n → ℝ)) = 0} : Set (cellDiskPullbackPair p C n j).fst)) :
    (cellDiskPullbackFiberHomeomorph p C n j x : E) = x.1.1.2 :=
  (rfl)

omit [T2Space B] in
/-- The inverse identification of the fibres puts a point of the fibre of `p` over the centre of
the disk. -/
lemma coe_cellDiskPullbackFiberHomeomorph_symm_apply (n : ℕ) (j : cell C n)
    (e : (p ⁻¹' {map n j 0} : Set E)) :
    ((cellDiskPullbackFiberHomeomorph p C n j).symm e).1.1 =
      (⟨0, mem_closedBall_self zero_le_one⟩, e.1) :=
  (rfl)

end CellDisk

section Homology

variable (hp : serreFibrations p) (R : Type u) [Ring R]

variable (p C) in
/-- The projection `(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the pullback of `p` along the
characteristic map of the `n`-cell `j` to consecutive stages of the skeletal filtration. -/
def cellDiskPullbackPairMap (n : ℕ) (j : cell C n) :
    cellDiskPullbackPair p C n j ⟶ preimageSkeletonPair p C n :=
  cellDiskPullbackPairι p C n j ≫ cellPullbackPairMap p C n

@[simp]
lemma coe_cellDiskPullbackPairMap_fst_apply (n : ℕ) (j : cell C n)
    (x : (cellDiskPullbackPair p C n j).fst) :
    (ConcreteCategory.hom (Y := _root_.TopCat.of
      (p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)))
      (TopPair.Hom.fst (cellDiskPullbackPairMap p C n j)) x).1 = x.1.2 :=
  (coe_cellPullbackPairMap_fst_apply n _).trans (cellDiskPullbackPairι_fst_apply_snd n j x)

include hp

variable (C) in
/-- **The relative homology of consecutive stages of the skeletal filtration of a Serre fibration is
the direct sum of the contributions of the cells.** The projections
`(Pⱼ, ∂Pⱼ) ⟶ (p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))` from the pullbacks of `p` along the characteristic maps of the
`n`-cells exhibit `Hₖ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R)` as the coproduct of the `Hₖ(Pⱼ, ∂Pⱼ; R)`. -/
def isColimitCofanSingularHomologyPreimageSkeletonPair (n k : ℕ) :
    IsColimit (Cofan.mk ((preimageSkeletonPair p C n).singularHomology (ModuleCat.of R R) k)
      fun j ↦ (cellDiskPullbackPair p C n j).singularHomologyMap (cellDiskPullbackPairMap p C n j)
        (ModuleCat.of R R) k) :=
  have := isIso_singularHomologyMap_cellPullbackPairMap C hp R n k
  IsColimit.ofIsoColimit (TopPair.isColimitCofanSingularHomologyOfIsColimit (ModuleCat.{u} R)
      (ModuleCat.of R R) k (isColimitCofanCellDiskPullbackPairι p C n))
    (Cofan.ext (asIso ((cellPullbackPair p C n).singularHomologyMap (cellPullbackPairMap p C n)
      (ModuleCat.of R R) k)) fun j ↦ by
        simp [cellDiskPullbackPairMap, TopPair.singularHomologyMap_comp])

/-- **The homology of the pullback of a Serre fibration along the characteristic map of a cell,
relative to its part over the boundary sphere, is the homology of the fibre over the centre of the
cell, shifted by the dimension:** `Hq+n(Pⱼ, ∂Pⱼ; R) ≅ Hq(p⁻¹(χⱼ(0)); R)`. -/
def cellDiskPullbackPairSingularHomologyIso (n q : ℕ) (j : cell C n) :
    (cellDiskPullbackPair p C n j).singularHomology (ModuleCat.of R R) (q + n) ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {map n j 0} : Set E)) :=
  singularHomologyPreimageSphereIso R (mem_serreFibrations_pullbackFst hp (cellULiftMap C n j)) q
      (q + n) (by simp) ≪≫
    ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R)).mapIso
      (_root_.TopCat.isoOfHomeo (cellDiskPullbackFiberHomeomorph p C n j))

variable (C) in
/-- **The first page of the skeletal filtration of a Serre fibration.** For a Serre fibration
`p : E ⟶ B` and a relative CW complex `C ⊆ B` with skeleta `Xⁿ`,
`Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) ≅ ⨁ⱼ Hq(p⁻¹(χⱼ(0)); R)`, the sum running over the `n`-cells `j` of
`C` and `χⱼ(0)` being the centre of the cell `j`. On the summand of `j` the inverse is
`Hq(p⁻¹(χⱼ(0))) ≅ Hq+n(Pⱼ, ∂Pⱼ) ⟶ Hq+n(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))`
(`TauCeti.TopCat.ι_preimageSkeletonPairSingularHomologyIsoSigma_inv`). -/
def preimageSkeletonPairSingularHomologyIsoSigma (n q : ℕ) :
    (preimageSkeletonPair p C n).singularHomology (ModuleCat.of R R) (q + n) ≅
      ∐ fun j : cell C n ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {map n j 0} : Set E)) :=
  (isColimitCofanSingularHomologyPreimageSkeletonPair C hp R n (q + n)).coconePointUniqueUpToIso
      (coproductIsCoproduct _) ≪≫
    Sigma.mapIso fun j ↦ cellDiskPullbackPairSingularHomologyIso hp R n q j

@[reassoc (attr := simp)]
lemma ι_preimageSkeletonPairSingularHomologyIsoSigma_inv (n q : ℕ) (j : cell C n) :
    Sigma.ι _ j ≫ (preimageSkeletonPairSingularHomologyIsoSigma C hp R n q).inv =
      (cellDiskPullbackPairSingularHomologyIso hp R n q j).inv ≫
        (cellDiskPullbackPair p C n j).singularHomologyMap (cellDiskPullbackPairMap p C n j)
          (ModuleCat.of R R) (q + n) := by
  rw [preimageSkeletonPairSingularHomologyIsoSigma, Iso.trans_inv, Sigma.ι_mapIso_inv_assoc]
  exact congrArg _ ((isColimitCofanSingularHomologyPreimageSkeletonPair C hp R n
    (q + n)).comp_coconePointUniqueUpToIso_inv (coproductIsCoproduct _) ⟨j⟩)

end Homology

end TopCat

end TauCeti
