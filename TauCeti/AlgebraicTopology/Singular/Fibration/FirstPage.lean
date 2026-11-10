/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Fibration.Cells
public import TauCeti.AlgebraicTopology.Singular.Fibration.Disk
import Mathlib.Algebra.Category.ModuleCat.AB
import TauCeti.AlgebraicTopology.Singular.Additivity

/-!
# The first page of the skeletal filtration of a Serre fibration

Let `p : E ⟶ B` be a Serre fibration and `C ⊆ B` a relative CW complex with skeleta
`Xⁿ = skeletonLT C (n + 1)`. The first page of the spectral sequence of the filtration of `E` by
the preimages `Eₙ = p⁻¹(Xⁿ)` consists of the relative homology groups `Hₘ(Eₙ, Eₙ₋₁; R)`. This file
computes them in terms of the fibres of `p`: writing `xⱼ = map n j 0` for the centre of the
`n`-cell `j`,

* `H_{q+n}(Eₙ, Eₙ₋₁; R) ≅ ⨁ⱼ H_q(p⁻¹(xⱼ); R)`, the sum over the `n`-cells
  (`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma`);
* `Hₘ(Eₙ, Eₙ₋₁; R) = 0` for `m < n`
  (`TauCeti.TopCat.isZero_singularHomology_preimageSkeletonPair_of_lt`).

On the summand of the cell `j`, the isomorphism is induced by the projection to `E` of the pullback
of `p` to the disk of `j`, relative to its part over the boundary sphere
(`TauCeti.TopCat.ι_preimageSkeletonPairSingularHomologyIsoSigma_inv`). This is the description of
the first page from which the second page is computed as the cellular homology of the base with
coefficients in the homology of the fibres.

The proof assembles three computations.

* The projection from the pullback `P` of `p` to the disjoint union of the disks of the `n`-cells,
  relative to its part `∂P` over the boundary spheres, identifies `Hₘ(Eₙ, Eₙ₋₁; R)` with
  `Hₘ(P, ∂P; R)` (`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIso`).
* The pair `(P, ∂P)` is the disjoint union, over the cells `j`, of the pullbacks `(Pⱼ, ∂Pⱼ)` of
  `p` to the disk of `j` (`TauCeti.TopCat.sigmaCellFibrationPairIso`), and relative singular
  homology is additive (`TopPair.isColimitCofanSingularHomology`).
* Each `Pⱼ` is a Serre fibration over the disk, so `H_{q+n}(Pⱼ, ∂Pⱼ; R)` is the homology of its
  fibre over the centre (`TauCeti.TopCat.singularHomologyPreimageSphereIso`), which is the fibre
  of `p` over `xⱼ`.

The disk computation is stated for a base in the universe of the total space, so the disk of a
cell is taken here to be the closed unit ball of `ULift (Fin n → ℝ)`.

## Main definitions and results

* `TauCeti.TopCat.cellFibrationPair`: the pullback `(Pⱼ, ∂Pⱼ)` of `p` to the disk of the
  `n`-cell `j`, relative to its part over the boundary sphere, with its projection
  `TauCeti.TopCat.cellFibrationPairMap` to `(Eₙ, Eₙ₋₁)`.
* `TauCeti.TopCat.sigmaCellFibrationPairIso`: `∐ⱼ (Pⱼ, ∂Pⱼ) ≅ (P, ∂P)`.
* `TauCeti.TopCat.cellFibrationPairSingularHomologyIso`:
  `H_{q+n}(Pⱼ, ∂Pⱼ; R) ≅ H_q(p⁻¹(xⱼ); R)`.
* `TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma`:
  `H_{q+n}(Eₙ, Eₙ₋₁; R) ≅ ⨁ⱼ H_q(p⁻¹(xⱼ); R)`.
* `TauCeti.TopCat.isZero_singularHomology_preimageSkeletonPair_of_lt`: the vanishing below the
  filtration degree.

## References

* J.-P. Serre, *Homologie singulière des espaces fibrés. Applications*, Ann. of Math. 54 (1951),
  Chapter II.
* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 5.1.
* J. McCleary, *A User's Guide to Spectral Sequences*, 2nd ed., Section 5.1.
-/

public section

noncomputable section

universe u

open CategoryTheory Limits Metric Set Topology Topology.RelCWComplex

namespace TauCeti

namespace TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} [T2Space B] {C D : Set B} [RelCWComplex C D]

/-- The closed unit ball of `ULift (Fin n → ℝ)` is homeomorphic to that of `Fin n → ℝ`. -/
private abbrev uliftBallHomeomorph (n : ℕ) :
    closedBall (0 : ULift.{u} (Fin n → ℝ)) 1 ≃ₜ closedBall (0 : Fin n → ℝ) 1 :=
  Homeomorph.ulift.subtype fun _ ↦ Iff.rfl

variable (C) in
/-- The characteristic map of the `n`-cell `j`, on the closed unit ball of
`ULift (Fin n → ℝ)`. -/
def cellDiskMap (n : ℕ) (j : cell C n) :
    _root_.TopCat.of (closedBall (0 : ULift.{u} (Fin n → ℝ)) 1) ⟶ B :=
  _root_.TopCat.ofHom ((sigmaCellMap C n).comp
    ⟨fun y ↦ ⟨j, uliftBallHomeomorph n y⟩,
      continuous_sigmaMk.comp (uliftBallHomeomorph n).continuous⟩)

omit [T2Space B] in
@[simp]
lemma cellDiskMap_apply (n : ℕ) (j : cell C n) (y : closedBall (0 : ULift.{u} (Fin n → ℝ)) 1) :
    cellDiskMap C n j y = map n j (y : ULift (Fin n → ℝ)).down :=
  sigmaCellMap_apply C n _

variable (p C) in
/-- The pullback of `p` along the characteristic map of the `n`-cell `j`. -/
abbrev cellFibration (n : ℕ) (j : cell C n) :=
  _root_.TopCat.pullbackFst (cellDiskMap C n j) p

variable (p C) in
/-- The pair of the pullback of `p` to the disk of the `n`-cell `j`, relative to its part over
the boundary sphere. -/
abbrev cellFibrationPair (n : ℕ) (j : cell C n) : TopPair.{u} :=
  TopPair.ofSubset (cellFibration p C n j ⁻¹'
    {x | (x : ULift.{u} (Fin n → ℝ)) ∈ sphere (0 : ULift.{u} (Fin n → ℝ)) 1})

/-- The map from the disjoint union of the pullbacks to the individual disks onto the pullback to
the disjoint union of the disks. -/
private def sigmaCellFibrationFun (n : ℕ)
    (x : Σ j : cell C n, (cellFibrationPair p C n j).fst) : cellPullback p C n :=
  ⟨(⟨x.1, uliftBallHomeomorph n x.2.1.1⟩, x.2.1.2), x.2.2⟩

omit [T2Space B] in
private lemma continuous_sigmaCellFibrationFun_mk (n : ℕ) (j : cell C n) :
    Continuous fun x : (cellFibrationPair p C n j).fst ↦
      sigmaCellFibrationFun (p := p) n ⟨j, x⟩ :=
  Continuous.subtype_mk ((((continuous_sigmaMk (σ := fun _ : cell C n ↦
    closedBall (0 : Fin n → ℝ) 1) (i := j)).comp ((uliftBallHomeomorph n).continuous.comp
    (continuous_fst.comp continuous_subtype_val))).prodMk
      (continuous_snd.comp continuous_subtype_val))) fun x ↦ x.2

omit [T2Space B] in
private lemma isOpenEmbedding_sigmaCellFibrationFun_mk (n : ℕ) (j : cell C n) :
    IsOpenEmbedding fun x : (cellFibrationPair p C n j).fst ↦
      sigmaCellFibrationFun (p := p) n ⟨j, x⟩ := by
  refine ⟨?_, ?_⟩
  · refine (IsEmbedding.of_comp_iff IsEmbedding.subtypeVal).1 ?_
    have h : IsEmbedding (Prod.map (fun y ↦ (⟨j, uliftBallHomeomorph.{u} n y⟩ :
        Σ _ : cell C n, closedBall (0 : Fin n → ℝ) 1)) (id : E → E)) :=
      ((IsEmbedding.sigmaMk (σ := fun _ : cell C n ↦ closedBall (0 : Fin n → ℝ) 1)
        (i := j)).comp (uliftBallHomeomorph n).isEmbedding).prodMap IsEmbedding.id
    exact h.comp IsEmbedding.subtypeVal
  · have hr : range (fun x : (cellFibrationPair p C n j).fst ↦
        sigmaCellFibrationFun (p := p) n ⟨j, x⟩) =
        (fun x : cellPullback p C n ↦ x.1.1) ⁻¹' range (Sigma.mk j) := by
      ext ⟨⟨⟨j', y⟩, e⟩, h⟩
      constructor
      · rintro ⟨x, hx⟩
        rw [← hx]
        exact ⟨_, rfl⟩
      · rintro ⟨y', hy'⟩
        obtain ⟨rfl, hy⟩ := Sigma.mk.inj hy'
        exact ⟨⟨((uliftBallHomeomorph n).symm y, e), h⟩, rfl⟩
    rw [hr]
    exact isOpen_range_sigmaMk.preimage (continuous_fst.comp continuous_subtype_val)

variable (p C) in
/-- The pullback of `p` to the disjoint union of the disks of the `n`-cells is the disjoint union
of the pullbacks of `p` to the individual disks. -/
def sigmaCellFibrationHomeomorph (n : ℕ) :
    (Σ j : cell C n, (cellFibrationPair p C n j).fst) ≃ₜ cellPullback p C n :=
  Equiv.toHomeomorphOfContinuousOpen
    { toFun := sigmaCellFibrationFun n
      invFun x := ⟨x.1.1.1, ⟨((uliftBallHomeomorph n).symm x.1.1.2, x.1.2), x.2⟩⟩
      left_inv _ := rfl
      right_inv _ := rfl }
    (continuous_sigma fun j ↦ continuous_sigmaCellFibrationFun_mk n j)
    (isOpenMap_sigma.2 fun j ↦ (isOpenEmbedding_sigmaCellFibrationFun_mk n j).isOpenMap)

omit [T2Space B] in
@[simp]
lemma sigmaCellFibrationHomeomorph_apply_fst_fst_fst (n : ℕ)
    (x : Σ j : cell C n, (cellFibrationPair p C n j).fst) :
    (sigmaCellFibrationHomeomorph p C n x).1.1.1 = x.1 :=
  (rfl)

omit [T2Space B] in
@[simp]
lemma coe_sigmaCellFibrationHomeomorph_apply_fst_fst_snd (n : ℕ)
    (x : Σ j : cell C n, (cellFibrationPair p C n j).fst) :
    ((sigmaCellFibrationHomeomorph p C n x).1.1.2 : Fin n → ℝ) =
      (x.2.1.1 : ULift.{u} (Fin n → ℝ)).down :=
  (rfl)

omit [T2Space B] in
@[simp]
lemma sigmaCellFibrationHomeomorph_apply_fst_snd (n : ℕ)
    (x : Σ j : cell C n, (cellFibrationPair p C n j).fst) :
    (sigmaCellFibrationHomeomorph p C n x).1.2 = x.2.1.2 :=
  (rfl)

variable (p C) in
/-- The map of pairs from the disjoint union of the pullback pairs over the individual `n`-cells to
the pullback pair over all of them. -/
private def sigmaCellFibrationPairHom (n : ℕ) :
    TopPair.sigma (cellFibrationPair p C n) ⟶ cellPullbackPair p C n :=
  TopPair.ofHom (_root_.TopCat.ofHom (sigmaCellFibrationHomeomorph p C n : C(_, _)))
    (_root_.TopCat.ofHom ⟨fun q ↦ ⟨sigmaCellFibrationHomeomorph p C n
        ((TopPair.sigma (cellFibrationPair p C n)).map q), mem_sphere_zero_iff_norm.1 q.2.2⟩,
      ((sigmaCellFibrationHomeomorph p C n).continuous.comp
        (TopPair.sigma (cellFibrationPair p C n)).map.hom.continuous).subtype_mk _⟩)
    (by ext; rfl)

omit [T2Space B] in
private lemma surjective_snd_sigmaCellFibrationPairHom (n : ℕ) :
    Function.Surjective (TopPair.Hom.snd (sigmaCellFibrationPairHom p C n)) := by
  rintro ⟨x, hx⟩
  exact ⟨⟨_, ⟨((sigmaCellFibrationHomeomorph p C n).symm x).2, mem_sphere_zero_iff_norm.2 hx⟩⟩,
    Subtype.ext ((sigmaCellFibrationHomeomorph p C n).apply_symm_apply x)⟩

variable (p C) in
/-- **The pullback pair over the `n`-cells is the disjoint union of the pullback pairs over the
individual cells.** -/
def sigmaCellFibrationPairIso (n : ℕ) :
    TopPair.sigma (cellFibrationPair p C n) ≅ cellPullbackPair p C n :=
  have : IsIso (TopPair.Hom.fst (sigmaCellFibrationPairHom p C n)) :=
    inferInstanceAs (IsIso (_root_.TopCat.isoOfHomeo
      (X := (TopPair.sigma (cellFibrationPair p C n)).fst) (Y := cellPullback p C n)
      (sigmaCellFibrationHomeomorph p C n)).hom)
  have := TopPair.isIso_of_isIso_fst_of_surjective_snd _
    (surjective_snd_sigmaCellFibrationPairHom (p := p) (C := C) n)
  asIso (sigmaCellFibrationPairHom p C n)

/-- The centre of the closed unit ball. -/
private abbrev ballCenter (n : ℕ) : closedBall (0 : ULift.{u} (Fin n → ℝ)) 1 :=
  ⟨0, mem_closedBall_self zero_le_one⟩

variable (p C) in
/-- The fibre of the pullback of `p` to the disk of the `n`-cell `j` over the centre of the disk is
the fibre of `p` over the centre of the cell. -/
def cellFibrationFiberHomeomorph (n : ℕ) (j : cell C n) :
    (cellFibration p C n j ⁻¹' {x | (x : ULift.{u} (Fin n → ℝ)) = 0}) ≃ₜ
      (p ⁻¹' {map n j 0} : Set E) where
  toFun x := ⟨x.1.1.2, by
    have h : x.1.1.1 = ballCenter n := Subtype.ext x.2
    rw [mem_preimage, mem_singleton_iff, ← x.1.2, h, cellDiskMap_apply]
    rfl⟩
  invFun e := ⟨⟨(ballCenter n, e.1), (cellDiskMap_apply n j _).trans e.2.symm⟩, rfl⟩
  left_inv x := Subtype.ext <| Subtype.ext <| Prod.ext (Subtype.ext x.2.symm) rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

omit [T2Space B] in
@[simp]
lemma sigmaCellFibrationPairIso_hom_fst (n : ℕ) :
    TopPair.Hom.fst (sigmaCellFibrationPairIso p C n).hom =
      _root_.TopCat.ofHom (sigmaCellFibrationHomeomorph p C n : C(_, _)) :=
  (rfl)

omit [T2Space B] in
lemma coe_cellFibrationFiberHomeomorph_apply (n : ℕ) (j : cell C n)
    (x : (cellFibration p C n j ⁻¹' {x | (x : ULift.{u} (Fin n → ℝ)) = 0})) :
    (cellFibrationFiberHomeomorph p C n j x : E) = x.1.1.2 :=
  (rfl)

variable (p C) in
/-- **The projection to `E`** `(y, e) ↦ e` from the pullback of `p` to the disk of the `n`-cell
`j`, as a map of pairs to `(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹))`. -/
def cellFibrationPairMap (n : ℕ) (j : cell C n) :
    cellFibrationPair p C n j ⟶ preimageSkeletonPair p C n :=
  TopPair.ofHom (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.1.2,
      cellPullback_mem_preimage_skeletonLT (sigmaCellFibrationFun n ⟨j, x⟩)⟩, by fun_prop⟩)
    (_root_.TopCat.ofHom ⟨fun x ↦ ⟨x.1.1.2, cellPullback_mem_preimage_skeletonLT_of_norm_eq_one
      (x := sigmaCellFibrationFun n ⟨j, x.1⟩) (mem_sphere_zero_iff_norm.1 x.2)⟩, by fun_prop⟩)
    rfl

@[simp]
lemma coe_cellFibrationPairMap_fst_apply (n : ℕ) (j : cell C n)
    (x : (cellFibrationPair p C n j).fst) :
    (ConcreteCategory.hom (Y := _root_.TopCat.of
      (p ⁻¹' (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set B)))
      (TopPair.Hom.fst (cellFibrationPairMap p C n j)) x).1 = x.1.2 :=
  (rfl)

/-- On the summand of the `n`-cell `j`, the projection from the pullback pair over all the
`n`-cells is the projection from the pullback pair over `j`. -/
@[reassoc (attr := simp)]
lemma sigmaι_sigmaCellFibrationPairIso_hom_cellPullbackPairMap (n : ℕ) (j : cell C n) :
    TopPair.sigmaι (cellFibrationPair p C n) j ≫ (sigmaCellFibrationPairIso p C n).hom ≫
      cellPullbackPairMap p C n = cellFibrationPairMap p C n j :=
  TopPair.hom_ext_of_fst _ (by ext x; exact Subtype.ext (coe_cellPullbackPairMap_fst_apply n _))

variable (hp : serreFibrations p) (R : Type u) [Ring R]

omit [T2Space B] in
include hp in
/-- The pullback of a Serre fibration to the disk of a cell is a Serre fibration. -/
lemma mem_serreFibrations_cellFibration (n : ℕ) (j : cell C n) :
    serreFibrations (cellFibration p C n j) :=
  mem_serreFibrations_pullbackFst hp _

private lemma finrank_ulift_fin_fun (n : ℕ) : Module.finrank ℝ (ULift.{u} (Fin n → ℝ)) = n := by
  rw [finrank_ulift, Module.finrank_fin_fun]

variable (C) in
/-- The relative homology of the pullback pair over the `n`-cell `j` is the homology of the fibre
of `p` over the centre of the cell, shifted by `n`. -/
def cellFibrationPairSingularHomologyIso (n : ℕ) (j : cell C n) (q m : ℕ) (h : q + n = m) :
    (cellFibrationPair p C n j).singularHomology (ModuleCat.of R R) m ≅
      ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {map n j 0} : Set E)) :=
  singularHomologyPreimageSphereIso R (mem_serreFibrations_cellFibration hp n j) q m
      (by rw [finrank_ulift_fin_fun, h]) ≪≫
    (((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
      (ModuleCat.of R R))).mapIso (_root_.TopCat.isoOfHomeo (cellFibrationFiberHomeomorph p C n j))

variable (p C) in
/-- The relative homology of the pullback pair over the `n`-cells is the coproduct of the relative
homologies of the pullback pairs over the individual cells. -/
def cellPullbackPairSingularHomologyIso (n m : ℕ) :
    (cellPullbackPair p C n).singularHomology (ModuleCat.of R R) m ≅
      ∐ fun j ↦ (cellFibrationPair p C n j).singularHomology (ModuleCat.of R R) m :=
  (asIso (TopPair.singularHomologyMap (sigmaCellFibrationPairIso p C n).hom
    (ModuleCat.of R R) m)).symm ≪≫
    (TopPair.isColimitCofanSingularHomology (cellFibrationPair p C n) (ModuleCat.{u} R)
      (ModuleCat.of R R) m).coconePointUniqueUpToIso (colimit.isColimit _)

variable (C) in
/-- **The first page of the skeletal filtration of a Serre fibration.** For a Serre fibration
`p : E ⟶ B` and a relative CW complex `C ⊆ B` with skeleta `Xⁿ`, the relative homology
`Hₘ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R)`, for `m = q + n`, is the direct sum over the `n`-cells `j` of the
homology `H_q(p⁻¹(xⱼ); R)` of the fibre over the centre `xⱼ` of the cell. -/
def preimageSkeletonPairSingularHomologyIsoSigma (n q m : ℕ) (h : q + n = m) :
    (preimageSkeletonPair p C n).singularHomology (ModuleCat.of R R) m ≅
      ∐ fun j : cell C n ↦ ((AlgebraicTopology.singularHomologyFunctor (ModuleCat.{u} R) q).obj
        (ModuleCat.of R R)).obj (_root_.TopCat.of (p ⁻¹' {map n j 0} : Set E)) :=
  preimageSkeletonPairSingularHomologyIso C hp R n m ≪≫
    cellPullbackPairSingularHomologyIso p C R n m ≪≫
    Sigma.mapIso fun j ↦ cellFibrationPairSingularHomologyIso C hp R n j q m h

/-- On the summand of the `n`-cell `j`, the inverse of
`TauCeti.TopCat.preimageSkeletonPairSingularHomologyIsoSigma` is induced by the projection
`TauCeti.TopCat.cellFibrationPairMap` from the pullback pair over `j`, after the identification
`TauCeti.TopCat.cellFibrationPairSingularHomologyIso` of its relative homology with the homology of
the fibre. -/
@[reassoc (attr := simp)]
lemma ι_preimageSkeletonPairSingularHomologyIsoSigma_inv (n q m : ℕ) (h : q + n = m)
    (j : cell C n) :
    Sigma.ι _ j ≫ (preimageSkeletonPairSingularHomologyIsoSigma C hp R n q m h).inv =
      (cellFibrationPairSingularHomologyIso C hp R n j q m h).inv ≫
        TopPair.singularHomologyMap (cellFibrationPairMap p C n j) (ModuleCat.of R R) m := by
  simp [preimageSkeletonPairSingularHomologyIsoSigma, cellPullbackPairSingularHomologyIso,
    ← TopPair.singularHomologyMap_comp]

include hp in
/-- **The first page of the skeletal filtration of a Serre fibration vanishes below the
filtration degree**: `Hₘ(p⁻¹(Xⁿ), p⁻¹(Xⁿ⁻¹); R) = 0` for `m < n`. -/
theorem isZero_singularHomology_preimageSkeletonPair_of_lt {n m : ℕ} (hm : m < n) :
    IsZero ((preimageSkeletonPair p C n).singularHomology (ModuleCat.of R R) m) := by
  have h : IsZero ((TopPair.sigma (cellFibrationPair p C n)).singularHomology
      (ModuleCat.of R R) m) :=
    (TopPair.isColimitCofanSingularHomology _ (ModuleCat.{u} R) _ m).isZero_pt
      (Functor.isZero _ fun j ↦ isZero_singularHomology_preimage_sphere R
        (mem_serreFibrations_cellFibration hp n j.as) (by rwa [finrank_ulift_fin_fun]))
  exact h.of_iso (preimageSkeletonPairSingularHomologyIso C hp R n m ≪≫
    asIso (TopPair.singularHomologyMap (sigmaCellFibrationPairIso p C n).inv _ m))

end TopCat

end TauCeti
