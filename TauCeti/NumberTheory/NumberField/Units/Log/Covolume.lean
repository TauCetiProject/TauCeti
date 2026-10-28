/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Units.Log.Hyperplane
public import TauCeti.Algebra.Module.ZLattice.Covolume
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.NumberTheory.NumberField.Units.Regulator

/-!
# Euclidean covolume of the full weighted logarithmic unit lattice

The full weighted logarithms lie in the sum-zero hyperplane in Euclidean space on the
infinite places. Its induced Euclidean volume differs from the product measure in Mathlib's
coordinates omitting one place: the factor is the square root of the number of infinite
places. Consequently the Euclidean covolume of the full unit lattice is
`sqrt (rank K + 1) * NumberField.Units.regulator K`.

The logarithms retain Mathlib's weights: one at a real place and two at a complex place.
The factor comes from the coordinate hyperplane, with no further change of these weights.
-/

public noncomputable section

open MeasureTheory Module NumberField NumberField.Units
open NumberField.Units.dirichletUnitTheorem
open scoped NumberField

namespace TauCeti

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- The sum-zero logarithmic hyperplane with the inner product induced from Euclidean space
on all infinite places. -/
abbrev euclideanLogSpace : Submodule ℝ (EuclideanSpace ℝ (InfinitePlace K)) :=
  (singleParityCheckCode ℝ (InfinitePlace K)).comap
    (EuclideanSpace.equiv (InfinitePlace K) ℝ).toLinearMap

open Classical in
/-- The Euclidean logarithmic hyperplane has the same vectors as the full logarithmic
hyperplane with its finite-product norm. -/
def euclideanLogSpaceEquiv : euclideanLogSpace K ≃ₗ[ℝ]
    singleParityCheckCode ℝ (InfinitePlace K) where
  toFun x := ⟨EuclideanSpace.equiv (InfinitePlace K) ℝ x, x.property⟩
  invFun x := ⟨(EuclideanSpace.equiv (InfinitePlace K) ℝ).symm x, by
    change (EuclideanSpace.equiv (InfinitePlace K) ℝ)
      ((EuclideanSpace.equiv (InfinitePlace K) ℝ).symm x.val) ∈
        singleParityCheckCode ℝ (InfinitePlace K)
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using x.property⟩
  left_inv x := by ext w; rfl
  right_inv x := by ext w; rfl
  map_add' x y := rfl
  map_smul' a x := rfl

open Classical in
/-- The identification of logarithmic hyperplanes preserves every coordinate. -/
@[simp] theorem euclideanLogSpaceEquiv_apply (x : euclideanLogSpace K) (w : InfinitePlace K) :
    (euclideanLogSpaceEquiv K x).val w = x.val w := by rfl

open Classical in
/-- Coordinates on the Euclidean logarithmic hyperplane obtained by omitting Mathlib's
distinguished infinite place. -/
def euclideanLogCoordinates : euclideanLogSpace K ≃L[ℝ] logSpace K :=
  ((euclideanLogSpaceEquiv K).trans (unitLogCoordinates K)).toContinuousLinearEquiv

open Classical in
/-- The full weighted logarithmic unit lattice, with the induced Euclidean metric. -/
def euclideanUnitLattice : Submodule ℤ (euclideanLogSpace K) :=
  ZLattice.comap ℝ (E := logSpace K) (F := euclideanLogSpace K)
    (unitLattice K) (euclideanLogCoordinates K).toLinearMap

open Classical in
instance discreteTopology_euclideanUnitLattice : DiscreteTopology (euclideanUnitLattice K) := by
  unfold euclideanUnitLattice
  infer_instance

open Classical in
instance isZLattice_euclideanUnitLattice : IsZLattice ℝ (euclideanUnitLattice K) := by
  unfold euclideanUnitLattice
  infer_instance

open Classical in
/-- The Euclidean lattice consists exactly of the full weighted logarithmic unit vectors. -/
theorem mem_euclideanUnitLattice (x : euclideanLogSpace K) :
    x ∈ euclideanUnitLattice K ↔
      euclideanLogSpaceEquiv K x ∈ fullUnitLattice K := by
  rw [fullUnitLattice_eq_comap]
  rfl

open Classical in
/-- The coordinate basis of the Euclidean logarithmic hyperplane: each vector is one at its
indexed place, minus one at the omitted place, and zero elsewhere. -/
def euclideanLogBasis : Basis {w : InfinitePlace K // w ≠ w₀} ℝ (euclideanLogSpace K) :=
  (Pi.basisFun ℝ _).map (euclideanLogCoordinates K).symm.toLinearEquiv

open Classical in
/-- Restoring a deleted coordinate gives the standard sum-zero extension. -/
theorem euclideanLogCoordinates_symm_apply (y : logSpace K) (w : InfinitePlace K) :
    ((euclideanLogCoordinates K).symm y).val w =
      NumberField.Units.logSpaceExtend K y w := by
  simpa [euclideanLogCoordinates, euclideanLogSpaceEquiv] using
    unitLogCoordinates_symm_apply K y w

open Classical in
/-- The Gram matrix of the deleted-coordinate basis is the identity plus the all-ones
matrix. This is the source of the Euclidean normalization factor. -/
theorem gram_euclideanLogBasis :
    Matrix.gram ℝ (euclideanLogBasis K) =
      1 + Matrix.of (fun _ _ : {w : InfinitePlace K // w ≠ w₀} ↦ (1 : ℝ)) := by
  ext i j
  rw [Matrix.gram_apply, Submodule.coe_inner, PiLp.inner_apply,
    Fintype.sum_eq_add_sum_subtype_ne _ w₀]
  simp [euclideanLogBasis, euclideanLogCoordinates_symm_apply, Pi.basisFun_apply,
    NumberField.Units.logSpaceExtend_apply_w₀,
    NumberField.Units.logSpaceExtend_apply_val, Matrix.one_apply, eq_comm, Pi.single_apply,
    add_comm]

open Classical in
/-- The squared Euclidean volume of the coordinate parallelepiped is the number of infinite
places. -/
theorem det_gram_euclideanLogBasis :
    (Matrix.gram ℝ (euclideanLogBasis K)).det = rank K + 1 := by
  rw [gram_euclideanLogBasis]
  have h := Matrix.det_one_add_replicateCol_mul_replicateRow
    (ι := Unit) (fun _ : {w : InfinitePlace K // w ≠ w₀} ↦ (1 : ℝ)) (fun _ ↦ 1)
  have hm : (Matrix.replicateCol Unit fun _ : {w : InfinitePlace K // w ≠ w₀} ↦ (1 : ℝ)) *
      Matrix.replicateRow Unit (fun _ : {w : InfinitePlace K // w ≠ w₀} ↦ (1 : ℝ)) =
        Matrix.of (fun _ _ ↦ (1 : ℝ)) := by
    ext i j
    simp [Matrix.mul_apply]
  simpa [hm, dotProduct, NumberField.Units.rank, add_comm] using h

open Classical in
/-- The coordinate parallelepiped has Euclidean volume `sqrt (rank K + 1)`. -/
theorem volume_real_fundamentalDomain_euclideanLogBasis :
    volume.real (ZSpan.fundamentalDomain (euclideanLogBasis K)) =
      Real.sqrt (rank K + 1) := by
  have hs := (euclideanLogBasis K).volume_real_fundamentalDomain_sq_eq_det_gram
  rw [det_gram_euclideanLogBasis] at hs
  nlinarith [measureReal_nonneg (μ := volume)
    (s := ZSpan.fundamentalDomain (euclideanLogBasis K)),
    Real.sqrt_nonneg (rank K + 1), Real.sq_sqrt (by positivity : (0 : ℝ) ≤ rank K + 1)]

open Classical in
/-- **Full-logarithm covolume normalization.** The covolume of the full weighted logarithmic
unit lattice for the induced Euclidean volume on the sum-zero hyperplane is
`sqrt (rank K + 1) * regulator K`. In rank zero the factor is one. -/
theorem covolume_euclideanUnitLattice :
    ZLattice.covolume (euclideanUnitLattice K) =
      Real.sqrt (rank K + 1) * regulator K := by
  change ZLattice.covolume (ZLattice.comap ℝ (E := logSpace K) (F := euclideanLogSpace K)
    (unitLattice K) (euclideanLogCoordinates K).toLinearMap) = _
  let b := (basisUnitLattice K).reindex (equivFinRank K)
  let c := b.ofZLatticeComap ℝ (unitLattice K) (euclideanLogCoordinates K).toLinearEquiv
  rw [ZLattice.covolume_eq_det_mul_measureReal _ volume c
    (euclideanLogBasis K), volume_real_fundamentalDomain_euclideanLogBasis]
  have hdet : |(euclideanLogBasis K).det ((↑) ∘ c)| = regulator K := by
    rw [regulator_eq_det', Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    congr 1
    ext i j
    simp [Basis.toMatrix_apply, euclideanLogBasis, c, b, Basis.ofZLatticeComap_apply,
      ← logEmbedding_fundSystem]
  rw [hdet, mul_comm]

open Classical in
/-- The induced Euclidean volume on the existing full logarithmic hyperplane. This is the
pushforward of subspace volume from its coordinate-preserving Euclidean realization. -/
def fullLogEuclideanVolume : Measure (singleParityCheckCode ℝ (InfinitePlace K)) :=
  volume.map (euclideanLogSpaceEquiv K)

open Classical in
instance isAddHaarMeasure_fullLogEuclideanVolume :
    (fullLogEuclideanVolume K).IsAddHaarMeasure := by
  unfold fullLogEuclideanVolume
  infer_instance

open Classical in
/-- **Full weighted unit-log lattice versus the canonical regulator.** For the induced
Euclidean Haar measure, the covolume of the existing full logarithmic unit lattice is
`sqrt (rank K + 1) * regulator K`. -/
theorem covolume_fullUnitLattice_fullLogEuclideanVolume :
    ZLattice.covolume (fullUnitLattice K) (fullLogEuclideanVolume K) =
      Real.sqrt (rank K + 1) * regulator K := by
  have he : MeasurePreserving (euclideanLogSpaceEquiv K).toContinuousLinearEquiv
      volume (fullLogEuclideanVolume K) :=
    ⟨(euclideanLogSpaceEquiv K).toContinuousLinearEquiv.continuous.measurable, rfl⟩
  have hL : ZLattice.comap ℝ (fullUnitLattice K)
      (euclideanLogSpaceEquiv K).toContinuousLinearEquiv.toLinearMap =
        euclideanUnitLattice K := by
    ext x
    exact (mem_euclideanUnitLattice K x).symm
  rw [← ZLattice.covolume_comap (fullUnitLattice K) (fullLogEuclideanVolume K) volume he, hL]
  exact covolume_euclideanUnitLattice K

end TauCeti
