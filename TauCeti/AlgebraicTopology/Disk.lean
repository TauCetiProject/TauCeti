/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.Category.TopPair
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Euclidean disks and their boundaries

The closed Euclidean disk is contractible, and its boundary is path-connected when the disk has
dimension at least two.  This module also constructs the standard `TopPair` consisting of a disk
and its boundary, providing the topological input for relative-homology calculations.
-/

public section

noncomputable section
open CategoryTheory
universe u

namespace TauCeti.TopCat

/-- The `n`-dimensional Euclidean disk is contractible. -/
instance contractibleSpace_disk (n : ℕ) :
    ContractibleSpace (TopCat.disk n) := by
  change ContractibleSpace (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
  let hX : ContractibleSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    Metric.contractibleSpace_closedBall (x := 0) (r := 1) (by norm_num)
  have h : (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := Homeomorph.ulift
  exact h.contractibleSpace_iff.mpr hX

/-- The boundary of the `n`-dimensional disk is path-connected when `n ≥ 2`. -/
lemma diskBoundary_isPathConnected {n : ℕ} (hn : 2 ≤ n) :
    PathConnectedSpace (TopCat.diskBoundary n) := by
  -- The `TopCat` carrier is the lift of the metric sphere.
  change PathConnectedSpace (ULift (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1))
  let _ : PathConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    isPathConnected_iff_pathConnectedSpace.mp
      (isPathConnected_sphere
        (E := EuclideanSpace ℝ (Fin n))
        (by
          rw [← Module.finrank_eq_rank]
          norm_num [finrank_euclideanSpace_fin]
          omega)
        0 (by norm_num))
  exact Homeomorph.ulift.symm.pathConnectedSpace

end TauCeti.TopCat

namespace TopPair

/-- The standard pair consisting of the `n`-dimensional disk and its boundary.  The abbreviation
keeps the component spaces reducible for the projection lemma below. -/
abbrev diskBoundaryPair (n : ℕ) : TopPair.{u} :=
  TopPair.of (TopCat.diskBoundaryInclusion n) (by
    let hT2 : T2Space (TopCat.disk n) := by
      change T2Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
      infer_instance
    exact
      (((ConcreteCategory.hom (TopCat.diskBoundaryInclusion n)).continuous_toFun).isClosedEmbedding
        ((TopCat.mono_iff_injective _).mp
          (inferInstance : Mono (TopCat.diskBoundaryInclusion n)))).isEmbedding)

/-- The underlying map of `diskBoundaryPair n` is the standard boundary inclusion. -/
@[simp]
lemma diskBoundaryPair_map (n : ℕ) :
    (diskBoundaryPair n).map = TopCat.diskBoundaryInclusion n := (rfl)

end TopPair
end
