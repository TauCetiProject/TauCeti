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
  -- `TopCat.disk` stores its metric closed ball inside a `ULift`; expose that carrier so the
  -- closed-ball contractibility instance can be transported through the lift equivalence.
  change ContractibleSpace (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
  let hX : ContractibleSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    Metric.contractibleSpace_closedBall (x := 0) (r := 1) (by norm_num)
  have h : (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := Homeomorph.ulift
  exact h.contractibleSpace_iff.mpr hX

/-- The boundary of the `n`-dimensional disk is path-connected when `n ≥ 2`. -/
lemma pathConnectedSpace_diskBoundary {n : ℕ} (hn : 2 ≤ n) :
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

namespace TauCeti

/-- The standard pair consisting of the `n`-dimensional disk and its boundary, used to express
relative singular homology of the disk with respect to its boundary. -/
abbrev diskBoundaryPair (n : ℕ) : TopPair.{u} :=
  TopPair.of (TopCat.diskBoundaryInclusion n) (by
    let hT2 : T2Space (TopCat.disk n) := by
      -- Typeclass synthesis does not unfold the `TopCat.disk` wrapper, whose carrier is the
      -- lifted closed ball.
      change T2Space (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
      infer_instance
    exact
      (((ConcreteCategory.hom (TopCat.diskBoundaryInclusion n)).continuous_toFun).isClosedEmbedding
        ((TopCat.mono_iff_injective _).mp
          (inferInstance : Mono (TopCat.diskBoundaryInclusion n)))).isEmbedding)

@[simp]
lemma diskBoundaryPair_fst (n : ℕ) :
    (diskBoundaryPair n).fst = TopCat.disk n := rfl

@[simp]
lemma diskBoundaryPair_snd (n : ℕ) :
    (diskBoundaryPair n).snd = TopCat.diskBoundary n := rfl

/-- The underlying map of `diskBoundaryPair n` is the standard boundary inclusion. -/
-- This equation is definitional for the reducible abbreviation; an `@[simp]` attribute would be
-- rejected by `simpNF` as a duplicate rule.
lemma diskBoundaryPair_map (n : ℕ) :
    (diskBoundaryPair n).map = TopCat.diskBoundaryInclusion n := (rfl)

end TauCeti
end
