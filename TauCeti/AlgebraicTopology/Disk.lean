/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Category.TopCat.Sphere
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Contractibility of the Euclidean disk

The closed Euclidean disk is a closed ball in a finite-dimensional real normed space.  This
file records the contractibility of the `TopCat` carrier, which is the absolute-space input for
the later relative calculation for a disk and its boundary.
-/

@[expose] public section

noncomputable section

namespace TauCeti.TopCat

/-- The `n`-dimensional Euclidean disk is contractible. -/
theorem contractibleSpace_disk (n : ℕ) :
    ContractibleSpace (TopCat.disk n) := by
  change ContractibleSpace (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1))
  let hX : ContractibleSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) :=
    Metric.contractibleSpace_closedBall (x := 0) (r := 1) (by norm_num)
  have h : (ULift (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) ≃ₜ
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 := Homeomorph.ulift
  exact h.contractibleSpace_iff.mpr hX

end TauCeti.TopCat
end
