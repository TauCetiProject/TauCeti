/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.LocalInverse

/-!
# Derivatives involving the local Lie logarithm

This file records first-order interactions between the local logarithm, the exponential, and
group multiplication.

## Main result

* `hasDerivAt_mulInvariantLog_mulInvariantExp_smul_mul_mulInvariantExp_smul`: the local logarithm
  of the product of two exponential lines has initial derivative `X + Y`.
-/

public section

open Function Manifold
open scoped ContDiff Manifold Topology

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [IsManifold I 1 G]

attribute [local instance] LieGroup.minSmoothnessThree

/-- The local logarithm of the product of two exponential lines has initial derivative `X + Y`. -/
theorem hasDerivAt_mulInvariantLog_mulInvariantExp_smul_mul_mulInvariantExp_smul
    [FiniteDimensional ℝ E]
    [LieGroup I ∞ G] [T2Space G] [BoundarylessManifold I G]
    (X Y : GroupLieAlgebra I G) :
    HasDerivAt
      (fun t : ℝ => (show E from mulInvariantLog (I := I) (G := G)
        (mulInvariantExp (I := I) (G := G) (t • X) *
          mulInvariantExp (I := I) (G := G) (t • Y))))
      ((show E from X) + (show E from Y)) 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hlog := hasFDerivAt_mulInvariantLogChart_one (I := I) (G := G)
  have hcurve :=
    hasFDerivAt_extChartAt_mulInvariantExp_smul_mul_mulInvariantExp_smul
      (I := I) (G := G) X Y
  have hlog' : HasFDerivAt (mulInvariantLogChart (I := I) (G := G))
      (ContinuousLinearMap.id ℝ E)
      (extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) ((0 : ℝ) • X) *
          mulInvariantExp (I := I) (G := G) ((0 : ℝ) • Y))) := by
    simpa using hlog
  have hcomp' := (hlog'.comp 0 hcurve).hasDerivAt
  rw [show (mulInvariantLogChart (I := I) (G := G) ∘
      fun t : ℝ => extChartAt I (1 : G)
        (mulInvariantExp (I := I) (G := G) (t • X) *
          mulInvariantExp (I := I) (G := G) (t • Y))) =
      fun t : ℝ => (show E from mulInvariantLog (I := I) (G := G)
        (mulInvariantExp (I := I) (G := G) (t • X) *
          mulInvariantExp (I := I) (G := G) (t • Y))) by
    funext t
    exact (mulInvariantLog_eq_chart (I := I) (G := G) _).symm] at hcomp'
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using hcomp'

end
