/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Order intervals and norm balls in C⋆-algebras

In a unital ordered C⋆-algebra `A`, for any nonnegative radius `r : ℝ`, the positive operators in
`closedBall 0 r` form the order interval `Set.Icc 0 (algebraMap ℝ A r)`
(`CStarAlgebra.Ici_zero_inter_closedBall_zero_eq_Icc`).
-/

public section

namespace CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- In a unital ordered C⋆-algebra `A`, for `0 ≤ r`, the positive elements of norm at most `r`
form the order interval `Set.Icc 0 (algebraMap ℝ A r)`. -/
theorem Ici_zero_inter_closedBall_zero_eq_Icc {r : ℝ} (hr : 0 ≤ r) :
    Set.Ici (0 : A) ∩ Metric.closedBall 0 r = Set.Icc 0 (algebraMap ℝ A r) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ici, Metric.mem_closedBall, dist_zero_right,
    mem_Icc_algebraMap_iff_norm_le hr]

end CStarAlgebra
