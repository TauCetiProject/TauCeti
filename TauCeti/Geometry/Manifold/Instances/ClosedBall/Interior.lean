/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic

/-!
# The interior of the closed unit ball

For a real inner product space `E` of dimension `n > 0`, the closed unit ball is a manifold with
boundary modelled on `EuclideanHalfSpace n` (`TauCeti.instChartedSpaceClosedBall`). Its manifold
interior consists of the points of norm less than `1` (`TauCeti.isInteriorPoint_closedBall_iff`),
so it is homeomorphic to the open unit ball, and in particular contractible.

## Main declarations

* `TauCeti.interior_closedBall_eq_preimage_ball`: the interior of the closed unit ball is the set
  of its points lying in the open unit ball.
* `TauCeti.closedBallInteriorHomeomorph`: the interior of the closed unit ball is homeomorphic to
  the open unit ball.
* `TauCeti.contractibleSpace_interior_closedBall`: the interior of the closed unit ball is
  contractible.
-/

public section

noncomputable section

open Set Metric Module Topology

open scoped Manifold

namespace TauCeti

variable {n : ℕ} [NeZero n] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n)]

/-- The interior points of the closed unit ball are exactly its points in the open unit ball. -/
theorem interior_closedBall_eq_preimage_ball :
    (𝓡∂ n).interior (closedBall (0 : E) 1) = Subtype.val ⁻¹' ball (0 : E) 1 := by
  ext x
  simp [ModelWithCorners.interior]

variable (n E) in
/-- **The interior of the closed unit ball is the open unit ball.** -/
def closedBallInteriorHomeomorph : (𝓡∂ n).interior (closedBall (0 : E) 1) ≃ₜ ball (0 : E) 1 :=
  (Homeomorph.setCongr interior_closedBall_eq_preimage_ball).trans
    (IsEmbedding.subtypeVal.homeomorphOfSubsetRange (by
      rw [Subtype.range_coe]
      exact ball_subset_closedBall))

@[simp]
theorem coe_closedBallInteriorHomeomorph_apply (x : (𝓡∂ n).interior (closedBall (0 : E) 1)) :
    (closedBallInteriorHomeomorph n E x : E) = x.val :=
  (rfl)

@[simp]
theorem coe_closedBallInteriorHomeomorph_symm_apply (y : ball (0 : E) 1) :
    (((closedBallInteriorHomeomorph n E).symm y).val : E) = y := by
  conv_rhs => rw [← (closedBallInteriorHomeomorph n E).apply_symm_apply y]
  rw [coe_closedBallInteriorHomeomorph_apply]

/-- The interior of the closed unit ball is contractible. -/
instance contractibleSpace_interior_closedBall :
    ContractibleSpace ((𝓡∂ n).interior (closedBall (0 : E) 1)) :=
  have : ContractibleSpace (ball (0 : E) 1) := contractibleSpace_ball zero_lt_one
  (closedBallInteriorHomeomorph n E).contractibleSpace

end TauCeti
