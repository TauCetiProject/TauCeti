/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Sets.Opens
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# The open unit ball as an open subset

The open unit ball `Metric.ball 0 1` of a normed space `F`, bundled as an element of
`TopologicalSpace.Opens F` (`TauCeti.unitBallOpens`), so that it can serve as the domain of
function spaces indexed by open sets. For a real normed space it is convex, and its closure is the
closed unit ball.

## Main declarations

* `TauCeti.unitBallOpens`: the open unit ball, as an open subset.
* `TauCeti.convex_unitBallOpens`, `TauCeti.closure_unitBallOpens`: in a real normed space it is
  convex, with closure the closed unit ball.
-/

public section

open Metric TopologicalSpace

namespace TauCeti

variable (F : Type*) [NormedAddCommGroup F]

/-- The open unit ball of a normed space, as an open subset. -/
def unitBallOpens : Opens F :=
  ⟨ball 0 1, isOpen_ball⟩

/-- The open unit ball, as a set. -/
@[simp]
theorem coe_unitBallOpens : (unitBallOpens F : Set F) = ball 0 1 := by
  rw [unitBallOpens, Opens.coe_mk]

variable {F} in
/-- A point lies in the open unit ball exactly when its norm is less than `1`. -/
@[simp]
theorem mem_unitBallOpens {v : F} : v ∈ unitBallOpens F ↔ ‖v‖ < 1 := by
  rw [← SetLike.mem_coe, coe_unitBallOpens, mem_ball_zero_iff]

variable {F} in
/-- A point lies in the open unit ball, as an open subset, exactly when it lies in `ball 0 1`. -/
theorem mem_unitBallOpens_iff_mem_ball {v : F} : v ∈ unitBallOpens F ↔ v ∈ ball 0 1 := by
  rw [← SetLike.mem_coe, coe_unitBallOpens]

/-- The centre of the open unit ball. -/
theorem zero_mem_unitBallOpens : (0 : F) ∈ unitBallOpens F :=
  mem_unitBallOpens.2 (by simp)

variable [NormedSpace ℝ F]

/-- The open unit ball of a real normed space is convex. -/
theorem convex_unitBallOpens : Convex ℝ (unitBallOpens F : Set F) := by
  rw [coe_unitBallOpens]
  exact convex_ball 0 1

/-- The closure of the open unit ball of a real normed space is the closed unit ball. -/
theorem closure_unitBallOpens : closure (unitBallOpens F : Set F) = closedBall 0 1 := by
  rw [coe_unitBallOpens, closure_ball 0 one_ne_zero]

end TauCeti
