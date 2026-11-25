/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# The closure and frontier of a punctured ball

In a nontrivial real normed space, removing the centre from the open ball `ball c r`, `0 < r`,
does not change its closure, the closed ball `closedBall c r`
(`TauCeti.closure_ball_sdiff_singleton`), but adds the centre to its frontier, which becomes
`sphere c r ∪ {c}` (`TauCeti.frontier_ball_sdiff_singleton`).
-/

public section

open Metric Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

/-- In a nontrivial real normed space, the closure of the punctured ball `ball c r \ {c}`,
`r ≠ 0`, is the closed ball `closedBall c r`. -/
theorem closure_ball_sdiff_singleton (c : E) {r : ℝ} (hr : r ≠ 0) :
    closure (ball c r \ {c}) = closedBall c r := by
  refine (closure_mono sdiff_subset).trans_eq (closure_ball c hr) |>.antisymm ?_
  rw [← closure_ball c hr, sdiff_eq]
  exact closure_minimal ((dense_compl_singleton c).open_subset_closure_inter isOpen_ball)
    isClosed_closure

/-- **The frontier of a punctured ball.** In a nontrivial real normed space, the frontier of the
punctured ball `ball c r \ {c}`, `0 < r`, is the sphere `sphere c r` together with the centre. -/
theorem frontier_ball_sdiff_singleton (c : E) {r : ℝ} (hr : 0 < r) :
    frontier (ball c r \ {c}) = sphere c r ∪ {c} := by
  rw [frontier, closure_ball_sdiff_singleton c hr.ne',
    (isOpen_ball.sdiff isClosed_singleton).interior_eq, sdiff_sdiff_right, closedBall_sdiff_ball,
    inter_eq_right.2 (by simpa using hr.le)]

end TauCeti
