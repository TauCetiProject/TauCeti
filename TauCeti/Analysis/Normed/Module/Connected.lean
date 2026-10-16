/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
public import Mathlib.Analysis.Normed.Module.Connected

/-!
# Connectedness of punctured balls

In a real normed space of dimension greater than one, removing the centre from an open ball of
positive radius leaves a path-connected set. This is the local form of Mathlib's
`isPathConnected_compl_singleton_of_one_lt_rank`, to which it reduces through the homeomorphism
`OpenPartialHomeomorph.univBall` of the whole space onto the ball, sending `0` to the centre. It is
the local input for showing that removing a discrete set from a connected manifold of dimension
greater than one keeps it connected.

## Main declarations

* `TauCeti.isPathConnected_ball_sdiff_singleton`, `TauCeti.isConnected_ball_sdiff_singleton`: a
  punctured open ball is path connected, hence connected.
-/

public section

open Metric Set

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- In a real normed space of dimension greater than one, an open ball of positive radius with its
centre removed is path connected. -/
theorem isPathConnected_ball_sdiff_singleton (h : 1 < Module.rank ℝ E) (x : E) {r : ℝ}
    (hr : 0 < r) : IsPathConnected (ball x r \ {x}) := by
  set e := OpenPartialHomeomorph.univBall x r
  have he : Function.Injective e :=
    injOn_univ.1 (OpenPartialHomeomorph.univBall_source x r ▸ e.injOn)
  have himage : e '' {0}ᶜ = ball x r \ {x} := by
    rw [compl_eq_univ_sdiff, image_sdiff he, ← OpenPartialHomeomorph.univBall_source x r,
      e.image_source_eq_target, OpenPartialHomeomorph.univBall_target x hr, image_singleton,
      OpenPartialHomeomorph.univBall_apply_zero]
  exact himage ▸ (isPathConnected_compl_singleton_of_one_lt_rank h 0).image
    (OpenPartialHomeomorph.continuous_univBall x r)

/-- In a real normed space of dimension greater than one, an open ball of positive radius with its
centre removed is connected. -/
theorem isConnected_ball_sdiff_singleton (h : 1 < Module.rank ℝ E) (x : E) {r : ℝ}
    (hr : 0 < r) : IsConnected (ball x r \ {x}) :=
  (isPathConnected_ball_sdiff_singleton h x hr).isConnected

end TauCeti
