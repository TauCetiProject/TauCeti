/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Inclusions of finite-radius balls, spheres, and annuli into extended-radius balls

In a pseudometric space, open balls `Metric.eball c R` with extended radius `R : ℝ≥0∞` unify
finite-radius open balls (`R = ENNReal.ofReal R₀`) with the whole space (`R = ⊤`). This file
records set inclusions of finite-radius closed balls, spheres, and closed concentric annuli
`Metric.closedBall c R' \ Metric.ball c r'` into `Metric.eball c R` and open concentric annuli
`Metric.eball c R \ Metric.closedBall c r` when `ENNReal.ofReal R' < R`.
-/

public section

open Metric Set
open scoped ENNReal

namespace TauCeti

variable {α : Type*} [PseudoMetricSpace α] {c : α}

/-- If `ENNReal.ofReal r < R`, the closed ball `Metric.closedBall c r` is contained in the open
extended-radius ball `Metric.eball c R`. -/
theorem closedBall_subset_eball {r : ℝ} {R : ℝ≥0∞} (h : ENNReal.ofReal r < R) :
    closedBall c r ⊆ eball c R :=
  fun z hz => (edist_dist z c ▸ ENNReal.ofReal_le_ofReal hz).trans_lt h

/-- If `ENNReal.ofReal r < R`, the sphere `Metric.sphere c r` is contained in the open
extended-radius ball `Metric.eball c R`. -/
theorem sphere_subset_eball {r : ℝ} {R : ℝ≥0∞} (h : ENNReal.ofReal r < R) :
    sphere c r ⊆ eball c R :=
  sphere_subset_closedBall.trans (closedBall_subset_eball h)

/-- If `r < r'` and `ENNReal.ofReal R' < R`, the closed concentric annulus
`Metric.closedBall c R' \ Metric.ball c r'` is contained in the open concentric annulus
`Metric.eball c R \ Metric.closedBall c r`. -/
theorem closedBall_sdiff_ball_subset_eball_sdiff_closedBall {r r' R' : ℝ} {R : ℝ≥0∞}
    (hrr' : r < r') (hR'R : ENNReal.ofReal R' < R) :
    closedBall c R' \ ball c r' ⊆ eball c R \ closedBall c r :=
  sdiff_subset_sdiff (closedBall_subset_eball hR'R) (closedBall_subset_ball hrr')

/-- Any sphere of radius `ρ` with `r < ρ` and `ENNReal.ofReal ρ < R` lies inside the open
concentric annulus `Metric.eball c R \ Metric.closedBall c r`. -/
theorem sphere_subset_eball_sdiff_closedBall {r ρ : ℝ} {R : ℝ≥0∞}
    (hrρ : r < ρ) (hρR : ENNReal.ofReal ρ < R) :
    sphere c ρ ⊆ eball c R \ closedBall c r :=
  closedBall_sdiff_ball.symm.trans_subset
    (closedBall_sdiff_ball_subset_eball_sdiff_closedBall hrρ hρR)

end TauCeti
