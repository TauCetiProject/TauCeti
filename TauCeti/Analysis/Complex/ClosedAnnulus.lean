/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# The closed annulus in the complex plane

The closed annulus `r₁ ≤ ‖z‖ ≤ r₂` centred at the origin of `ℂ`, with its membership criterion and
its compactness.

## Main declarations

* `Complex.closedAnnulus`: the closed annulus `r₁ ≤ ‖z‖ ≤ r₂`.
* `Complex.isCompact_closedAnnulus`: the closed annulus is compact.
-/

public section

open Metric

namespace Complex

/-- The closed annulus `r₁ ≤ ‖z‖ ≤ r₂` in `ℂ`. -/
noncomputable def closedAnnulus (r₁ r₂ : ℝ) : Set ℂ :=
  closedBall 0 r₂ \ ball 0 r₁

@[simp]
theorem mem_closedAnnulus {r₁ r₂ : ℝ} {z : ℂ} :
    z ∈ closedAnnulus r₁ r₂ ↔ r₁ ≤ ‖z‖ ∧ ‖z‖ ≤ r₂ := by
  simp [closedAnnulus, and_comm]

theorem isCompact_closedAnnulus (r₁ r₂ : ℝ) : IsCompact (closedAnnulus r₁ r₂) :=
  (isCompact_closedBall 0 r₂).diff isOpen_ball

instance instCompactSpaceClosedAnnulus (r₁ r₂ : ℝ) : CompactSpace (closedAnnulus r₁ r₂) :=
  isCompact_iff_compactSpace.1 (isCompact_closedAnnulus r₁ r₂)

end Complex
