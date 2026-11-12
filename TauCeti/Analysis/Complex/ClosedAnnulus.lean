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
* `Complex.closedAnnulus.le_norm_coe` and `Complex.closedAnnulus.norm_coe_le`: the norm bounds of
  a point of the closed annulus.
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

/-- A point of the closed annulus has norm at least `r₁`. -/
theorem closedAnnulus.le_norm_coe {r₁ r₂ : ℝ} (z : closedAnnulus r₁ r₂) : r₁ ≤ ‖(z : ℂ)‖ :=
  (mem_closedAnnulus.1 z.2).1

/-- A point of the closed annulus has norm at most `r₂`. -/
theorem closedAnnulus.norm_coe_le {r₁ r₂ : ℝ} (z : closedAnnulus r₁ r₂) : ‖(z : ℂ)‖ ≤ r₂ :=
  (mem_closedAnnulus.1 z.2).2

theorem isCompact_closedAnnulus (r₁ r₂ : ℝ) : IsCompact (closedAnnulus r₁ r₂) :=
  (isCompact_closedBall 0 r₂).diff isOpen_ball

instance instCompactSpaceClosedAnnulus (r₁ r₂ : ℝ) : CompactSpace (closedAnnulus r₁ r₂) :=
  isCompact_iff_compactSpace.1 (isCompact_closedAnnulus r₁ r₂)

end Complex
