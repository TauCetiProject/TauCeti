/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ClosedAnnulus
public import TauCeti.Topology.CWComplex.Classical.Circle
public import TauCeti.Topology.CWComplex.Classical.ClosedBall
public import TauCeti.Topology.CWComplex.Classical.Product

/-!
# Closed annuli have finite CW type

The closed annulus `r₁ ≤ ‖z‖ ≤ r₂` in `ℂ` with `0 < r₁` is homeomorphic to `Circle × [r₁, r₂]`
by polar coordinates (`Complex.closedAnnulusHomeomorph`), and for `r₁ ≤ 0` it is the closed ball
of radius `r₂`, so closed annuli have finite CW type for all radii.

## Main declarations

* `TauCeti.finiteCWType_closedAnnulus`: every closed annulus in `ℂ` has finite CW type.
-/

public section

open Complex Metric

namespace TauCeti

/-- A closed annulus in `ℂ` has finite CW type: for `0 < r₁` it is homeomorphic to
`Circle × [r₁, r₂]`, and for `r₁ ≤ 0` it is the closed ball of radius `r₂`. -/
instance finiteCWType_closedAnnulus (r₁ r₂ : ℝ) : FiniteCWType (closedAnnulus r₁ r₂) := by
  rcases le_or_gt r₁ 0 with h₀ | h₀
  · have : closedAnnulus r₁ r₂ = closedBall 0 r₂ := by
      ext z
      rw [mem_closedAnnulus, mem_closedBall_zero_iff]
      exact ⟨And.right, fun h ↦ ⟨h₀.trans (norm_nonneg _), h⟩⟩
    rw [this]
    infer_instance
  · exact (closedAnnulusHomeomorph h₀).finiteCWType

end TauCeti
