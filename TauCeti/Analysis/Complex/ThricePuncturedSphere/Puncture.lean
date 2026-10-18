/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.PuncturedNeighborhoods
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Analytic inverse coordinates at the punctures

The inverse standard coordinate of a puncture is complex differentiable away from the origin.
-/

public section

namespace TauCeti.ThricePuncturedSphere.Puncture

/-- The inverse puncture coordinate is complex differentiable at every nonzero point. -/
theorem differentiableAt_coordInv (q : Puncture) {w : ℂ} (hw : w ≠ 0) :
    DifferentiableAt ℂ (coordInv q) w := by
  cases q
  · rw [coordInv_zero]
    exact differentiableAt_id.div_const 2
  · rw [coordInv_one]
    exact (differentiableAt_id.div_const 2).const_sub 1
  · rw [coordInv_inf]
    exact (differentiableAt_const 2).div differentiableAt_id hw

end TauCeti.ThricePuncturedSphere.Puncture
