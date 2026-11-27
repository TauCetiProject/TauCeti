/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinC.AxisRotation
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.CircleLift

/-!
# Continuity of the `Spinᶜ` lift of the rotations about an axis

The rotations of `ℝ³` about the first coordinate axis, `TauCeti.axisRotationGroup`, carry the
topology of a subgroup of the orthogonal group of `ℝ³`, with the operator norm topology. The lift
`TauCeti.axisSpinCLift : SO(2) → Spinᶜ(3)` is continuous (`TauCeti.continuous_axisSpinCLift`):
it is the continuous plane lift `CliffordAlgebra.spinCCircle` composed with the angle
`TauCeti.axisRotationAngle`, which is continuous (`TauCeti.continuous_axisRotationAngle`).
Continuity is what lets the lift change the structure group of the principal `SO(2)`-bundle of
frames adapted to a unit vector field on an oriented three-dimensional bundle.

## Main results

* `TauCeti.continuous_axisSpinCLift`: the `Spinᶜ` lift of the rotations about the first axis is
  continuous.
-/

public section

noncomputable section

open CliffordAlgebra

namespace TauCeti

/-- **The `Spinᶜ` lift of the rotations about the first axis is continuous.** -/
@[fun_prop]
theorem continuous_axisSpinCLift : Continuous axisSpinCLift := by
  rw [axisSpinCLift_eq_comp]
  exact (continuous_spinCCircle _ _ _).comp continuous_axisRotationAngle

end TauCeti
