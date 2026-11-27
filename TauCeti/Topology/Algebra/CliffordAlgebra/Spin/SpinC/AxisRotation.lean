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
topology of a subgroup of the orthogonal group of `ℝ³`, with the operator norm topology. Their
angle `TauCeti.axisRotationAngle`, the unit complex number `a + b i` with `g e₁ = a e₁ + b e₂`, is
continuous (`TauCeti.continuous_axisRotationAngle`), and so is the lift
`TauCeti.axisSpinCLift : SO(2) → Spinᶜ(3)` (`TauCeti.continuous_axisSpinCLift`), which is the
continuous plane lift `CliffordAlgebra.spinCCircle` composed with the angle. Continuity is what
lets the lift change the structure group of the principal `SO(2)`-bundle of frames adapted to a
unit vector field on an oriented three-dimensional bundle.

## Main results

* `TauCeti.continuous_axisRotationAngle`: the angle of a rotation about the first axis is
  continuous.
* `TauCeti.continuous_axisSpinCLift`: the `Spinᶜ` lift of the rotations about the first axis is
  continuous.
-/

public section

noncomputable section

open CliffordAlgebra

namespace TauCeti

/-- **The angle of a rotation about the first axis is continuous**: its real and imaginary parts
are coordinates of `g e₁`. -/
theorem continuous_axisRotationAngle : Continuous axisRotationAngle := by
  have hre : Continuous fun g : axisRotationGroup ↦ (axisRotationAngle g : ℂ).re := by
    simp only [re_axisRotationAngle]
    fun_prop
  have him : Continuous fun g : axisRotationGroup ↦ (axisRotationAngle g : ℂ).im := by
    simp only [im_axisRotationAngle]
    fun_prop
  have hc : Continuous fun g : axisRotationGroup ↦ (axisRotationAngle g : ℂ) :=
    (Complex.equivRealProdCLM.symm.continuous.comp (hre.prodMk him)).congr fun g ↦
      Complex.ext (by simp) (by simp)
  exact continuous_induced_rng.2 hc

/-- **The `Spinᶜ` lift of the rotations about the first axis is continuous.** -/
theorem continuous_axisSpinCLift : Continuous axisSpinCLift := by
  rw [axisSpinCLift_eq_comp]
  exact (continuous_spinCCircle _ _ _).comp continuous_axisRotationAngle

end TauCeti
