/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.CircleLift
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.Rotation
public import TauCeti.Topology.Algebra.CliffordAlgebra.Spin.SpinC.Basic
import TauCeti.Analysis.Complex.Circle.Basic

/-!
# Continuity of the `Spinᶜ` lift of the rotations of a plane

For orthogonal vectors `u, w` with `Q u * Q w = 1`, the `Spinᶜ` lift
`CliffordAlgebra.spinCCircle : U(1) → Spinᶜ(Q)` of the rotations of the plane of `u` and `w` is
continuous for the quotient topology of `Spinᶜ(Q)` (`CliffordAlgebra.continuous_spinCCircle`). It
is defined by descending `y ↦ [Re y + Im y ι u ι w, y]` along the squaring map `y ↦ y²` of the
circle, and that map is a quotient map: a continuous surjection from the compact circle onto the
Hausdorff circle. So its continuity follows from that of the circle subgroup
`CliffordAlgebra.spinCircle` of `Spin(Q)` (`CliffordAlgebra.continuous_spinCircle`) and of the
quotient map `Spin(Q) × U(1) → Spinᶜ(Q)`. Continuity is what lets the lift change the structure
group of a principal circle bundle, such as the bundle of frames adapted to an oriented plane
field.

## Main results

* `CliffordAlgebra.continuous_spinCCircle`: the `Spinᶜ` lift of the rotations of a plane is
  continuous.
-/

public section

noncomputable section

namespace CliffordAlgebra

open TauCeti

variable {M : Type*} [AddCommGroup M] [Module ℝ M] {Q : QuadraticForm ℝ M} (hQ : Q ≠ 0)
  {u w : M} (huw : Q.IsOrtho u w) (h : Q u * Q w = 1)

/-- **The `Spinᶜ` lift of the rotations of a plane is continuous.** It descends
`y ↦ [Re y + Im y ι u ι w, y]` along the squaring map of the circle, which is a quotient map. -/
@[fun_prop]
theorem continuous_spinCCircle : Continuous (spinCCircle Q hQ u w huw h) := by
  have hsq : Topology.IsQuotientMap fun y : Circle ↦ y ^ 2 :=
    (continuous_id.pow 2).isClosedMap.isQuotientMap (continuous_id.pow 2)
      fun z : Circle ↦ Circle.exists_pow_nat_eq z two_ne_zero
  refine hsq.continuous_iff.2 ?_
  simp only [Function.comp_def, spinCCircle_sq]
  exact (spinCGroup.continuous_mk Q hQ).comp
    ((continuous_spinCircle Q huw h).prodMk continuous_id)

end CliffordAlgebra
