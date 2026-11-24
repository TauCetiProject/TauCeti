/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Circle.Degree
import TauCeti.Analysis.SpecialFunctions.Complex.Circle.Inner

/-!
# Monodromy of the double cover of the circle

The squaring map `z ↦ z²` is a double cover of the circle (`Circle.isQuotientCoveringMap_npow`).
Lifting the loop `t ↦ exp(2πit)` through it from a sheet `z` traces the half turn
`t ↦ z exp(πit)`, which ends at `-z`. So the generator of `π₁(S¹)` exchanges the two sheets `±1`
of the fibre over `1` (`Circle.coe_monodromy_sq_expLoop`).

## Main results

* `Circle.coe_monodromy_sq_expLoop`: the monodromy of `z ↦ z²` along `expLoop` sends `z` to `-z`.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3.
-/

public section

namespace Circle

open Real

/-- **For the double cover of the circle, the generator of `π₁(S¹)` exchanges the sheets**: lifting
the loop `t ↦ exp(2πit)` through `z ↦ z²` from the sheet `z` traces the half turn
`t ↦ z exp(πit)`, which ends at `-z`. -/
theorem coe_monodromy_sq_expLoop (z : Circle) (hz : z ^ 2 = 1) :
    ((isQuotientCoveringMap_npow 2).isCoveringMap.monodromy (.mk expLoop) ⟨z, hz⟩ : Circle) =
      -z := by
  have hΓ : (fun w : Circle ↦ w ^ 2) ∘
      (⟨fun t : unitInterval ↦ z * exp (π * t), by fun_prop⟩ : C(unitInterval, Circle)) =
        expLoop := by
    funext t
    rw [Function.comp_apply, ContinuousMap.coe_mk, mul_pow, hz, _root_.one_mul, expLoop_apply,
      ← exp_nsmul]
    congr 1
    rw [nsmul_eq_mul, Nat.cast_ofNat]
    ring
  rw [(isQuotientCoveringMap_npow 2).isCoveringMap.monodromy_eq_apply_one hΓ (by simp)]
  simp [exp_pi]

end Circle
