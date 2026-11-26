/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Poisson.Boundary.Function
import TauCeti.Analysis.Complex.UpperHalfPlane.Cayley

/-!
# Checks for boundary functions of bounded holomorphic functions on the half-plane

Explicit boundary functions `F*` (`TauCeti.upperHalfPlaneBoundaryFun`).

* *The exponential.* For `F(z) = e^{iz}`, `|F(x + iy)| = e^{-y}`
  (`norm_exp_mul_I_ofReal_add_mul_I`), so `F` is bounded by `1` on `ℂ₊`; its boundary function is
  `F*(x) = e^{ix}` (`upperHalfPlaneBoundaryFun_exp_mul_I`), and `F = P[F*]` on `ℂ₊`
  (`exp_mul_I_eq_upperHalfPlanePoissonIntegralFun`).
* *A constant.* The boundary function of `c` is `c` (`TauCeti.upperHalfPlaneBoundaryFun_const`).
* *A Blaschke factor.* For `F(z) = (z - i) / (z + i)`, `F*(x) = (x - i) / (x + i)` has modulus `1`
  everywhere (`norm_upperHalfPlaneBoundaryFun_blaschke`).
-/

public section

noncomputable section

namespace TauCeti.Examples.BoundaryFunction

open Complex Filter MeasureTheory Set Topology
open _root_.UpperHalfPlane (upperHalfPlaneSet)

/-! ### The exponential `e^{iz}` -/

/-- `|e^{i(x + iy)}| = e^{-y}`. -/
theorem norm_exp_mul_I_ofReal_add_mul_I (x y : ℝ) :
    ‖exp (I * ((x : ℂ) + y * I))‖ = Real.exp (-y) := by
  rw [norm_exp]
  congr 1
  simp

/-- `e^{iz}` is bounded by `1` on the upper half-plane. -/
theorem norm_exp_mul_I_le_one {z : ℂ} (hz : z ∈ upperHalfPlaneSet) : ‖exp (I * z)‖ ≤ 1 := by
  rw [norm_exp, Real.exp_le_one_iff]
  simpa using (le_of_lt (show 0 < z.im from hz))

/-- The boundary function of `e^{iz}` is `e^{ix}`. -/
theorem upperHalfPlaneBoundaryFun_exp_mul_I (x : ℝ) :
    upperHalfPlaneBoundaryFun (fun z ↦ exp (I * z)) x = exp (I * x) :=
  upperHalfPlaneBoundaryFun_eq_of_continuousOn (by fun_prop) x

/-- `e^{iz} = P[e^{ix}](z)` on the upper half-plane. -/
theorem exp_mul_I_eq_upperHalfPlanePoissonIntegralFun {z : ℂ} (hz : z ∈ upperHalfPlaneSet) :
    exp (I * z) = upperHalfPlanePoissonIntegralFun (fun x : ℝ ↦ exp (I * x)) z := by
  rw [eq_upperHalfPlanePoissonIntegralFun_upperHalfPlaneBoundaryFun (S := 1)
    (fun w _ ↦ by fun_prop) (fun w hw ↦ norm_exp_mul_I_le_one hw) hz]
  rw [funext upperHalfPlaneBoundaryFun_exp_mul_I]

/-! ### A Blaschke factor -/

/-- The boundary function of `(z - i) / (z + i)` has modulus `1` everywhere. -/
theorem norm_upperHalfPlaneBoundaryFun_blaschke (x : ℝ) :
    ‖upperHalfPlaneBoundaryFun (fun z ↦ (z - I) / (z + I)) x‖ = 1 := by
  rw [upperHalfPlaneBoundaryFun_eq_of_continuousWithinAt
    (continuousAt_sub_I_div_add_I x).continuousWithinAt, norm_div, norm_sub_I_div_norm_add_I_ofReal]

end TauCeti.Examples.BoundaryFunction
