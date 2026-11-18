/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Line
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# The `W^{1,2}` energy density of a section

For a map `ξ : ℝ × ℝ → V` into a normed space, the `W^{1,2}` energy density
`‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²` (`TauCeti.Floer.sobolevDensity`) is the integrand of the squared
`W^{1,2}` norm of `ξ` in the coordinates `(s, t)`, the derivatives being taken along the coordinate
vectors `TauCeti.stdComplexLineReal` and `TauCeti.stdComplexLineImag`. It is the energy that the
semi-Fredholm estimates of the linearized Floer operator control.

## Main results

* `TauCeti.Floer.sobolevDensity_nonneg`: the density is nonnegative.
* `TauCeti.Floer.continuous_sobolevDensity`: the density of a `C¹` map is continuous.
* `TauCeti.Floer.sobolevDensity_congr`: the density at `z` depends only on the germ of the map
  at `z`.
-/

public section

open scoped Topology

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- The `W^{1,2}` energy density `‖∂s ξ‖² + ‖∂t ξ‖² + ‖ξ‖²` of a map `ξ : ℝ × ℝ → V`. -/
noncomputable def sobolevDensity (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : ℝ :=
  ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 + ‖ξ z‖ ^ 2

theorem sobolevDensity_apply (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    sobolevDensity ξ z =
      ‖fderiv ℝ ξ z stdComplexLineReal‖ ^ 2 + ‖fderiv ℝ ξ z stdComplexLineImag‖ ^ 2 +
        ‖ξ z‖ ^ 2 :=
  (rfl)

theorem sobolevDensity_nonneg (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : 0 ≤ sobolevDensity ξ z := by
  rw [sobolevDensity_apply]
  positivity

/-- The zero map has zero energy density. -/
@[simp]
theorem sobolevDensity_zero (z : ℝ × ℝ) : sobolevDensity (0 : ℝ × ℝ → V) z = 0 := by
  simp [sobolevDensity_apply]

/-- The `W^{1,2}` energy density of a `C¹` map is continuous. -/
theorem continuous_sobolevDensity {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) :
    Continuous (sobolevDensity ξ) := by
  have := hξ.continuous_fderiv one_ne_zero
  have := hξ.continuous
  simp only [funext (sobolevDensity_apply ξ)]
  fun_prop

/-- Two maps that agree near `z` have the same energy density at `z`. -/
theorem sobolevDensity_congr {ξ η : ℝ × ℝ → V} {z : ℝ × ℝ} (h : ξ =ᶠ[𝓝 z] η) :
    sobolevDensity ξ z = sobolevDensity η z := by
  rw [sobolevDensity_apply, sobolevDensity_apply, h.fderiv_eq, h.eq_of_nhds]

end TauCeti.Floer
