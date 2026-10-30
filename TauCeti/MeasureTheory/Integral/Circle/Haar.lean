/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# Haar integrals on the additive circle as circle averages

Normalized Haar measure on `AddCircle (2 * π)` corresponds to normalized arc length on the unit
circle in `ℂ` under `AddCircle.toCircle`. Since `Complex.arg` inverts this map on the unit circle,
a Haar integral of `g` equals the circle average of `g ∘ Complex.arg` over the unit circle. This
lets results about circle averages, such as the Poisson integral formula, be read as statements
about integrals over the additive circle.
-/

public section

open Complex MeasureTheory Real

namespace AddCircle

local instance : Fact (0 < 2 * π) := ⟨two_pi_pos⟩

/-- On the unit circle, `AddCircle.toCircle` inverts `Complex.arg`. -/
theorem toCircle_arg_of_mem_sphere {z : ℂ} (hz : z ∈ Metric.sphere 0 1) :
    (toCircle (Complex.arg z : AddCircle (2 * π)) : ℂ) = z := by
  let u : Circle := ⟨z, by simpa [Submonoid.unitSphere] using hz⟩
  have hu := Circle.exp_arg u
  simpa [u, toCircle_apply_mk, circleMap] using congrArg Subtype.val hu

/-- A Haar integral over `AddCircle (2 * π)` is the circle average over the unit circle of the
integrand composed with `Complex.arg`. -/
theorem integral_haarAddCircle_eq_circleAverage_arg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : AddCircle (2 * π) → E) :
    ∫ θ, g θ ∂haarAddCircle = circleAverage (fun z ↦ g (Complex.arg z)) 0 1 := by
  rw [integral_haarAddCircle, circleAverage,
    ← AddCircle.intervalIntegral_preimage (2 * π) 0]
  rw [zero_add]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  apply congrArg g
  apply injective_toCircle (mul_ne_zero two_ne_zero pi_ne_zero)
  simpa [toCircle_apply_mk, circleMap] using (Circle.exp_arg (Circle.exp θ)).symm

end AddCircle
