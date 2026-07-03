/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Integral.CircleIntegral

/-!
# Model-sector generalized winding numbers (Hungerbühler–Wasem §2)

This file computes the **generalized winding number of a circular arc**: for a counterclockwise
arc of opening angle `α` about its centre `z₀`, the value of `(2πi)⁻¹ ∮ dz/(z − z₀)` along the arc
is `α / 2π` (Hungerbühler–Wasem, arXiv:1808.00997, (2.4)). Because `z₀` is the *centre* — off the
arc — the contour integral is an ordinary interval integral, and the computation is elementary:
the integrand `γ̇ / (γ − z₀)` is constantly `i` on the arc `γ θ = z₀ + r·e^{iθ}`.

The positive-angle specializations record the two arc values used downstream in the generalized
residue theory: a **semicircle** (`α = π`) has winding `½` and a **`π/3` arc** has winding `1/6`.
A full circle (`α = 2π`) has winding `1`, reconciling with `circleIntegral.integral_sub_center_inv`.

## Main results

* `windingNumber_modelSector` — the arc of opening angle `α` has winding number `α / 2π`.
* `windingNumber_modelSector_pi` — the `α = π` (semicircle) specialization: winding `½`.
* `windingNumber_modelSector_pi_div_three` — the `α = π/3` specialization: winding `1/6`.

## Provenance

Migrated and adapted from the AINTLIB `LeanModularForms` project (the sector-geometry material of
`ForMathlib/HungerbuhlerWasem/Crossing.lean`).

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997, (2.4).
-/

public section

noncomputable section

open Complex intervalIntegral

namespace TauCeti.Contour

/-- **The model-sector winding number** (Hungerbühler–Wasem (2.4)). A counterclockwise circular arc
of opening angle `α` about its centre `z₀` contributes generalized winding number `α / 2π`:
`(2πi)⁻¹ ∫_0^α (γ̇ / (γ − z₀)) dθ = α / 2π` for `γ θ = z₀ + r·e^{iθ}`. In particular a full circle
(`α = 2π`) has winding number `1`, reconciling with `circleIntegral.integral_sub_center_inv`. -/
theorem windingNumber_modelSector {z₀ : ℂ} {r : ℝ} (hr : r ≠ 0) (α : ℝ) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..α, deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀)
      = (α : ℂ) / (2 * (Real.pi : ℂ)) := by
  have hint : ∀ θ : ℝ, deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀) = Complex.I := by
    intro θ
    have hne : circleMap (0 : ℂ) r θ ≠ 0 := circleMap_ne_center hr
    rw [deriv_circleMap, circleMap_sub_center, mul_comm (circleMap 0 r θ) Complex.I,
      mul_div_assoc, div_self hne, mul_one]
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  simp_rw [hint]
  rw [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  field_simp

/-- **A semicircular arc (`α = π`) has winding number `½`** — the `α = π` specialization of
`windingNumber_modelSector` (`π / 2π = ½`). -/
theorem windingNumber_modelSector_pi {z₀ : ℂ} {r : ℝ} (hr : r ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..Real.pi, deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀)
      = 1 / 2 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [windingNumber_modelSector hr]
  field_simp

/-- **A `π/3` arc (`α = π/3`) has winding number `1/6`** — the `α = π/3` specialization of
`windingNumber_modelSector` (`(π/3) / 2π = 1/6`). -/
theorem windingNumber_modelSector_pi_div_three {z₀ : ℂ} {r : ℝ} (hr : r ≠ 0) :
    (2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
        ∫ θ in (0 : ℝ)..(Real.pi / 3), deriv (circleMap z₀ r) θ / (circleMap z₀ r θ - z₀)
      = 1 / 6 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [windingNumber_modelSector hr]
  push_cast
  field_simp
  ring

end TauCeti.Contour

end
