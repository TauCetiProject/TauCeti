/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
public import TauCeti.Analysis.Contour.Winding.Integrand
public import TauCeti.Analysis.Contour.Winding.Number.Basic
import TauCeti.Analysis.Contour.Winding.AbsolutelyContinuous.Basic

/-!
# The real formula for the winding number (Hungerbühler–Wasem Prop 2.3)

For a closed absolutely continuous curve `γ` that avoids a point `w`, Hungerbühler–Wasem Prop 2.3
evaluates the generalized winding number by the **real** integral

`n_w(γ) = (1 / 2π) ∫_a^b (x ẏ − y ẋ) / (x² + y²) dt`,

where `x + i y = γ − w`. Writing `γ − w = x + i y` and `γ' = ẋ + i ẏ`, the winding integrand
`(γ − w)⁻¹ · γ'` has imaginary part exactly `(x ẏ − y ẋ) / (x² + y²)` (the real integrand above,
here with denominator `Complex.normSq (γ − w) = x² + y²`); this pointwise piece is
`realWindingIntegrand_eq_div`. For a point *off* the curve the winding number is a genuine integer
(`AbsolutelyContinuousOnInterval.exists_int_windingNumber`), hence real, so the unnormalized
integral `∮_γ dz/(z − w)` is purely imaginary: its real part vanishes, and its imaginary part
divided by `2π` is the winding number, given by the real integral above. This is the off-curve
(no principal-value) case of the real formula; the on-curve bounded-integrand form and the
`½·k·|Λ̇|` crossing value need the immersion geometry and stay separate.

## Main results

* `AbsolutelyContinuousOnInterval.windingNumber_eq_real_integral` — the winding number of a closed
  absolutely continuous curve off `w` equals the real integral `(1 / 2π) ∫ (x ẏ − y ẋ) / (x² + y²)`.

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Prop 2.3.

## Provenance

The pointwise imaginary-part decomposition and the real winding formula are migrated and cleaned
from the AINTLIB `LeanModularForms` generalized-winding-number development, restated here for a raw
`γ : ℝ → ℂ` on an oriented interval.
-/

public section

open Complex MeasureTheory Set intervalIntegral

open scoped Interval

namespace TauCeti.Contour

/-- **The real formula for the winding number** (Hungerbühler–Wasem Prop 2.3, off-curve case).
For a closed absolutely continuous curve `γ` on the oriented interval with endpoints `a`, `b`
(`γ a = γ b`) that avoids `w`, the generalized winding number about `w` is the real integral

`n_w(γ) = (1 / 2π) ∫_a^b (x ẏ − y ẋ) / (x² + y²) dt`,   `x + i y = γ − w`,

with no principal value. The winding number is an integer here, so the index integral is purely
imaginary; its imaginary part is this real integral (`realWindingIntegrand_eq_div`), while its real
part — the increment of `log ‖γ − w‖` — vanishes by closedness. -/
theorem _root_.AbsolutelyContinuousOnInterval.windingNumber_eq_real_integral {γ : ℝ → ℂ} {w : ℂ}
    {a b : ℝ} (hγ : AbsolutelyContinuousOnInterval γ a b) (hclosed : γ a = γ b)
    (hw : w ∉ γ '' Set.uIcc a b) :
    windingNumber γ a b w
      = ((1 / (2 * Real.pi)
          * ∫ t in a..b, realWindingIntegrand (γ t - w) (deriv γ t) : ℝ) : ℂ) := by
  obtain ⟨n, hn⟩ := hγ.exists_int_windingNumber hclosed hw
  have h_int := hγ.intervalIntegrable_inv_sub_mul_deriv hw
  -- The winding number is the ordinary index integral, and it equals the integer `n`.
  have hwind_int : windingNumber γ a b w
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t :=
    hγ.windingNumber_eq_integral hw
  have h2πI_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  -- Read off the index integral: `∮_γ dz/(z − w) = 2πi · n`.
  have hCI : (∫ t in a..b, (γ t - w)⁻¹ * deriv γ t) = 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) := by
    have key : (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t = (n : ℂ) :=
      hwind_int.symm.trans hn
    rw [← key, ← mul_assoc, mul_inv_cancel₀ h2πI_ne, one_mul]
  -- Its imaginary part is `2π · n`, purely from the value `2πi · n`.
  have him : (∫ t in a..b, (γ t - w)⁻¹ * deriv γ t).im = 2 * Real.pi * (n : ℝ) := by
    rw [hCI]
    have hrw : 2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) = ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [hrw]
    simp [Complex.mul_im]
  -- The real integrand is the imaginary part of the winding integrand, so its integral is `2π · n`.
  have hrealint : (∫ t in a..b, realWindingIntegrand (γ t - w) (deriv γ t)) =
      2 * Real.pi * (n : ℝ) := by
    have hpt : ∀ t, realWindingIntegrand (γ t - w) (deriv γ t) = ((γ t - w)⁻¹ * deriv γ t).im :=
      fun t ↦ realWindingIntegrand_def (γ t - w) (deriv γ t)
    simp_rw [hpt, ← RCLike.im_to_complex]
    rw [intervalIntegral_im h_int, RCLike.im_to_complex, him]
  -- Assemble: `n_w(γ) = n = (1 / 2π) · (2π · n)`.
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  rw [hn, hrealint, one_div, inv_mul_cancel_left₀ hpi, Complex.ofReal_intCast]

end TauCeti.Contour
