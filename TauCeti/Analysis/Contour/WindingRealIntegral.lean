/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Analysis.Contour.WindingInteger

/-!
# The real bounded-integrand formula for the winding number (Hungerbühler–Wasem Prop 2.3)

For a closed piecewise-`C¹` curve `γ` that avoids a point `w`, Hungerbühler–Wasem Prop 2.3 evaluates
the generalized winding number by the **real** integral

`n_w(γ) = (1 / 2π) ∫_a^b (x ẏ − y ẋ) / (x² + y²) dt`,

where `x + i y = γ − w`. Writing `γ − w = x + i y` and `γ' = ẋ + i ẏ`, the winding integrand
`(γ − w)⁻¹ · γ'` has imaginary part exactly `(x ẏ − y ẋ) / (x² + y²)` (the real integrand above,
here with denominator `Complex.normSq (γ − w) = x² + y²`); this pointwise piece is the private
helper `inv_mul_im`. For a point *off* the curve the
winding number is a genuine integer (`exists_int_windingNumber_of_closed`), hence real, so the
ordinary index integral `(2πi)⁻¹ ∮_γ dz/(z − w)` is purely imaginary: its real part vanishes and its
imaginary part is the real integral above. This is the off-curve (no principal-value) case of the
real formula — the computational workhorse of Layer 1; the on-curve bounded-integrand form and the
`½·k·|Λ̇|` crossing value need the immersion geometry and stay separate.

## Main results

* `TauCeti.Contour.windingNumber_eq_real_integral_of_closed` — the winding number of a closed curve
  off `w` equals the real bounded integral `(1 / 2π) ∫ (x ẏ − y ẋ) / (x² + y²)`.

This is Layer 1 of the Hungerbühler–Wasem generalized residue theorem (HW Thm 3.3).

## References

* N. Hungerbühler, M. Wasem, *Non-integer valued winding numbers and a generalized Residue
  Theorem*, arXiv:1808.00997 — Prop 2.3.

## Provenance

The pointwise imaginary-part decomposition and the real winding formula are migrated and cleaned
from the AINTLIB `LeanModularForms` generalized-winding-number development, restated here for a raw
`γ : ℝ → ℂ` on an oriented interval in the vocabulary the roadmap fixes.
-/

public section

open Complex MeasureTheory Set intervalIntegral

open scoped Interval

namespace TauCeti.Contour

/-- **Imaginary part of `z⁻¹ · v`.** Writing `z = x + i y` and `v = ẋ + i ẏ`, the imaginary part of
`z⁻¹ · v` is `(x ẏ − y ẋ) / (x² + y²)`, with `Complex.normSq z = x² + y²`. This is the Hungerbühler–
Wasem real winding integrand (Prop 2.3). Stated for all `z`, `v` (at `z = 0` both sides are `0`). -/
private theorem inv_mul_im (z v : ℂ) :
    (z⁻¹ * v).im = (z.re * v.im - z.im * v.re) / Complex.normSq z := by
  rw [inv_mul_eq_div, Complex.div_im]; ring

/-- **The real bounded-integrand formula for the winding number** (Hungerbühler–Wasem Prop 2.3,
off-curve case). For a curve `γ` on the oriented interval with endpoints `a`, `b` that returns to
its start (`γ a = γ b`), is continuous on `Set.uIcc a b`, differentiable off a countable set `P`,
avoids
`w` throughout, and has an interval-integrable index integrand, the generalized winding number about
`w` is the real integral

`n_w(γ) = (1 / 2π) ∫_a^b (x ẏ − y ẋ) / (x² + y²) dt`,   `x + i y = γ − w`,

with bounded real integrand and no principal value. The winding number is a genuine integer here
(`exists_int_windingNumber_of_closed`), so the index integral is purely imaginary; its imaginary
part is this real integral (`inv_mul_im`), while its real part — the increment of `log ‖γ − w‖` —
vanishes by closedness. -/
theorem windingNumber_eq_real_integral_of_closed {γ : ℝ → ℂ} {w : ℂ} {a b : ℝ} {P : Set ℝ}
    (hclosed : γ a = γ b) (hP : P.Countable)
    (hγ_cont : ContinuousOn γ (Set.uIcc a b))
    (hγ_diff : ∀ t ∈ Set.Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t)
    (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ w)
    (h_int : IntervalIntegrable (fun t ↦ (γ t - w)⁻¹ * deriv γ t) MeasureTheory.volume a b) :
    windingNumber γ a b w
      = ((1 / (2 * Real.pi)
          * ∫ t in a..b,
              ((γ t - w).re * (deriv γ t).im - (γ t - w).im * (deriv γ t).re)
                / Complex.normSq (γ t - w) : ℝ) : ℂ) := by
  obtain ⟨n, hn⟩ := exists_int_windingNumber_of_closed hclosed hP hγ_cont hγ_diff h_avoid h_int
  -- The winding number is the ordinary index integral, and it equals the integer `n`.
  have hwind_int : windingNumber γ a b w
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ * ∫ t in a..b, (γ t - w)⁻¹ * deriv γ t :=
    windingNumber_eq_integral_of_avoidance hγ_cont h_avoid h_int
  have h2πI_ne : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
      Complex.I_ne_zero
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
  have hrealint : (∫ t in a..b,
        ((γ t - w).re * (deriv γ t).im - (γ t - w).im * (deriv γ t).re)
          / Complex.normSq (γ t - w)) = 2 * Real.pi * (n : ℝ) := by
    have hpt : ∀ t, ((γ t - w).re * (deriv γ t).im - (γ t - w).im * (deriv γ t).re)
        / Complex.normSq (γ t - w) = ((γ t - w)⁻¹ * deriv γ t).im :=
      fun t ↦ (inv_mul_im (γ t - w) (deriv γ t)).symm
    simp_rw [hpt, ← RCLike.im_to_complex]
    rw [intervalIntegral_im h_int, RCLike.im_to_complex, him]
  -- Assemble: `n_w(γ) = n = (1 / 2π) · (2π · n)`.
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  rw [hn, hrealint, one_div, inv_mul_cancel_left₀ hpi, Complex.ofReal_intCast]

end TauCeti.Contour
