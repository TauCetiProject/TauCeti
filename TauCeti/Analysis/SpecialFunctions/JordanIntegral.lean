/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import TauCeti.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Jordan's integral bound

The estimate

$$\int_0^\pi e^{-c\sin\theta}\,d\theta \;<\; \frac{\pi}{c} \qquad (c > 0)$$

which is the analytic engine of **Jordan's lemma** in contour integration. The integrand is
close to `1` near the endpoints `θ = 0, π`, so the bound is not obtained by a pointwise
estimate on the whole interval; what makes it work is **Jordan's inequality**
`sin θ ≥ (2/π) θ` on `[0, π/2]` (Mathlib's `Real.mul_le_sin`), which forces enough decay near
the endpoint to make the whole integral `O(1/c)`.

Applied to `|e^{iaz}| = e^{-aR\sin\theta}` on an arc of radius `R`, the relevant instance is
`c = aR`, giving the bound `1/(aR)`; its `1/R` factor is what cancels the `R` in the arc length
`πR`. That is why Jordan's lemma beats the naive `ML` bound, which would instead need the
integrand itself to decay faster than `1/R`.

## Main results

* `TauCeti.integral_exp_neg_mul_sin_lt` — the bound above.

## References

* C. Jordan, *Cours d'analyse de l'École Polytechnique*, vol. 2 (1894), §270.
* P. Henrici, *Applied and Computational Complex Analysis*, vol. 1, §4.8.
-/

public section

open Real MeasureTheory Set

namespace TauCeti

/-- On `[0, π/2]` Jordan's inequality bounds the integrand by a decaying exponential. -/
private theorem exp_neg_mul_sin_le {c : ℝ} (hc : 0 ≤ c) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) (π / 2)) :
    Real.exp (-c * Real.sin θ) ≤ Real.exp (-(2 * c / π) * θ) := by
  have := mul_le_mul_of_nonneg_left (Real.mul_le_sin hθ.1 hθ.2) hc
  rw [Real.exp_le_exp]
  linarith [show 2 * c / π * θ = c * (2 / π * θ) by ring]

/-- Half the interval carries half the integral: `θ ↦ π - θ` exchanges `[0, π/2]` and
`[π/2, π]` and fixes `sin`. -/
private theorem integral_exp_neg_mul_sin_eq_two_mul (c : ℝ) :
    ∫ θ in (0 : ℝ)..π, Real.exp (-c * Real.sin θ)
      = 2 * ∫ θ in (0 : ℝ)..(π / 2), Real.exp (-c * Real.sin θ) := by
  have hrefl : ∫ θ in (π / 2)..π, Real.exp (-c * Real.sin θ)
      = ∫ θ in (0 : ℝ)..(π / 2), Real.exp (-c * Real.sin θ) := by
    simpa [Real.sin_pi_sub, sub_half] using intervalIntegral.integral_comp_sub_left
      (fun θ => Real.exp (-c * Real.sin θ)) (a := π / 2) (b := π) π
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := π / 2)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop), hrefl, two_mul]

/-- **Jordan's integral bound.** For `c > 0`, `∫₀^π e^{-c sin θ} dθ < π / c`. -/
theorem integral_exp_neg_mul_sin_lt (c : ℝ) (hc : 0 < c) :
    ∫ θ in (0 : ℝ)..π, Real.exp (-c * Real.sin θ) < π / c := by
  have hmono : (∫ θ in (0 : ℝ)..(π / 2), Real.exp (-c * Real.sin θ))
      ≤ ∫ θ in (0 : ℝ)..(π / 2), Real.exp (-(2 * c / π) * θ) :=
    intervalIntegral.integral_mono_on (by positivity)
      (by apply Continuous.intervalIntegrable; fun_prop)
      (by apply Continuous.intervalIntegrable; fun_prop) fun θ hθ => exp_neg_mul_sin_le hc.le hθ
  rw [integral_exp_mul (neg_ne_zero.mpr (by positivity)),
    show -(2 * c / π) * (π / 2) = -c by field_simp, mul_zero, Real.exp_zero] at hmono
  rw [integral_exp_neg_mul_sin_eq_two_mul]
  calc 2 * ∫ θ in (0 : ℝ)..(π / 2), Real.exp (-c * Real.sin θ)
      ≤ π * (1 - Real.exp (-c)) / c := by
        convert mul_le_mul_of_nonneg_left hmono zero_le_two using 1
        field_simp
        ring
    _ < π / c := by
        gcongr
        nlinarith [mul_pos Real.pi_pos (Real.exp_pos (-c))]

end TauCeti

end
