/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.MellinBarnes
import TauCeti.Analysis.Complex.SlitPlane

/-!
# Barnes's integral for Euler's hypergeometric integral

Barnes's integral (DLMF 15.6.6) represents the regularized Gauss function at a negative argument
`-x`, `x > 0`, as a vertical integral of Gamma functions,

`𝐅(a, b; c; -x) = (1 / (2π Γ(a) Γ(b))) ∫ Γ(a + t) Γ(b + t) Γ(-t) / Γ(c + t) x^t dy`,

along the line `t = σ + i y`, `y ∈ ℝ`, with `-min(Re a, Re b) < σ < 0`. The line separates the
poles `t = -a - k`, `t = -b - k` of the first two factors from the poles `t = k` of `Γ(-t)`. This
file proves the identity for Euler's normalized integral `Complex.eulerIntegral a b c (-x)`, which
represents `𝐅(a, b; c; -x)` where `0 < Re b < Re c` (DLMF 15.6.1), so `Re b < Re c` is assumed as
well; the vertical integral converges there.

Both results specialize the slit-plane Mellin–Barnes theorems
`Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_inv_Gamma_mul_neg_cpow` and
`Complex.eulerIntegral_eq_mellinBarnes`
(`TauCeti/Analysis/SpecialFunctions/Hypergeometric/MellinBarnes.lean`) to `z = -x` (`x > 0`).

## Main results

* `Complex.verticalIntegrable_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_cpow`: for `σ < 0`,
  `-σ < Re a`, `-σ < Re b < Re c` and `x > 0`, the integrand
  `Γ(a + t) Γ(b + t) Γ(-t) Γ(c + t)⁻¹ x^t` of DLMF 15.6.6 is integrable along the line
  `t = σ + i y`.
* `Complex.eulerIntegral_neg_eq_mellinBarnes`: DLMF 15.6.6 for Euler's integral at the
  negative argument `-x`.

## References

* NIST Digital Library of Mathematical Functions, equations 15.6.1 and 15.6.6,
  <https://dlmf.nist.gov/15.6>.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.5.
-/

public section

open Real
open Complex hiding exp continuous_exp log

namespace Complex

/-- **Convergence of the Mellin–Barnes integral** (DLMF 15.6.6) in the region of Euler's
integral: for `σ < 0`, `-σ < Re a`, `-σ < Re b`, `Re b < Re c` and `x > 0`, the integrand
`Γ(a + t) Γ(b + t) Γ(-t) Γ(c + t)⁻¹ x^t` is integrable along the line `t = σ + i y`. -/
theorem verticalIntegrable_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_cpow {a b c : ℂ}
    {σ x : ℝ} (hσ : σ < 0) (hσa : -σ < a.re) (hσb : -σ < b.re) (_hbc : b.re < c.re) (hx : 0 < x) :
    VerticalIntegrable
      (fun t ↦ Gamma (a + t) * Gamma (b + t) * Gamma (-t) * (Gamma (c + t))⁻¹ * (x : ℂ) ^ t) σ := by
  have hz : -(-(x : ℂ)) ∈ slitPlane := by simpa using ofReal_mem_slitPlane.mpr hx
  have ha : ∀ n : ℕ, a.re + σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hb : ∀ n : ℕ, b.re + σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hσ' : ∀ n : ℕ, σ ≠ n := fun n _ ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  simpa [VerticalIntegrable] using
    integrable_Gamma_mul_Gamma_mul_Gamma_mul_inv_Gamma_mul_neg_cpow c hz ha hb hσ'

/-- **The Mellin–Barnes integral** (DLMF 15.6.6) for Euler's integral at a negative argument. For
`x > 0`, `σ < 0`, `-σ < Re a`, `-σ < Re b` and `Re b < Re c`,
`eulerIntegral a b c (-x) = (2π Γ(a) Γ(b))⁻¹ ∫ Γ(a + t) Γ(b + t) Γ(-t) Γ(c + t)⁻¹ x^t dy`
along the line `t = σ + i y`. -/
theorem eulerIntegral_neg_eq_mellinBarnes {a b c : ℂ} {σ x : ℝ} (hσ : σ < 0) (hσa : -σ < a.re)
    (hσb : -σ < b.re) (hbc : b.re < c.re) (hx : 0 < x) :
    eulerIntegral a b c (-x) = (2 * π * Gamma a * Gamma b)⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I) := by
  have hz : -(-(x : ℂ)) ∈ slitPlane := by simpa using ofReal_mem_slitPlane.mpr hx
  simpa using eulerIntegral_eq_mellinBarnes a hbc hz hσ (neg_lt.mp hσa) (neg_lt.mp hσb)

end Complex
