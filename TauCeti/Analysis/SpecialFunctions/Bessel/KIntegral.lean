/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes.ShiftedProduct
import TauCeti.Analysis.SpecialFunctions.MacdonaldIntegral

/-!
# The integral `∫₀^∞ s^{p-1} e^{-s - x/s} ds` as a series

For `x > 0` and real `p` the integral

`∫₀^∞ s^{p - 1} e^{-s - x/s} ds = 2 x^{p/2} K_p(2 √x)`

is the Macdonald function in the reduced form of DLMF 10.32.10. This file proves that for
`0 < p < 1` it is the combination of reduced Bessel series

`∫₀^∞ s^{p - 1} e^{-s - x/s} ds = (π / sin pπ) (𝐅(1 - p, x) - x^p 𝐅(1 + p, x))`,

where `𝐅(b, x) = ∑ₙ xⁿ / (n! Γ(b + n))` is Mathlib's regularized `₀F₁`,
`Complex.regularizedHGFun 0 {b}`. In Bessel notation this is
`K_p = π (I_{-p} - I_p) / (2 sin pπ)` (DLMF 10.27.4) at the argument `2 √x`, with
`I_{±p}(2 √x) = x^{±p/2} 𝐅(1 ± p, x)`. Integrals of this shape arise from
`∫₀^∞ e^{-ζ cosh u} cosh(pu) du` by the substitution `s = (ζ/2) eᵘ`, with `x = ζ²/4`; this is how
integral representations of the form `z^{1/2} ∫₀^∞ e^{-ζ cosh u} cosh(pu) du`, such as that of
the generalized Airy functions with `p = 1/(n + 2)`, reduce to series in `𝐅`.

The proof combines the Mellin–Barnes inversion formula `Complex.mellinInv_Gamma_mul_Gamma_add`
(`TauCeti/Analysis/SpecialFunctions/MacdonaldIntegral.lean`) at `σ = 1` with the general
complex-parameter residue evaluation `Complex.mellinInv_Gamma_mul_Gamma_add_eq_regularizedHGFun`
(`TauCeti/Analysis/SpecialFunctions/Gamma/MellinBarnes/ShiftedProduct.lean`).

## Main results

* `Complex.integral_cpow_mul_exp_neg_add_div_Ioi`: the series evaluation above for `0 < p < 1`.

## References

* G. N. Watson, *A Treatise on the Theory of Bessel Functions*, 2nd ed., Cambridge University
  Press, 1944, §3.7 (6) and §6.22 (15).
* *NIST Digital Library of Mathematical Functions*, 10.27.4, 10.32.10 and 10.43.19,
  <https://dlmf.nist.gov/10>.
-/

public section

noncomputable section

open Set
open scoped Real

namespace Complex

/-- **The integral `∫₀^∞ s^{p - 1} e^{-s - x/s} ds` as a combination of `₀F₁` series.** For
`0 < p < 1` and `x > 0`,
`∫₀^∞ s^{p - 1} e^{-s - x/s} ds = (π / sin pπ) (𝐅(1 - p, x) - x^p 𝐅(1 + p, x))`, where
`𝐅(b, x) = ∑ₙ xⁿ / (n! Γ(b + n))` is the regularized `₀F₁`. In Bessel notation both sides are
`2 x^{p/2} K_p(2 √x)`, the right side being `(π / sin pπ) x^{p/2} (I_{-p}(2 √x) - I_p(2 √x))`. -/
theorem integral_cpow_mul_exp_neg_add_div_Ioi {p x : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) :
    ∫ s in Ioi (0 : ℝ), (s : ℂ) ^ ((p : ℂ) - 1) * Real.exp (-(s + x / s)) =
      ((π / Real.sin (π * p) : ℝ) : ℂ) * (regularizedHGFun 0 {1 - (p : ℂ)} x -
        (x : ℂ) ^ (p : ℂ) * regularizedHGFun 0 {1 + (p : ℂ)} x) := by
  have hp : ∀ m : ℤ, (p : ℂ) ≠ m := fun m h ↦ by
    have hre : p = m := by simpa using congrArg re h
    have h1 : (0 : ℤ) < m := by exact_mod_cast hre ▸ hp0
    have h2 : m < (1 : ℤ) := by exact_mod_cast hre ▸ hp1
    omega
  have h := (mellinInv_Gamma_mul_Gamma_add (a := (p : ℂ)) one_pos
    (by rw [ofReal_re]; linarith) hx).symm.trans
    (mellinInv_Gamma_mul_Gamma_add_eq_regularizedHGFun hp one_pos
      (by rw [ofReal_re]; linarith) hx)
  refine h.trans ?_
  rw [← ofReal_mul, ← ofReal_sin, ← ofReal_div]

end Complex

end
