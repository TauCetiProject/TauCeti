/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.HardyZ
public import TauCeti.NumberTheory.LSeries.RiemannZeta.RiemannSiegelTheta.Basic

/-!
# Hardy's function through the Riemann–Siegel theta function

Mathlib's `hardyZ t` is the quotient `Λ(1/2 + it) / |Γℝ(1/2 + it)|` of the completed zeta function
by the modulus of its archimedean factor. Since `ϑ(t)` is an argument of `Γℝ(1/2 + it)`
(`TauCeti.Gammaℝ_half_add_mul_I_eq_norm_mul_exp_riemannSiegelTheta`), this quotient is
`e^{iϑ(t)} ζ(1/2 + it)` (`TauCeti.ofReal_hardyZ_eq_exp_riemannSiegelTheta_mul`), the form of Hardy's
function used by the Riemann–Siegel formula.

## References

* E. C. Titchmarsh, *The Theory of the Riemann Zeta-Function*, 2nd ed. (revised by
  D. R. Heath-Brown), §4.17.
-/

public section

open Complex

namespace TauCeti

/-- **Hardy's function through the theta function.** Mathlib's `hardyZ t`, the quotient
`Λ(1/2 + it)/|Γℝ(1/2 + it)|`, is `e^{iϑ(t)} ζ(1/2 + it)`. -/
theorem ofReal_hardyZ_eq_exp_riemannSiegelTheta_mul (t : ℝ) :
    (hardyZ t : ℂ) = exp (riemannSiegelTheta t * I) * riemannZeta (1 / 2 + t * I) := by
  have hs : (1 / 2 + t * I : ℂ) ≠ 0 := fun h ↦ by simpa using congrArg re h
  rw [ofReal_hardyZ, riemannZeta_def_of_ne_zero hs]
  conv_rhs => rw [Gammaℝ_half_add_mul_I_eq_norm_mul_exp_riemannSiegelTheta]
  field_simp [exp_ne_zero]

end TauCeti
