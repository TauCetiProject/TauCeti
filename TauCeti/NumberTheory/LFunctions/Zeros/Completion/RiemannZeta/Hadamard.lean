/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Hadamard.OrderOne
public import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Basic

import TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard
import TauCeti.NumberTheory.LFunctions.Zeros.Completion.RiemannZeta.Growth

/-!
# Hadamard factorization and logarithmic derivative of the completed Riemann zeta function

Combining `orderLE_zetaEntireCompletion`, `zetaEntireCompletion 0 = 1`, nonvanishing on `1 ≤ Re s`
(`zetaEntireCompletion_ne_zero_of_one_le_re`), and the record-level real-part cancellation theorems
of `TauCeti.NumberTheory.LFunctions.Zeros.Completion.Hadamard` specializes Hadamard factorization
and constant-free real-part expansion to twice Riemann's ξ-function `zetaEntireCompletion`:

* **Hadamard factorization** (`zetaEntireCompletion_hadamard`): `zetaEntireCompletion` factors
  globally as `exp (a + b * s)` times the multipliable genus-one canonical product over its zeros.
* **Cancelled real-part expansion** (`re_logDeriv_zetaEntireCompletion_zero`,
  `re_logDeriv_zetaEntireCompletion_eq_tsum`): `(logDeriv zetaEntireCompletion 0).re =`
  `-∑' ρ, m_ρ * Re (1 / ρ)`, so off the zeros `Re (logDeriv zetaEntireCompletion s)` equals
  `∑' ρ, m_ρ * Re (1 / (s - ρ))` with no additive constant.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., §11 and §12.
* H. L. Montgomery and R. C. Vaughan, *Multiplicative Number Theory I* (2006), §10.2 and §11.1.
* E. C. Titchmarsh, rev. D. R. Heath-Brown, *The Theory of the Riemann Zeta-Function*, 2nd ed.,
  §2.12.
-/

public section

open Complex

namespace TauCeti.LFunctions

/-- **Hadamard product for `zetaEntireCompletion`.** Twice Riemann's ξ-function factors globally as
`exp (a + b * s)` times the multipliable genus-one canonical product over its zeros, with
`exp a = zetaEntireCompletion 0` and `b = logDeriv zetaEntireCompletion 0`. -/
theorem zetaEntireCompletion_hadamard :
    ∃ a b : ℂ, exp a = zetaEntireCompletion 0 ∧ b = logDeriv zetaEntireCompletion 0 ∧ ∀ s : ℂ,
      Multipliable (fun ρ : ℂ ↦
        weierstrassFactor 1 (ρ⁻¹ * s) ^
          (MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat) ∧
      zetaEntireCompletion s = exp (a + b * s) * ∏' ρ : ℂ,
        weierstrassFactor 1 (ρ⁻¹ * s) ^
          (MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat :=
  hadamard_of_orderLE_one orderLE_zetaEntireCompletion differentiable_zetaEntireCompletion (by simp)

/-- The real part of the Hadamard linear constant `logDeriv zetaEntireCompletion 0` equals
`-∑' ρ, m_ρ * Re (1 / ρ)`. -/
theorem re_logDeriv_zetaEntireCompletion_zero :
    (logDeriv zetaEntireCompletion 0).re =
      -∑' ρ : (MeromorphicOn.divisor zetaEntireCompletion Set.univ).support,
        ((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℝ) * (1 / (ρ : ℂ)).re := by
  rw [← riemannZetaData_entireCompletion]
  exact riemannZetaData_hasFunctionalEquation.re_logDeriv_entireCompletion_zero
    riemannZetaData_hasMeromorphicContinuation
    (by rw [riemannZetaData_entireCompletion]; exact orderLE_zetaEntireCompletion)
    (fun z hz ↦ by
      rw [riemannZetaData_entireCompletion]
      exact zetaEntireCompletion_ne_zero_of_one_le_re hz)

/-- Cancelled real-part partial-fraction expansion of `logDeriv zetaEntireCompletion` off the
zeros: `Re (logDeriv zetaEntireCompletion s) = ∑' ρ, m_ρ * Re (1 / (s - ρ))`. -/
theorem re_logDeriv_zetaEntireCompletion_eq_tsum {s : ℂ} (hs : zetaEntireCompletion s ≠ 0) :
    (logDeriv zetaEntireCompletion s).re =
      ∑' ρ : (MeromorphicOn.divisor zetaEntireCompletion Set.univ).support,
        ((MeromorphicOn.divisor zetaEntireCompletion Set.univ ρ).toNat : ℝ) *
          (1 / (s - ρ)).re := by
  rw [← riemannZetaData_entireCompletion] at hs ⊢
  exact riemannZetaData_hasFunctionalEquation.re_logDeriv_entireCompletion_eq_tsum
    riemannZetaData_hasMeromorphicContinuation
    (by rw [riemannZetaData_entireCompletion]; exact orderLE_zetaEntireCompletion)
    (fun z hz ↦ by
      rw [riemannZetaData_entireCompletion]
      exact zetaEntireCompletion_ne_zero_of_one_le_re hz) hs

end TauCeti.LFunctions
