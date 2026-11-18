/-
Copyright (c) 2026 The PrimeNumberTheoremAnd contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The PrimeNumberTheoremAnd contributors
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import TauCeti.NumberTheory.ArithmeticFunction.Defs
import TauCeti.NumberTheory.LSeries.Convolution

/-!
# The Dirichlet series of the `k`-fold divisor function

For `k : ℕ`, the Dirichlet-convolution power `ζ ^ k` of the arithmetic function
`ArithmeticFunction.zeta` is the `k`-fold divisor function `d_k`: `d_k n` counts the ordered
`k`-tuples of positive integers with product `n`. On `Re s > 1` its Dirichlet series converges
absolutely and has sum `riemannZeta s ^ k`. At `k = 0` both sides are `1`.

## Main results

* `ArithmeticFunction.LSeriesHasSum_zeta_pow`: for `Re s > 1`, the Dirichlet series of `ζ ^ k`
  has sum `riemannZeta s ^ k`.
* `ArithmeticFunction.summable_norm_term_zeta_pow`: for `Re s > 1`, the Dirichlet series of
  `ζ ^ k` converges absolutely.

Both follow from Mathlib's `ArithmeticFunction.LSeriesHasSum_zeta` by
`ArithmeticFunction.LSeriesHasSum_pow`.

## References

The statement corresponds to `LSeriesSummable_zeta_pow` and
`LSeries_zeta_pow_eq_riemannZeta_pow` in
[Alex Kontorovich, Terence Tao and contributors, *Prime Number Theorem and More*][PNT].

[PNT]: https://github.com/TauCetiProject/PrimeNumberTheoremAnd/blob/5fae9883a8ea055caa79cc4d73717b3b690d22fc/PrimeNumberTheoremAnd/IwaniecKowalskiCh1.lean#L273-L311
-/

public section

namespace ArithmeticFunction

open scoped ArithmeticFunction.zeta LSeries.notation

/-- **The Dirichlet series of `d_k = ζ ^ k`.** For every `k : ℕ` and `Re s > 1`, the Dirichlet
series of the `k`-fold divisor function `ζ ^ k` has sum `riemannZeta s ^ k`. Here `ζ` is the
arithmetic function, not `riemannZeta`. -/
theorem LSeriesHasSum_zeta_pow (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n ↦ ((ζ ^ k : ArithmeticFunction ℕ) n : ℂ)) s (riemannZeta s ^ k) := by
  have hζ : LSeriesHasSum ↗(ζ : ArithmeticFunction ℂ) s (riemannZeta s) := by
    simpa only [natCoe_apply] using LSeriesHasSum_zeta hs
  simpa only [← natCoe_pow, natCoe_apply] using LSeriesHasSum_pow hζ k

/-- For every `k : ℕ` and `Re s > 1`, the Dirichlet series of the `k`-fold divisor function
`ζ ^ k` converges absolutely. -/
theorem summable_norm_term_zeta_pow (k : ℕ) {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ ↦
      ‖LSeries.term (fun n ↦ ((ζ ^ k : ArithmeticFunction ℕ) n : ℂ)) s n‖ := by
  have h := (LSeriesHasSum_zeta_pow k hs).LSeriesSummable
  rw [LSeriesSummable] at h
  exact summable_norm_iff.mpr h

end ArithmeticFunction
