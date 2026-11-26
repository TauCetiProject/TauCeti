/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Liouville
public import TauCeti.NumberTheory.LSeries.Totient
public import TauCeti.NumberTheory.LSeries.TwoPowOmega
import TauCeti.NumberTheory.LSeries.RiemannZeta.EulerProduct

/-!
# The series of `2^ω`, `μ²`, `λ` and `φ` as quotients of zeta values

For `Re s > 1`, the Dirichlet series of `2^{ω(n)}`, `μ(n)²` and `λ(n)` are `ζ(s)² / ζ(2s)`,
`ζ(s) / ζ(2s)` and `ζ(2s) / ζ(s)`, and for `Re s > 2` the series of `φ(n)` is
`ζ(s - 1) / ζ(s)`. Their abscissas of absolute convergence are `1`, `1`, `1` and `2`.

The coefficient functions are Mathlib's `ArithmeticFunction.cardDistinctFactors` (in
`n ↦ 2^{ω(n)}`), `ArithmeticFunction.moebius`, `ArithmeticFunction.liouville` and `Nat.totient`,
cast to `ℂ`. Each statement collects the corresponding results for the individual series, which
are proved through Euler products and Dirichlet convolution in the files imported here.

## Main results

* `TauCeti.LSeries_two_pow_omega_moebius_sq_liouville`: the three quotients on `Re s > 1`.
* `TauCeti.abscissaOfAbsConv_two_pow_omega_moebius_sq_liouville_totient`: the four abscissas.

The series of `φ` alone is `TauCeti.LSeries_totient`.

## References

* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, AMS Colloquium Publications 53 (2004),
  (1.31)–(1.33) and (1.35).
* T. M. Apostol, *Introduction to Analytic Number Theory*, Springer (1976), Chapter 11.
-/

public section

open ArithmeticFunction

namespace TauCeti

/-- For `Re s > 1`, `Σ 2^{ω(n)} n^{-s} = ζ(s)² / ζ(2s)`, `Σ μ(n)² n^{-s} = ζ(s) / ζ(2s)` and
`Σ λ(n) n^{-s} = ζ(2s) / ζ(s)`. -/
theorem LSeries_two_pow_omega_moebius_sq_liouville {s : ℂ} (hs : 1 < s.re) :
    _root_.LSeries (fun n ↦ (2 : ℂ) ^ cardDistinctFactors n) s =
        riemannZeta s ^ 2 / riemannZeta (2 * s) ∧
      _root_.LSeries (fun n ↦ (moebius n : ℂ) ^ 2) s = riemannZeta s / riemannZeta (2 * s) ∧
      _root_.LSeries (fun n ↦ (liouville n : ℂ)) s = riemannZeta (2 * s) / riemannZeta s := by
  refine ⟨(LSeriesHasSum_two_pow_cardDistinctFactors hs).LSeries_eq,
    (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re (one_lt_re_two_mul hs))).mpr ?_,
    (LSeriesHasSum_liouville hs).LSeries_eq⟩
  rw [mul_comm, ← riemannZeta_eq_mul_LSeries_moebius_sq hs]

/-- The abscissas of absolute convergence of the Dirichlet series of `2^ω`, `μ²`, `λ` and `φ`
are `1`, `1`, `1` and `2`. -/
theorem abscissaOfAbsConv_two_pow_omega_moebius_sq_liouville_totient :
    _root_.LSeries.abscissaOfAbsConv (fun n ↦ (2 : ℂ) ^ cardDistinctFactors n) = 1 ∧
      _root_.LSeries.abscissaOfAbsConv (fun n ↦ (moebius n : ℂ) ^ 2) = 1 ∧
      _root_.LSeries.abscissaOfAbsConv (fun n ↦ (liouville n : ℂ)) = 1 ∧
      _root_.LSeries.abscissaOfAbsConv (fun n ↦ (n.totient : ℂ)) = 2 :=
  ⟨abscissaOfAbsConv_two_pow_cardDistinctFactors, abscissaOfAbsConv_moebius_sq,
    abscissaOfAbsConv_liouville, abscissaOfAbsConv_totient⟩

end TauCeti
