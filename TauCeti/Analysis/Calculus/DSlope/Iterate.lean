/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# Finite expansions by iterated divided slopes

Iterating `Function.swap dslope a` expands any function `f : 𝕜 → E` around `a` as a polynomial in
`z - a` plus a remainder:
`f z = ∑ j < n, (z - a) ^ j • (dslope^[j] f) a + (z - a) ^ n • (dslope^[n] f) z`.
This identity is pure algebra: it is `sub_smul_dslope` applied `n` times, with no regularity of
`f`. When `f` has the power series `p` at `a`, the coefficients `(dslope^[j] f) a` are the Taylor
coefficients `p.coeff j`, and the remainder `dslope^[n] f` is analytic at `a`
(`HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope`). So this is the splitting of a
convergent power series into its part of degree below `n` and `(z - a) ^ n` times an analytic
function.

## Main results

* `TauCeti.sum_range_pow_smul_iterate_dslope_add`: the finite expansion by iterated divided slopes.
* `HasFPowerSeriesAt.iterate_dslope_eq_coeff`: its coefficients are the Taylor coefficients.
-/

public section

open Function

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Every function is a polynomial of degree below `n` in `z - a`, with the values at `a` of its
iterated divided slopes as coefficients, plus `(z - a) ^ n` times its `n`-th iterated divided
slope. -/
theorem TauCeti.sum_range_pow_smul_iterate_dslope_add (f : 𝕜 → E) (a z : 𝕜) (n : ℕ) :
    ∑ j ∈ Finset.range n, (z - a) ^ j • (swap dslope a)^[j] f a +
      (z - a) ^ n • (swap dslope a)^[n] f z = f z := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := sub_smul_dslope ((swap dslope a)^[n] f) a z
    rw [Finset.sum_range_succ, iterate_succ_apply', swap, pow_succ, mul_smul, h, smul_sub,
      add_assoc, add_sub_cancel, ih]

/-- If `f` has the power series `p` at `a`, then the `j`-th iterated divided slope of `f` at `a`
takes the value `p.coeff j` at `a`. -/
theorem HasFPowerSeriesAt.iterate_dslope_eq_coeff {f : 𝕜 → E} {p : FormalMultilinearSeries 𝕜 𝕜 E}
    {a : 𝕜} (hp : HasFPowerSeriesAt f p a) (j : ℕ) :
    (swap dslope a)^[j] f a = p.coeff j := by
  rw [← (hp.has_fpower_series_iterate_dslope_fslope j).coeff_zero 1,
    ← FormalMultilinearSeries.coeff, FormalMultilinearSeries.coeff_iterate_fslope, zero_add]
