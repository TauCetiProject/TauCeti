/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The Riemann zeta function at real arguments

For a real `s > 1`, Mathlib's `riemannZeta s` is the sum of the complex Dirichlet series
`∑ 1 / n ^ s`. This file records the corresponding statements for the real series: the real
`p`-series `∑ (n + 1) ^ (-s)` sums to the real part of `riemannZeta s`. Together with Mathlib's
`riemannZeta_re_pos_of_one_lt` and `riemannZeta_im_eq_zero_of_one_lt`, this identifies the
real normalizing constant of a `p`-series, as needed for the Zipf law on the positive integers.

The file also proves that `riemannZeta` is measurable, so that families of laws normalized by its
real values are measurable in their parameter.

## Main results

* `TauCeti.hasSum_nat_add_one_rpow_neg_riemannZeta_re`: `∑ (n + 1) ^ (-s) = Re ζ(s)` for `s > 1`;
* `TauCeti.hasSum_nat_rpow_neg_riemannZeta_re`: the same series indexed from `n = 0` with the
  vanishing term `0 ^ (-s)`;
* `TauCeti.measurable_riemannZeta`: the Riemann zeta function is measurable.
-/

public section

open Complex

namespace TauCeti

/-- For real `s > 1`, the real series `∑ (n + 1) ^ (-s)` sums to the real part of `riemannZeta s`.
-/
theorem hasSum_nat_add_one_rpow_neg_riemannZeta_re {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) ^ (-s)) (riemannZeta s).re := by
  have hsum : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-s) := by
    simpa using (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith : -s < -1))
  have hζ : riemannZeta s = ((∑' n : ℕ, ((n : ℝ) + 1) ^ (-s) : ℝ) : ℂ) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs), ofReal_tsum]
    congr 1 with n
    rw [ofReal_cpow (by positivity), one_div, ← cpow_neg]
    norm_cast
  rw [hζ, ofReal_re]
  exact hsum.hasSum

/-- For real `s > 1`, the real series `∑ n ^ (-s)` over all natural numbers sums to the real part of
`riemannZeta s`; its `n = 0` term is `0 ^ (-s) = 0`. -/
theorem hasSum_nat_rpow_neg_riemannZeta_re {s : ℝ} (hs : 1 < s) :
    HasSum (fun n : ℕ => (n : ℝ) ^ (-s)) (riemannZeta s).re := by
  rw [← hasSum_nat_add_iff' 1]
  simpa [Real.zero_rpow (by linarith : -s ≠ 0)] using
    hasSum_nat_add_one_rpow_neg_riemannZeta_re hs

/-- The Riemann zeta function is measurable: it is continuous away from its pole at `1`. -/
@[fun_prop]
theorem measurable_riemannZeta : Measurable riemannZeta :=
  measurable_of_continuousOn_compl_singleton 1 differentiableOn_riemannZeta.continuousOn

end TauCeti
