/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.DiscSeries
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

/-!
# Polylogarithms on the closed unit disc, zeta values and the circle

In every weight `n ≥ 2` the polylogarithm series `∑_{k ≥ 0} z ^ (k + 1) / (k + 1) ^ n` is
dominated on the closed unit disc `‖z‖ ≤ 1` by the convergent `p`-series `∑ (k + 1) ^ (-n)`, and
it converges absolutely to the principal polylogarithm `Liₙ(z)` there
(`TauCeti.Polylog.hasSum_polylog_of_norm_le_one` and
`TauCeti.Polylog.hasSum_norm_polylog_of_norm_le_one`). This file draws the consequences:

* the partial sums converge uniformly to `Liₙ` on the closed unit disc, so `Liₙ` is continuous
  there, in particular at `1` for approach from inside the disc;
* the endpoint value is Riemann's zeta value, `Liₙ(1) = ζ(n)`, and so `Li₂(1) = π² / 6`;
* on the unit circle `Liₙ` is Mathlib's exponential zeta function:
  `Liₙ(exp (2 π i a)) = HurwitzZeta.expZeta a n` for every real `a`.

Weight one is excluded throughout: `Li₁(z) = -Log (1 - z)` is unbounded as `z → 1` inside the
disc, whatever its totalised value at `1`. Conjugation symmetry on the closed disc is
`TauCeti.Polylog.polylog_conj_of_re_le_one`.

## Main results

* `TauCeti.Polylog.tendstoUniformlyOn_polylog_closedBall_one`: uniform convergence of the disc
  series on `Metric.closedBall 0 1` for `n ≥ 2`.
* `TauCeti.Polylog.continuousOn_polylog_closedBall_one`: continuity of `polylog n` on the closed
  unit disc for `n ≥ 2`.
* `TauCeti.Polylog.polylog_eq_riemannZeta`: `polylog n 1 = riemannZeta n` for `n ≥ 2`.
* `TauCeti.Polylog.polylog_two_one`: `polylog 2 1 = π ^ 2 / 6`.
* `TauCeti.Polylog.polylog_exp_eq_expZeta`: `polylog n (exp (2 π i a)) = expZeta a n` for
  `n ≥ 2` and real `a`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §1.4, p. 51.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics, and Geometry II
  (2007), Part I, §1, p. 6.
-/

public section

open Filter Metric Set

namespace TauCeti.Polylog

/-- **Uniform convergence on the closed unit disc.** In every weight `n ≥ 2`, the partial sums of
the polylogarithm power series converge uniformly to `polylog n` on `Metric.closedBall 0 1`. -/
theorem tendstoUniformlyOn_polylog_closedBall_one {n : ℤ} (hn : 2 ≤ n) :
    TendstoUniformlyOn
      (fun N (z : ℂ) ↦ ∑ k ∈ Finset.range N, z ^ (k + 1) / (k + 1 : ℂ) ^ n)
      (polylog n) atTop (closedBall 0 1) := by
  have hu := (hasSum_norm_polylog_of_norm_le_one hn (z := 1) (by simp)).summable
  refine (tendstoUniformlyOn_tsum_nat hu fun k z hz ↦ ?_).congr_right fun z hz ↦
    (polylog_eq_tsum_of_norm_le_one hn (mem_closedBall_zero_iff.mp hz)).symm
  simp only [norm_div, norm_pow, norm_one, one_pow]
  gcongr
  exact pow_le_one₀ (norm_nonneg z) (mem_closedBall_zero_iff.mp hz)

/-- **Closed-disc continuity.** In every weight `n ≥ 2`, `polylog n` is continuous on the closed
unit disc, in particular at `1` for approach from inside the disc. -/
theorem continuousOn_polylog_closedBall_one {n : ℤ} (hn : 2 ≤ n) :
    ContinuousOn (polylog n) (closedBall 0 1) :=
  (tendstoUniformlyOn_polylog_closedBall_one hn).continuousOn
    (Frequently.of_forall fun _ ↦ by fun_prop)

/-- **Zeta values.** In every weight `n ≥ 2`, the polylogarithm at `1` is Riemann's zeta value:
`Liₙ(1) = ζ(n)`. -/
theorem polylog_eq_riemannZeta {n : ℤ} (hn : 2 ≤ n) : polylog n 1 = riemannZeta n := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [Complex.intCast_re]; exact_mod_cast hn),
    polylog_eq_tsum_of_norm_le_one hn (by simp)]
  simp only [one_pow, Complex.cpow_intCast]

/-- Euler's value of the dilogarithm at `1`: `Li₂(1) = ζ(2) = π ^ 2 / 6`. -/
theorem polylog_two_one : polylog 2 1 = (Real.pi : ℂ) ^ 2 / 6 := by
  rw [polylog_eq_riemannZeta le_rfl, Int.cast_ofNat, riemannZeta_two]

/-- **Circle values.** In every weight `n ≥ 2`, the polylogarithm on the unit circle is Mathlib's
exponential zeta function: `Liₙ(exp (2 π i a)) = ∑_{k ≥ 1} exp (2 π i a k) / k ^ n = expZeta a n`
for every real `a`. -/
theorem polylog_exp_eq_expZeta {n : ℤ} (hn : 2 ≤ n) (a : ℝ) :
    polylog n (Complex.exp (2 * Real.pi * Complex.I * a)) =
      HurwitzZeta.expZeta (a : UnitAddCircle) n := by
  have hz : ‖Complex.exp (2 * Real.pi * Complex.I * a)‖ ≤ 1 := by
    rw [Complex.norm_exp]
    simp
  have h := (hasSum_nat_add_iff' 1).mpr
    (HurwitzZeta.hasSum_expZeta_of_one_lt_re a (by rw [Complex.intCast_re]; exact_mod_cast hn))
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, mul_zero, Complex.exp_zero,
    Complex.zero_cpow hn0, div_zero, sub_zero] at h
  refine (hasSum_polylog_of_norm_le_one hn hz).unique (h.congr_fun fun k ↦ ?_)
  rw [Complex.cpow_intCast, ← Complex.exp_nat_mul]
  push_cast
  congr 2
  ring

end TauCeti.Polylog
