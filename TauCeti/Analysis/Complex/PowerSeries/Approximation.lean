/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Approximating holomorphic functions on a disc by entire functions and polynomials

A holomorphic function on an open disc `ball c s` in `ℂ`, with values in a complex Banach space,
is the uniform limit on every smaller closed disc `closedBall c r`, `r < s`, of the partial sums of
its Taylor series at `c`. These partial sums are polynomial in `z - c`, hence entire. So the
function is uniformly approximated on `closedBall c r` by entire functions, and when it is
scalar-valued, by complex polynomials (`DifferentiableOn.exists_polynomial_norm_sub_lt`); in
particular, an entire scalar function is uniformly approximated by polynomials on every bounded set
(`Differentiable.exists_polynomial_norm_sub_lt`).

This is the disc case of Runge's approximation theorem. It is the correction step in the
solution of the inhomogeneous Cauchy–Riemann equation on a disc by exhaustion, where local
solutions on an increasing sequence of discs are made to converge by subtracting entire
approximations of their holomorphic differences.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  proof of Theorem 13.2.
-/

public section

open Metric
open scoped NNReal

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- On `closedBall c r` (`0 ≤ r < s`), a Taylor partial sum of a function holomorphic on
`ball c s` approximates it uniformly within `ε`. -/
private theorem exists_cauchyPowerSeries_partialSum_norm_sub_lt {h : ℂ → W} {c : ℂ}
    {r s ε : ℝ} (hh : DifferentiableOn ℂ h (ball c s)) (hr : 0 ≤ r) (hrs : r < s)
    (hε : 0 < ε) :
    ∃ (t : ℝ≥0) (N : ℕ), ∀ z ∈ closedBall c r,
      ‖h z - (cauchyPowerSeries h c t).partialSum N (z - c)‖ < ε := by
  set t : ℝ≥0 := ((r + s) / 2).toNNReal
  have ht : (t : ℝ) = (r + s) / 2 := Real.coe_toNNReal _ (by linarith)
  set t' : ℝ≥0 := ((3 * r + s) / 4).toNNReal
  have ht' : (t' : ℝ) = (3 * r + s) / 4 := Real.coe_toNNReal _ (by linarith)
  have hps := DifferentiableOn.hasFPowerSeriesOnBall
    (hh.mono (closedBall_subset_ball (by rw [ht]; linarith)))
    (by rw [← NNReal.coe_pos, ht]; linarith)
  have hu := hps.tendstoUniformlyOn (r' := t')
    (ENNReal.coe_lt_coe.2 (by rw [← NNReal.coe_lt_coe, ht, ht']; linarith))
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 hu ε hε).exists
  refine ⟨t, N, fun z hz ↦ ?_⟩
  have hz' : ‖z - c‖ < t' := by
    have hzr : ‖z - c‖ ≤ r := by simpa [dist_eq_norm] using hz
    rw [ht']
    linarith
  simpa [dist_eq_norm] using hN (z - c) (by simpa using hz')

/-- A holomorphic function on an open disc `ball c s` is approximated uniformly on every smaller
closed disc `closedBall c r`, `r < s`, by entire functions. -/
theorem DifferentiableOn.exists_differentiable_norm_sub_lt {h : ℂ → W} {c : ℂ} {r s ε : ℝ}
    (hh : DifferentiableOn ℂ h (ball c s)) (hrs : r < s) (hε : 0 < ε) :
    ∃ P : ℂ → W, Differentiable ℂ P ∧ ∀ z ∈ closedBall c r, ‖h z - P z‖ < ε := by
  rcases lt_or_ge r 0 with hr | hr
  · exact ⟨0, differentiable_const 0, by simp [closedBall_eq_empty.2 hr]⟩
  obtain ⟨t, N, hN⟩ := exists_cauchyPowerSeries_partialSum_norm_sub_lt hh hr hrs hε
  set p := cauchyPowerSeries h c t
  refine ⟨fun z ↦ p.partialSum N (z - c), ?_, hN⟩
  have hd (k : ℕ) : Differentiable ℂ fun y : ℂ ↦ p k fun _ : Fin k ↦ y :=
    ((p k).contDiff.differentiable one_ne_zero).comp
      (differentiable_pi.2 fun _ ↦ differentiable_id)
  exact (Differentiable.fun_sum fun k _ ↦ hd k).comp (differentiable_id.sub_const c)

/-- A scalar holomorphic function on an open disc `ball c s` is approximated uniformly on every
smaller closed disc `closedBall c r`, `r < s`, by complex polynomials. -/
theorem DifferentiableOn.exists_polynomial_norm_sub_lt {h : ℂ → ℂ} {c : ℂ} {r s ε : ℝ}
    (hh : DifferentiableOn ℂ h (ball c s)) (hrs : r < s) (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ closedBall c r, ‖h z - p.eval z‖ < ε := by
  rcases lt_or_ge r 0 with hr | hr
  · exact ⟨0, by simp [closedBall_eq_empty.2 hr]⟩
  obtain ⟨t, N, hN⟩ := exists_cauchyPowerSeries_partialSum_norm_sub_lt hh hr hrs hε
  set q := cauchyPowerSeries h c t
  refine ⟨∑ k ∈ Finset.range N,
      Polynomial.C (q k fun _ ↦ 1) * (Polynomial.X - Polynomial.C c) ^ k, fun z hz ↦ ?_⟩
  have heval : (∑ k ∈ Finset.range N,
      Polynomial.C (q k fun _ ↦ 1) * (Polynomial.X - Polynomial.C c) ^ k).eval z =
      q.partialSum N (z - c) := by
    rw [Polynomial.eval_finsetSum, FormalMultilinearSeries.partialSum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    have hmul : (fun _ : Fin k ↦ z - c) = fun _ : Fin k ↦ (z - c) • (1 : ℂ) := by simp
    rw [hmul, (q k).map_smul_univ]
    simp [mul_comm]
  rw [heval]
  exact hN z hz

/-- An entire scalar function is approximated uniformly on every bounded subset of `ℂ` by complex
polynomials. -/
theorem Differentiable.exists_polynomial_norm_sub_lt {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {K : Set ℂ} (hK : Bornology.IsBounded K) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖h z - p.eval z‖ < ε := by
  obtain ⟨r, hr⟩ := hK.subset_closedBall 0
  obtain ⟨p, hp⟩ := hh.differentiableOn.exists_polynomial_norm_sub_lt (lt_add_one r) hε
  exact ⟨p, fun z hz ↦ hp z (hr hz)⟩
