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
# Approximating holomorphic functions on a disc or bounded set by Taylor polynomials

A holomorphic function on an open disc `ball c s` in `ℂ`, with values in a complex Banach space,
is the uniform limit on every smaller closed disc `closedBall c r`, `r < s`, of the partial sums of
its Taylor series at `c`. These partial sums are polynomial in `z - c`, hence entire. So the
function is uniformly approximated on `closedBall c r` by entire functions. For a scalar entire
function `f : ℂ → ℂ`, its Taylor series at `0` has infinite radius of convergence, giving uniform
approximation by `Polynomial ℂ` on every bounded set `K ⊆ ℂ`
(`Differentiable.exists_polynomial_norm_sub_lt`).

This is the disc case of Runge's approximation theorem. It is the correction step in the
solution of the inhomogeneous Cauchy–Riemann equation on a disc by exhaustion, where local
solutions on an increasing sequence of discs are made to converge by subtracting entire
approximations of their holomorphic differences.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  proof of Theorem 13.2.
* A. Rainer, *Advanced Complex Analysis*, proof of Theorem 11.1.
-/

public section

open Metric
open scoped NNReal ENNReal

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- A holomorphic function on an open disc `ball c s` is approximated uniformly on every smaller
closed disc `closedBall c r`, `r < s`, by entire functions. -/
theorem DifferentiableOn.exists_differentiable_norm_sub_lt {h : ℂ → W} {c : ℂ} {r s ε : ℝ}
    (hh : DifferentiableOn ℂ h (ball c s)) (hrs : r < s) (hε : 0 < ε) :
    ∃ P : ℂ → W, Differentiable ℂ P ∧ ∀ z ∈ closedBall c r, ‖h z - P z‖ < ε := by
  rcases lt_or_ge r 0 with hr | hr
  · exact ⟨0, differentiable_const 0, by simp [closedBall_eq_empty.2 hr]⟩
  -- The Taylor series at `c` converges on `ball c t` and uniformly on `ball c t'`, where
  -- `r < t' < t < s`.
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
  set p := cauchyPowerSeries h c t
  refine ⟨fun z ↦ p.partialSum N (z - c), ?_, fun z hz ↦ ?_⟩
  · -- Each term `y ↦ p k (y, …, y)` of a partial sum is the diagonal of a multilinear map.
    have hd (k : ℕ) : Differentiable ℂ fun y : ℂ ↦ p k fun _ : Fin k ↦ y :=
      ((p k).contDiff.differentiable one_ne_zero).comp
        (differentiable_pi.2 fun _ ↦ differentiable_id)
    exact (Differentiable.fun_sum fun k _ ↦ hd k).comp (differentiable_id.sub_const c)
  · have hz' : ‖z - c‖ < t' := by
      rw [ht']
      linarith [show ‖z - c‖ ≤ r by simpa [dist_eq_norm] using hz]
    simpa [dist_eq_norm] using hN (z - c) (by simpa using hz')

/-- Every entire function `f : ℂ → ℂ` can be approximated uniformly on any bounded set `K ⊆ ℂ` by
polynomials in `Polynomial ℂ`. -/
theorem Differentiable.exists_polynomial_norm_sub_lt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {K : Set ℂ} (hK : Bornology.IsBounded K) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  obtain ⟨R₀, hR₀⟩ := hK.subset_ball 0
  set R : ℝ≥0 := (max R₀ 0).toNNReal
  have hR : (R : ℝ) = max R₀ 0 := Real.coe_toNNReal _ (le_max_right _ _)
  have hKsub : K ⊆ ball (0 : ℂ) R := fun w hw ↦
    ball_subset_ball (hR ▸ le_max_left _ _) (hR₀ hw)
  have hu := (hf.hasFPowerSeriesOnBall 0 zero_lt_one).tendstoUniformlyOn (r' := R)
    ENNReal.coe_lt_top
  obtain ⟨N, hN⟩ := (Metric.tendstoUniformlyOn_iff.1 hu ε hε).exists
  set q := cauchyPowerSeries f 0 1
  refine ⟨∑ n ∈ Finset.range N, Polynomial.C (q.coeff n) * Polynomial.X ^ n, fun z hz ↦ ?_⟩
  have hq_eval : (∑ n ∈ Finset.range N, Polynomial.C (q.coeff n) * Polynomial.X ^ n).eval z =
      q.partialSum N z := by
    rw [← Polynomial.coe_evalRingHom]
    simp only [map_sum, map_mul, map_pow, Polynomial.coe_evalRingHom,
      Polynomial.eval_C, Polynomial.eval_X, FormalMultilinearSeries.partialSum,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, mul_comm]
  rw [hq_eval]
  simpa [zero_add, dist_eq_norm, norm_sub_rev] using hN z (hKsub hz)
