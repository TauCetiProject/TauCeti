/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Analytic.ConvergenceRadius
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Approximating holomorphic functions on a disc or bounded set by Taylor polynomials

A holomorphic function on an open disc `ball c s` in `ℂ`, with values in a complex Banach space,
is the uniform limit on every smaller closed disc `closedBall c r`, `r < s`, of the partial sums of
its Taylor series at `c` (`DifferentiableOn.exists_partialSum_norm_sub_lt`). These partial sums are
polynomial in `z - c`, hence entire, so the function is uniformly approximated on `closedBall c r`
by entire functions (`DifferentiableOn.exists_differentiable_norm_sub_lt`) and, for scalar targets,
by complex polynomials (`DifferentiableOn.exists_polynomial_norm_sub_lt`). In particular, every
entire function `f : ℂ → ℂ` is uniformly approximated by `Polynomial ℂ` on every bounded set
`K ⊆ ℂ` (`Differentiable.exists_polynomial_norm_sub_lt`).

This is the disc case of Runge's approximation theorem. It is the correction step in the
solution of the inhomogeneous Cauchy–Riemann equation on a disc by exhaustion, where local
solutions on an increasing sequence of discs are made to converge by subtracting entire
approximations of their holomorphic differences.

## Main results

* `DifferentiableOn.exists_partialSum_norm_sub_lt`: uniform approximation on `closedBall c r`
  (`r < s`) by partial sums of a formal multilinear power series centred at `c`.
* `DifferentiableOn.exists_differentiable_norm_sub_lt`: uniform approximation on `closedBall c r`
  (`r < s`) by entire Banach-valued functions.
* `DifferentiableOn.exists_polynomial_norm_sub_lt`: uniform approximation on `closedBall c r`
  (`r < s`) of a scalar holomorphic function on `ball c s` by `Polynomial ℂ`.
* `Differentiable.exists_polynomial_norm_sub_lt`: uniform approximation of an entire scalar
  function on any bounded subset of `ℂ` by `Polynomial ℂ`.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  proof of Theorem 13.2.
* A. Rainer, *Advanced Complex Analysis*, proof of Theorem 11.1.
* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 10.16.
-/

public section

open Metric Polynomial
open scoped NNReal ENNReal

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]

/-- A holomorphic function on an open disc `ball c s` is approximated uniformly on every smaller
closed disc `closedBall c r`, `r < s`, by partial sums of a formal multilinear power series centred
at `c`. -/
theorem DifferentiableOn.exists_partialSum_norm_sub_lt {h : ℂ → W} {c : ℂ} {r s ε : ℝ}
    (hh : DifferentiableOn ℂ h (ball c s)) (hrs : r < s) (hε : 0 < ε) :
    ∃ (p : FormalMultilinearSeries ℂ ℂ W) (N : ℕ),
      ∀ z ∈ closedBall c r, ‖h z - p.partialSum N (z - c)‖ < ε := by
  rcases lt_or_ge r 0 with hr | hr
  · exact ⟨0, 0, by simp [closedBall_eq_empty.2 hr]⟩
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
  refine ⟨cauchyPowerSeries h c t, N, fun z hz ↦ ?_⟩
  have hz' : ‖z - c‖ < t' := by
    rw [ht']
    linarith [show ‖z - c‖ ≤ r by simpa [dist_eq_norm] using hz]
  simpa [dist_eq_norm, norm_sub_rev] using hN (z - c) (by simpa using hz')

/-- A holomorphic function on an open disc `ball c s` is approximated uniformly on every smaller
closed disc `closedBall c r`, `r < s`, by entire functions. -/
theorem DifferentiableOn.exists_differentiable_norm_sub_lt {h : ℂ → W} {c : ℂ} {r s ε : ℝ}
    (hh : DifferentiableOn ℂ h (ball c s)) (hrs : r < s) (hε : 0 < ε) :
    ∃ P : ℂ → W, Differentiable ℂ P ∧ ∀ z ∈ closedBall c r, ‖h z - P z‖ < ε := by
  obtain ⟨p, N, hN⟩ := hh.exists_partialSum_norm_sub_lt hrs hε
  refine ⟨fun z ↦ p.partialSum N (z - c), ?_, hN⟩
  -- Each term `y ↦ p k (y, …, y)` of a partial sum is the diagonal of a multilinear map.
  have hd (k : ℕ) : Differentiable ℂ fun y : ℂ ↦ p k fun _ : Fin k ↦ y :=
    ((p k).contDiff.differentiable one_ne_zero).comp
      (differentiable_pi.2 fun _ ↦ differentiable_id)
  exact (Differentiable.fun_sum fun k _ ↦ hd k).comp (differentiable_id.sub_const c)

/-- A scalar holomorphic function `h : ℂ → ℂ` on an open disc `ball c s` is approximated uniformly
on every smaller closed disc `closedBall c r`, `r < s`, by complex polynomials. -/
theorem DifferentiableOn.exists_polynomial_norm_sub_lt {h : ℂ → ℂ} {c : ℂ} {r s ε : ℝ}
    (hh : DifferentiableOn ℂ h (ball c s)) (hrs : r < s) (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ closedBall c r, ‖h z - p.eval z‖ < ε := by
  obtain ⟨q, N, hN⟩ := hh.exists_partialSum_norm_sub_lt hrs hε
  refine ⟨∑ k ∈ Finset.range N, C (q.coeff k) * (X - C c) ^ k, fun z hz ↦ ?_⟩
  have heval : (∑ k ∈ Finset.range N, C (q.coeff k) * (X - C c) ^ k).eval z =
      q.partialSum N (z - c) := by
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X,
      FormalMultilinearSeries.partialSum, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
  rw [heval]
  exact hN z hz

/-- Every entire function `f : ℂ → ℂ` can be approximated uniformly on any bounded set `K ⊆ ℂ` by
polynomials in `Polynomial ℂ`. -/
theorem Differentiable.exists_polynomial_norm_sub_lt {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    {K : Set ℂ} (hK : Bornology.IsBounded K) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : Polynomial ℂ, ∀ z ∈ K, ‖f z - p.eval z‖ < ε := by
  obtain ⟨R, hR⟩ := hK.subset_closedBall 0
  obtain ⟨p, hp⟩ := hf.differentiableOn.exists_polynomial_norm_sub_lt
    (c := 0) (r := R) (s := R + 1) (lt_add_one R) hε
  exact ⟨p, fun z hz ↦ hp z (hR hz)⟩
