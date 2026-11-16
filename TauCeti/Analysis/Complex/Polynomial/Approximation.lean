/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import TauCeti.Analysis.Complex.PowerSeries.Approximation

/-!
# Uniform polynomial approximation of holomorphic functions on discs and of entire functions

A complex-valued function `h : ℂ → ℂ` holomorphic on an open disc `ball c s` is uniformly
approximated on every smaller closed disc `closedBall c r`, `r < s`, by complex polynomials
`P : ℂ[X]` (`DifferentiableOn.exists_polynomial_norm_sub_lt`). In particular, every entire function
is uniformly approximated on every compact subset of `ℂ` by complex polynomials
(`Differentiable.exists_polynomial_norm_sub_lt`).

This refines the Banach-space entire-approximation theorem
`DifferentiableOn.exists_differentiable_norm_sub_lt` in
`TauCeti/Analysis/Complex/PowerSeries/Approximation.lean` for scalar targets by producing an
explicit polynomial `P : ℂ[X]`, linking entire holomorphic hulls in `ℂ` with polynomial hulls
(`TauCeti.polynomialHull`) and yielding the polynomial form of Runge's theorem on compact sets with
connected complement.

## Main results

* `DifferentiableOn.exists_polynomial_norm_sub_lt`: uniform polynomial approximation on smaller
  closed discs inside a disc of holomorphy.
* `Differentiable.exists_polynomial_norm_sub_lt`: uniform polynomial approximation of an entire
  function on any compact subset of `ℂ`.

## References

* W. Rudin, *Real and Complex Analysis*, 3rd ed., Theorem 10.16 and Theorem 13.7.
-/

public section

open Metric Polynomial

/-- A holomorphic function `h : ℂ → ℂ` on an open disc `ball c s` is approximated uniformly on every
smaller closed disc `closedBall c r`, `r < s`, by complex polynomials. -/
theorem DifferentiableOn.exists_polynomial_norm_sub_lt {h : ℂ → ℂ} {c : ℂ} {r s ε : ℝ}
    (hh : DifferentiableOn ℂ h (ball c s)) (hrs : r < s) (hε : 0 < ε) :
    ∃ P : ℂ[X], ∀ z ∈ closedBall c r, ‖h z - P.eval z‖ < ε := by
  obtain ⟨p, N, hN⟩ := hh.exists_partialSum_norm_sub_lt hrs hε
  refine ⟨∑ k ∈ Finset.range N, C (p k fun _ : Fin k ↦ 1) * (X - C c) ^ k, fun z hz ↦ ?_⟩
  have heval : (∑ k ∈ Finset.range N, C (p k fun _ : Fin k ↦ 1) * (X - C c) ^ k).eval z =
      p.partialSum N (z - c) := by
    simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_sub, eval_X,
      FormalMultilinearSeries.partialSum]
    exact Finset.sum_congr rfl fun k _ ↦ by simp [mul_comm]
  rw [heval]
  exact hN z hz

/-- Every entire function `h : ℂ → ℂ` is uniformly approximated on any compact set `K ⊆ ℂ` by
complex polynomials. -/
theorem Differentiable.exists_polynomial_norm_sub_lt {h : ℂ → ℂ} (hh : Differentiable ℂ h)
    {K : Set ℂ} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : ℂ[X], ∀ z ∈ K, ‖h z - P.eval z‖ < ε := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  obtain ⟨P, hP⟩ := hh.differentiableOn.exists_polynomial_norm_sub_lt
    (c := 0) (r := R) (s := R + 1) (lt_add_one R) hε
  exact ⟨P, fun z hz ↦ hP z (hR hz)⟩
