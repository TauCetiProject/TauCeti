/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
import TauCeti.NumberTheory.LSeries.Term

/-!
# Gaussian cutoffs for Dirichlet series

On the circle of radius `1 / X`, the real part of the quadratic term in the Gaussian
weight shifts the logarithmic cutoff `U` by a real number in `[0, X²]`. This gives a
common majorant at the real point `1 + 1 / U` for two sums used in the short-window
prime argument: the initial Dirichlet polynomial on the left of that point and
the tail beyond the window on its right.

The comparison uses absolute convergence at the reference point. In the tail
application it also supplies absolute convergence of the restricted series.

## Main definitions and results

* `TauCeti.LSeries.gaussianShift`: the displacement `X ^ 2 / 2 * (1 + X * z.re)` induced by the
  Gaussian weight on the circle `‖X * z‖ = 1`, with defining equation `gaussianShift_def`.
* `TauCeti.LSeries.gaussianShift_mem_Icc`: on `‖X * z‖ ≤ 1`, `gaussianShift X z ∈ [0, X²]`.
* `TauCeti.LSeries.re_gaussian_eq`: on `‖X * z‖ = 1`, the real part of the Gaussian exponent
  equals `2 - (U + gaussianShift X z) * z.re`.
* `TauCeti.LSeries.exists_hasSum_term_gaussian_bound`: majorizes a restricted Dirichlet series at
  `1 + z` by its absolute sum at `1 + 1 / U` times the Gaussian factor.

## References

* L. Alpöge, Lean formalization of the Riemann hypothesis for Dirichlet `L`-functions,
  `New.norm_sub_mul_sum_term_le` and the Gaussian cutoff steps in `src/Lib/Analytic/Primes.lean`,
  <https://github.com/leanprover-community/riemann-hypothesis/tree/dba5aded4bf7>.
-/

public section

open Complex

namespace TauCeti.LSeries

/-- The displacement of the logarithmic cutoff induced by the Gaussian on the circle
`‖X * z‖ = 1`. -/
noncomputable def gaussianShift (X : ℝ) (z : ℂ) : ℝ :=
  X ^ 2 / 2 * (1 + X * z.re)

/-- Defining formula for `gaussianShift`. -/
theorem gaussianShift_def (X : ℝ) (z : ℂ) :
    gaussianShift X z = X ^ 2 / 2 * (1 + X * z.re) :=
  (rfl)

/-- The displacement stays within the window of width `X²` on the scaled unit disc. -/
theorem gaussianShift_mem_Icc {X : ℝ} {z : ℂ} (hz : ‖(X : ℂ) * z‖ ≤ 1) :
    gaussianShift X z ∈ Set.Icc 0 (X ^ 2) := by
  have hre : |X * z.re| ≤ 1 := by
    simpa using (((X : ℂ) * z).abs_re_le_norm.trans hz)
  obtain ⟨hl, hu⟩ := abs_le.mp hre
  exact ⟨mul_nonneg (by positivity) (by linarith), by rw [gaussianShift_def]; nlinarith⟩

/-- On the scaled unit circle the Gaussian exponent is the exponent at the shifted cutoff. -/
theorem re_gaussian_eq {X : ℝ} {z : ℂ} (hz : ‖(X : ℂ) * z‖ = 1) (U : ℝ) :
    (2 - U * z - (X : ℂ) / 4 * (1 + X * z) ^ 2).re =
      2 - (U + gaussianShift X z) * z.re := by
  -- `‖X * z‖ = 1` says `X² (z.re² + z.im²) = 1`.
  have hnorm : X ^ 2 * (z.re ^ 2 + z.im ^ 2) = 1 := by
    have h := Complex.normSq_eq_norm_sq ((X : ℂ) * z)
    rw [hz, Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_apply] at h
    linear_combination h
  -- Write the coefficient `X / 4` as a real number, so that the real part splits termwise.
  have h4 : (X : ℂ) / 4 * (1 + X * z) ^ 2 = ((X / 4 : ℝ) : ℂ) * ((1 + X * z) * (1 + X * z)) := by
    push_cast
    ring
  rw [h4, sub_re, sub_re, re_ofReal_mul, re_ofReal_mul, mul_re, add_re, add_im, one_re, one_im,
    re_ofReal_mul, im_ofReal_mul, re_ofNat, gaussianShift_def]
  linear_combination X / 4 * hnorm

/-- A restricted Dirichlet series has a Gaussian majorant if its log indices are below
the shifted cutoff when moving left from `1 + 1 / U`, or above that cutoff when moving right.
The hypothesis is automatic for indices below `exp U` in the first case and for indices
at least `exp (U + X²)` in the second. -/
theorem exists_hasSum_term_gaussian_bound (a : ℕ → ℂ) (S : Set ℕ) {X U B : ℝ} {z : ℂ}
    (hz : ‖(X : ℂ) * z‖ = 1) (hU : X ^ 2 ≤ U)
    (hcut : ∀ n ∈ S, (Real.log n - (U + gaussianShift X z)) * (U⁻¹ - z.re) ≤ 0)
    (hB : HasSum (fun n : S ↦ ‖_root_.LSeries.term a (1 + (U⁻¹ : ℝ)) n‖) B) :
    ∃ L, HasSum (fun n : S ↦ _root_.LSeries.term a (1 + z) n) L ∧
      ‖L‖ ≤ Real.exp (2 - U * z - (X : ℂ) / 4 * (1 + X * z) ^ 2).re * B := by
  have hX : X ≠ 0 := by rintro rfl; simp at hz
  have hUpos : 0 < U := (sq_pos_of_ne_zero hX).trans_le hU
  have hshift : gaussianShift X z ≤ U := (gaussianShift_mem_Icc hz.le).2.trans hU
  have href : (U + gaussianShift X z) * U⁻¹ ≤ 2 := by
    rw [← div_eq_mul_inv, div_le_iff₀ hUpos]
    linarith
  let E := (2 - U * z - (X : ℂ) / 4 * (1 + X * z) ^ 2).re
  have hb (n : S) :
      ‖_root_.LSeries.term a (1 + z) n‖ ≤
        Real.exp E * ‖_root_.LSeries.term a (1 + (U⁻¹ : ℝ)) n‖ := by
    apply norm_term_le_exp_mul
    simp only [add_re, one_re, ofReal_re, add_sub_add_left_eq_sub]
    dsimp only [E]
    rw [re_gaussian_eq hz]
    linarith only [hcut n n.prop, href]
  have hsum := (hB.mul_left (Real.exp E)).summable.of_norm_bounded hb
  exact ⟨_, hsum.hasSum, hsum.hasSum.norm_le_of_bounded (hB.mul_left _) hb⟩

end TauCeti.LSeries
