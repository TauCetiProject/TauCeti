/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Gaussian cutoffs for Dirichlet series

On the circle of radius `1 / X`, the real part of the quadratic term in the Gaussian
weight shifts the logarithmic cutoff `U` by a real number in `[0, X²]`. This gives a
common majorant at the real point `1 + 1 / U` for two sums used in the short-window
prime argument: the initial Dirichlet polynomial on the left of that point and
the tail beyond the window on its right.

The comparison uses absolute convergence at the reference point. In the tail
application it also supplies absolute convergence of the restricted series.
-/

@[expose] public section

open Complex

namespace TauCeti.LSeries

/-- The displacement of the logarithmic cutoff induced by the Gaussian on the circle
`‖X * z‖ = 1`. -/
noncomputable def gaussianShift (X : ℝ) (z : ℂ) : ℝ :=
  X ^ 2 / 2 * (1 + X * z.re)

/-- The displacement stays within the window of width `X²` on the scaled unit disc. -/
theorem gaussianShift_mem_Icc {X : ℝ} {z : ℂ} (hz : ‖(X : ℂ) * z‖ ≤ 1) :
    gaussianShift X z ∈ Set.Icc 0 (X ^ 2) := by
  have hre : |X * z.re| ≤ 1 := by
    simpa using (((X : ℂ) * z).abs_re_le_norm.trans hz)
  obtain ⟨hl, hu⟩ := abs_le.mp hre
  exact ⟨mul_nonneg (by positivity) (by linarith), by unfold gaussianShift; nlinarith⟩

/-- On the scaled unit circle the Gaussian exponent is the exponent at the shifted cutoff. -/
theorem re_gaussian_eq {X : ℝ} {z : ℂ} (hz : ‖(X : ℂ) * z‖ = 1) (U : ℝ) :
    (2 - U * z - (X : ℂ) / 4 * (1 + X * z) ^ 2).re =
      2 - (U + gaussianShift X z) * z.re := by
  have him := ((X : ℂ) * z).sq_norm_sub_sq_re
  rw [hz] at him
  simp [mul_re, mul_im] at him
  rw [show (X : ℂ) / 4 = ((X / 4 : ℝ) : ℂ) by push_cast; rfl]
  norm_num [gaussianShift, sub_re, mul_re, mul_im, add_re, add_im, pow_two]
  linear_combination -X / 4 * him

/-- Changing the real part of the argument rescales the norm of a Dirichlet term by an
exponential in the logarithm of its index. -/
theorem norm_term_eq_exp_mul (a : ℕ → ℂ) (s w : ℂ) (n : ℕ) :
    ‖_root_.LSeries.term a s n‖ =
      Real.exp (Real.log n * (w.re - s.re)) * ‖_root_.LSeries.term a w n‖ := by
  simp only [_root_.LSeries.norm_term_eq]
  split_ifs with hn
  · simp
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Real.rpow_def_of_pos hnpos, Real.rpow_def_of_pos hnpos, mul_sub, Real.exp_sub]
    field_simp [Real.exp_ne_zero]

/-- An exponential bound on the real shift bounds a Dirichlet term by the corresponding term
at the reference point. -/
theorem norm_term_le_exp_mul (a : ℕ → ℂ) {s w : ℂ} {n : ℕ} {E : ℝ}
    (h : Real.log n * (w.re - s.re) ≤ E) :
    ‖_root_.LSeries.term a s n‖ ≤ Real.exp E * ‖_root_.LSeries.term a w n‖ := by
  rw [norm_term_eq_exp_mul a s w n]
  gcongr

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
    change _ ≤ (2 - U * z - (X : ℂ) / 4 * (1 + X * z) ^ 2).re
    rw [re_gaussian_eq hz]
    linarith only [hcut n n.prop, href]
  have hsum := (hB.mul_left (Real.exp E)).summable.of_norm_bounded hb
  exact ⟨_, hsum.hasSum, hsum.hasSum.norm_le_of_bounded (hB.mul_left _) hb⟩

end TauCeti.LSeries
