/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.GaussSeries
import Mathlib.NumberTheory.ZetaValues
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Sharp Lipschitz and shifted difference bounds for complex digamma

Subtracting Gauss' series for complex digamma at two arguments cancels Euler's constant and
expresses `digamma s - digamma w` as `∑' n, (s - w) / ((w + n) * (s + n))`. On the closed
half-plane `{s : ℂ | 1 ≤ s.re}`, comparing termwise against `∑' n, 1 / (n + 1)² = π² / 6` gives
the sharp Lipschitz estimate `‖digamma s - digamma w‖ ≤ ‖s - w‖ * (π² / 6)`
(`Complex.norm_digamma_sub_digamma_le_of_one_le_re`), together with its shifted forms
`Complex.norm_digamma_add_sub_digamma_add_le` and
`Complex.norm_digamma_add_one_sub_digamma_add_le`.

## References

* [NIST DLMF, equation 5.7.6](https://dlmf.nist.gov/5.7.E6).
-/

public section

open Complex Real

namespace Complex

/-- Sharp Lipschitz bound for complex digamma on the closed half-plane `{s : ℂ | 1 ≤ s.re}`:
`‖digamma s - digamma w‖ ≤ ‖s - w‖ * (π² / 6)`. -/
theorem norm_digamma_sub_digamma_le_of_one_le_re {s w : ℂ}
    (hs : 1 ≤ s.re) (hw : 1 ≤ w.re) :
    ‖digamma s - digamma w‖ ≤ ‖s - w‖ * (Real.pi ^ 2 / 6) := by
  have hp2 : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    simpa [Nat.cast_add, Nat.cast_one] using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have hsum := hp2.mul_left ‖s - w‖
  have hbd (n : ℕ) : ‖(s - w) / ((w + n) * (s + n))‖ ≤ ‖s - w‖ * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hsn : (n : ℝ) + 1 ≤ ‖s + n‖ := by
      have := Complex.re_le_norm (s + n); simp at this; linarith
    have hwn : (n : ℝ) + 1 ≤ ‖w + n‖ := by
      have := Complex.re_le_norm (w + n); simp at this; linarith
    rw [norm_div, norm_mul, mul_one_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by nlinarith [n.cast_nonneg (α := ℝ)])
  rw [digamma_sub_digamma_eq_tsum (ne_neg_natCast_of_re_pos (by linarith))
    (ne_neg_natCast_of_re_pos (by linarith)), ← hsum.tsum_eq]
  exact (norm_tsum_le_tsum_norm (summable_sub_div_add_mul_add s w).norm).trans
    ((Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbd hsum.summable).tsum_le_tsum
      hbd hsum.summable)

/-- Shifted Lipschitz bound for complex digamma: if `1 ≤ (z + a).re` and `1 ≤ (z + b).re`, then
`‖digamma (z + a) - digamma (z + b)‖ ≤ ‖a - b‖ * (π² / 6)`. -/
theorem norm_digamma_add_sub_digamma_add_le {z a b : ℂ}
    (ha : 1 ≤ (z + a).re) (hb : 1 ≤ (z + b).re) :
    ‖digamma (z + a) - digamma (z + b)‖ ≤ ‖a - b‖ * (Real.pi ^ 2 / 6) := by
  simpa only [add_sub_add_left_eq_sub] using norm_digamma_sub_digamma_le_of_one_le_re ha hb

/-- Uniform shifted digamma difference bound: if `‖b‖ ≤ R` and `R + 1 ≤ z.re`, then
`‖digamma (z + 1) - digamma (z + b)‖ ≤ (1 + R) * (π² / 6)`. -/
theorem norm_digamma_add_one_sub_digamma_add_le {z b : ℂ} {R : ℝ}
    (hb : ‖b‖ ≤ R) (hz : R + 1 ≤ z.re) :
    ‖digamma (z + 1) - digamma (z + b)‖ ≤ (1 + R) * (Real.pi ^ 2 / 6) := by
  have hR : 0 ≤ R := (norm_nonneg b).trans hb
  have hbre : -R ≤ b.re := (neg_le_neg hb).trans (abs_le.mp (abs_re_le_norm b)).1
  have hdig := norm_digamma_add_sub_digamma_add_le (z := z) (a := 1) (b := b)
    (by simp; linarith) (by simp; linarith)
  have h1b : ‖(1 : ℂ) - b‖ ≤ 1 + R := (norm_sub_le 1 b).trans (by norm_num; linarith)
  exact hdig.trans (mul_le_mul_of_nonneg_right h1b (by positivity))

end Complex
