/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma.GaussSeries
import Mathlib.NumberTheory.ZetaValues
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Sharp Lipschitz, order, and shifted difference bounds for digamma

Subtracting Gauss' series for digamma at two arguments cancels Euler's constant and expresses
`digamma s - digamma w` as `∑' n, (s - w) / ((w + n) * (s + n))`. On the closed half-plane
`{s : ℂ | 1 ≤ s.re}`, comparing termwise against `∑' n, 1 / (n + 1)² = π² / 6` gives the sharp
Lipschitz estimate `‖digamma s - digamma w‖ ≤ ‖s - w‖ * (π² / 6)`
(`Complex.norm_digamma_sub_digamma_le_of_one_le_re`), together with its shifted forms
`Complex.norm_digamma_add_sub_digamma_add_le` and
`Complex.norm_digamma_add_one_sub_digamma_add_le`.

For real arguments, the series yields strict monotonicity of `Real.digamma`
(`Real.strictMonoOn_digamma`), strict antitonicity and antitonicity of shifted differences in both
the shift parameter `t ↦ ψ(t + b) - ψ(t + a)` and the subtracted argument `a ↦ d - ψ(t + a)`, and
uniform two-sided bounds on shifted differences (`Real.digamma_add_sub_digamma_add_le`,
`Real.digamma_add_sub_digamma_add_bounds`, `Real.digamma_nat_add_one_sub_digamma_add_bounds`).

## References

* [NIST DLMF, equation 5.7.6](https://dlmf.nist.gov/5.7.E6).
* F. Calegari, V. Dimitrov and Y. Tang (CDT), *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Lemma 5.2.9, p. 676.
-/

public section

open Complex Real Set

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
      have := Complex.re_le_norm (s + n)
      simp only [add_re, natCast_re] at this
      linarith
    have hwn : (n : ℝ) + 1 ≤ ‖w + n‖ := by
      have := Complex.re_le_norm (w + n)
      simp only [add_re, natCast_re] at this
      linarith
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
    (by simp only [add_re, one_re]; linarith) (by simp only [add_re]; linarith)
  have h1b : ‖(1 : ℂ) - b‖ ≤ 1 + R := (norm_sub_le 1 b).trans (by rw [norm_one]; linarith)
  exact hdig.trans (mul_le_mul_of_nonneg_right h1b (by positivity))

end Complex

namespace Real

/-- Real digamma is strictly monotone on the positive real axis. -/
theorem strictMonoOn_digamma : StrictMonoOn digamma (Ioi 0) := by
  intro x hx y hy hxy
  rw [← sub_pos, digamma_sub_digamma_eq_tsum
    (fun m ↦ by linarith [mem_Ioi.mp hy, m.cast_nonneg (α := ℝ)])
    (fun m ↦ by linarith [mem_Ioi.mp hx, m.cast_nonneg (α := ℝ)])]
  refine (summable_sub_div_add_mul_add y x).tsum_pos (fun n ↦ div_nonneg (sub_nonneg.mpr hxy.le)
    (mul_pos (by linarith [mem_Ioi.mp hx, n.cast_nonneg (α := ℝ)])
      (by linarith [mem_Ioi.mp hy, n.cast_nonneg (α := ℝ)])).le) 0 ?_
  simpa using div_pos (sub_pos.mpr hxy) (mul_pos (mem_Ioi.mp hx) (mem_Ioi.mp hy))

/-- When `a < b`, the shifted digamma difference `t ↦ ψ(t + b) - ψ(t + a)` is strictly antitone
on `(-a, ∞)`. -/
theorem strictAntiOn_digamma_add_sub_digamma_add {a b : ℝ} (hab : a < b) :
    StrictAntiOn (fun t : ℝ ↦ digamma (t + b) - digamma (t + a)) (Ioi (-a)) := by
  intro t₁ ht₁ t₂ _ ht
  have hreg {u : ℝ} (hu : 0 < u) (m : ℕ) : u ≠ -(m : ℝ) := by linarith [m.cast_nonneg (α := ℝ)]
  have h0 := mem_Ioi.mp ht₁
  dsimp only
  rw [digamma_sub_digamma_eq_tsum (hreg (by linarith)) (hreg (by linarith)),
    digamma_sub_digamma_eq_tsum (hreg (by linarith)) (hreg (by linarith))]
  refine (summable_sub_div_add_mul_add (t₂ + b) (t₂ + a)).tsum_lt_tsum (i := 0) (fun n ↦ ?_) ?_
    (summable_sub_div_add_mul_add (t₁ + b) (t₁ + a))
  · simp only [add_sub_add_left_eq_sub]
    have _ := n.cast_nonneg (α := ℝ)
    exact div_le_div_of_nonneg_left (sub_nonneg.mpr hab.le) (mul_pos (by linarith) (by linarith))
      (mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith))
  · simp only [add_sub_add_left_eq_sub, Nat.cast_zero, add_zero]
    exact div_lt_div_of_pos_left (sub_pos.mpr hab) (mul_pos (by linarith) (by linarith))
      (mul_lt_mul'' (by linarith) (by linarith) (by linarith) (by linarith))

/-- When `a ≤ b`, the shifted digamma difference `t ↦ ψ(t + b) - ψ(t + a)` is antitone on
`(-a, ∞)`. -/
theorem antitoneOn_digamma_add_sub_digamma_add {a b : ℝ} (hab : a ≤ b) :
    AntitoneOn (fun t : ℝ ↦ digamma (t + b) - digamma (t + a)) (Ioi (-a)) := by
  rcases hab.eq_or_lt with rfl | hlt
  · intro _ _ _ _ _; simp
  · exact (strictAntiOn_digamma_add_sub_digamma_add hlt).antitoneOn

/-- Uniform upper bound on shifted digamma differences: for `t₀ ≤ t`, `-t₀ < c`, `c ≤ a`, and
`c ≤ b`, `ψ(t + b) - ψ(t + a) ≤ ψ(t₀ + b) - ψ(t₀ + c)` (generalizing CDT Lemma 5.2.9). -/
theorem digamma_add_sub_digamma_add_le {t₀ t c a b : ℝ}
    (ht : t₀ ≤ t) (hc : -t₀ < c) (hca : c ≤ a) (hcb : c ≤ b) :
    digamma (t + b) - digamma (t + a) ≤ digamma (t₀ + b) - digamma (t₀ + c) :=
  (sub_le_sub_left (monotoneOn_digamma
    (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith)) (by linarith)) _).trans <|
    antitoneOn_digamma_add_sub_digamma_add hcb
      (mem_Ioi.mpr (by linarith)) (mem_Ioi.mpr (by linarith)) ht

/-- For fixed `d` and `t`, `a ↦ d - ψ(t + a)` is strictly antitone on `(-t, ∞)`. -/
theorem strictAntiOn_const_sub_digamma_add (d t : ℝ) :
    StrictAntiOn (fun a : ℝ ↦ d - digamma (t + a)) (Ioi (-t)) := fun _ ha₁ _ ha₂ ha ↦
  sub_lt_sub_left (strictMonoOn_digamma (mem_Ioi.mpr (by linarith [mem_Ioi.mp ha₁]))
    (mem_Ioi.mpr (by linarith [mem_Ioi.mp ha₂])) (by linarith)) d

/-- For fixed `d` and `t`, `a ↦ d - ψ(t + a)` is antitone on `(-t, ∞)`. -/
theorem antitoneOn_const_sub_digamma_add (d t : ℝ) :
    AntitoneOn (fun a : ℝ ↦ d - digamma (t + a)) (Ioi (-t)) :=
  (strictAntiOn_const_sub_digamma_add d t).antitoneOn

/-- Two-sided uniform estimate on shifted digamma differences: for `t₀ ≤ t` and `-t₀ < c ≤ a ≤ b`,
`0 ≤ ψ(t + b) - ψ(t + a) ≤ ψ(t₀ + b) - ψ(t₀ + c)`. -/
theorem digamma_add_sub_digamma_add_bounds {t₀ t c a b : ℝ}
    (ht : t₀ ≤ t) (hc : -t₀ < c) (hca : c ≤ a) (hab : a ≤ b) :
    0 ≤ digamma (t + b) - digamma (t + a) ∧
      digamma (t + b) - digamma (t + a) ≤ digamma (t₀ + b) - digamma (t₀ + c) :=
  ⟨sub_nonneg.mpr (monotoneOn_digamma (mem_Ioi.mpr (by linarith))
    (mem_Ioi.mpr (by linarith)) (by linarith)),
    digamma_add_sub_digamma_add_le ht hc hca (hca.trans hab)⟩

/-- Two-sided estimate on `ψ(k + 1) - ψ(k + a)` for `k ≥ 1` and `-1 < c ≤ a ≤ 1`:
`0 ≤ ψ(k + 1) - ψ(k + a) ≤ ψ(2) - ψ(1 + c)`. -/
theorem digamma_nat_add_one_sub_digamma_add_bounds {k : ℕ} (hk : 1 ≤ k) {c a : ℝ}
    (hc : -1 < c) (hca : c ≤ a) (ha : a ≤ 1) :
    0 ≤ digamma ((k : ℝ) + 1) - digamma ((k : ℝ) + a) ∧
      digamma ((k : ℝ) + 1) - digamma ((k : ℝ) + a) ≤ digamma 2 - digamma (1 + c) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using
    digamma_add_sub_digamma_add_bounds hk' hc hca ha

end Real
