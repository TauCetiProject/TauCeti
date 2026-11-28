/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma.GaussSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The gamma contribution to the first Riesz explicit formula

A gamma factor with poles at `−(a + d*n)` contributes the terms
`−y ^ (−p) / (p * (p + 1))`, where `p = a + d*n > 0`. The upper-tail Mellin
transform of this series is the logarithmic derivative with its affine interpolant at `0`
and `1` subtracted, divided by `s * (s - 1)`. This isolates the contribution of the
strictly negative trivial zeros, leaving the term at zero to be handled separately.

The calculation uses Gauss' paired reciprocal expansion of the digamma function
(DLMF §5.7.6), as formalized in `Complex.digamma_eq_gaussSeries`.
-/

public section

open Complex MeasureTheory Set

namespace TauCeti

/-- The negative-pole contribution to the first Riesz explicit formula for a gamma factor
with poles at `−(a + d*n)`, where `a, d > 0`. -/
noncomputable def rieszGammaCorrection (a d y : ℝ) : ℂ :=
  ∑' n : ℕ, -((y : ℂ) ^ (-(↑(a + d * n) : ℂ))) / (↑(a + d * n) * (↑(a + d * n) + 1))

/-- The series for the contribution of the gamma poles at `−(a + d*n)`. -/
theorem rieszGammaCorrection_def (a d y : ℝ) : rieszGammaCorrection a d y =
    ∑' n : ℕ, -((y : ℂ) ^ (-(↑(a + d * n) : ℂ))) / (↑(a + d * n) * (↑(a + d * n) + 1)) := (rfl)

private noncomputable def gammaWeight (a d : ℝ) (n : ℕ) : ℝ :=
  1 / ((a + d * n) * (a + d * n + 1))

private theorem summable_gammaWeight {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    Summable (gammaWeight a d) := by
  let c := min a d
  have hc : 0 < c := lt_min ha hd
  have hsum : Summable (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2))
  refine (hsum.mul_left (1 / c ^ 2)).of_nonneg_of_le (fun n ↦ by dsimp [gammaWeight]; positivity) ?_
  intro n
  have h : c * ((n : ℝ) + 1) ≤ a + d * n := by
    rw [mul_add, mul_one]
    exact add_le_add (mul_le_mul_of_nonneg_right (min_le_right a d) (Nat.cast_nonneg n))
      (min_le_left a d) |>.trans (by rw [add_comm])
  calc
    gammaWeight a d n ≤ 1 / (c * ((n : ℝ) + 1)) ^ 2 := by
      apply one_div_le_one_div_of_le (by positivity)
      exact ((sq_le_sq₀ (mul_nonneg hc.le (by positivity)) (by positivity)).2 h).trans
        (by
          rw [sq]
          exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity))
    _ = (1 / c ^ 2) * (1 / ((n : ℝ) + 1) ^ 2) := by rw [mul_pow, one_div_mul_one_div]

private theorem norm_gammaTerm_le {a d y : ℝ} (hd : 0 ≤ d) (hy : 1 ≤ y) (n : ℕ) :
    ‖-((gammaWeight a d n : ℂ) * (y : ℂ) ^ (-(↑(a + d * n) : ℂ)))‖ ≤
      |gammaWeight a d n| * y ^ (-a) := by
  rw [norm_neg, norm_mul, norm_real, Real.norm_eq_abs,
    norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hy)]
  gcongr
  simp only [neg_re, ofReal_re, neg_le_neg_iff, le_add_iff_nonneg_right]
  positivity

/-- The series of contributions of the gamma poles converges absolutely for `y ≥ 1`. -/
theorem summable_rieszGammaCorrection {a d y : ℝ} (ha : 0 < a) (hd : 0 < d) (hy : 1 ≤ y) :
    Summable (fun n : ℕ ↦ -((y : ℂ) ^ (-(↑(a + d * n) : ℂ))) /
      (↑(a + d * n) * (↑(a + d * n) + 1))) := by
  simpa [gammaWeight, div_eq_mul_inv, mul_comm] using
    (((summable_gammaWeight ha hd).abs.mul_right (y ^ (-a))).of_norm_bounded
      (norm_gammaTerm_le (a := a) hd.le hy))

/-- The gamma correction decays at least as fast as `y ^ (-a)` on `[1, ∞)`. -/
theorem exists_norm_rieszGammaCorrection_le {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    ∃ C : ℝ, ∀ y ≥ 1, ‖rieszGammaCorrection a d y‖ ≤ C * y ^ (-a) := by
  refine ⟨∑' n, |gammaWeight a d n|, fun y hy ↦ ?_⟩
  rw [rieszGammaCorrection_def, ← tsum_mul_right]
  apply (norm_tsum_le_tsum_norm (summable_rieszGammaCorrection ha hd hy).norm).trans
  refine Summable.tsum_le_tsum ?_ (summable_rieszGammaCorrection ha hd hy).norm
    ((summable_gammaWeight ha hd).abs.mul_right _)
  intro n
  simpa [gammaWeight, div_eq_mul_inv, mul_comm] using norm_gammaTerm_le (a := a) hd.le hy n

/-- The gamma correction is continuous up to the endpoint `y = 1`. -/
theorem continuousOn_rieszGammaCorrection {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    ContinuousOn (rieszGammaCorrection a d) (Ici 1) := by
  rw [funext (rieszGammaCorrection_def a d)]
  refine continuousOn_tsum (u := fun n ↦ |gammaWeight a d n|) ?_
    (summable_gammaWeight ha hd).abs ?_
  · intro n
    apply ContinuousOn.div_const
    apply ContinuousOn.neg
    exact continuous_ofReal.continuousOn.cpow continuousOn_const fun y hy ↦
      Or.inl (by simpa using (zero_lt_one.trans_le hy : 0 < y))
  · intro n y hy
    have hy' : 1 ≤ y := hy
    have hp : y ^ (-a) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy' (neg_nonpos.mpr ha.le)
    have h := (norm_gammaTerm_le (a := a) hd.le hy' n).trans
      (mul_le_of_le_one_right (abs_nonneg _) hp)
    simpa [gammaWeight, div_eq_mul_inv, mul_comm] using h

/-- The gamma correction has an absolutely convergent upper-tail Mellin transform for
`Re s > -a`. -/
theorem integrableOn_rieszGammaCorrection_mul_cpow {a d : ℝ} {s : ℂ}
    (ha : 0 < a) (hd : 0 < d) (hs : -a < s.re) :
    IntegrableOn (fun y : ℝ ↦ rieszGammaCorrection a d y * (y : ℂ) ^ (-s - 1)) (Ioi 1) := by
  obtain ⟨C, hC⟩ := exists_norm_rieszGammaCorrection_le ha hd
  refine ((integrableOn_Ioi_rpow_of_lt (by linarith : -s.re - a - 1 < -1)
    zero_lt_one).const_mul C).mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    refine ((continuousOn_rieszGammaCorrection ha hd).mono Ioi_subset_Ici_self).mul ?_
    exact continuous_ofReal.continuousOn.cpow continuousOn_const fun y hy ↦
      Or.inl (by simpa using (zero_lt_one.trans hy : 0 < y))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hy), sub_re, neg_re, one_re]
    calc
      _ ≤ (C * y ^ (-a)) * y ^ (-s.re - 1) :=
        mul_le_mul_of_nonneg_right (hC y hy.le) (Real.rpow_nonneg (zero_lt_one.trans hy).le _)
      _ = C * y ^ (-s.re - a - 1) := by
        rw [mul_assoc, ← Real.rpow_add (zero_lt_one.trans hy)]
        congr 2
        ring

/-- After subtraction of its affine interpolant at `0` and `1`, the scaled digamma
function has a partial fraction expansion with cubic decay in the summation index. -/
private theorem hasSum_rieszGammaCorrection_resolvent {a d : ℝ} {s : ℂ}
    (ha : 0 < a) (hd : 0 < d) (hs : -a < s.re) :
    HasSum (fun n : ℕ ↦ s * (s - 1) * (-(gammaWeight a d n : ℂ) / (s + ↑(a + d * n))))
      ((digamma ((s + (a : ℂ)) / d) - (1 - s) * digamma ((a : ℂ) / d) -
        s * digamma ((1 + (a : ℂ)) / d)) / d) := by
  let t : ℂ → ℂ := fun z ↦ (z + (a : ℂ)) / d
  have hg (z : ℂ) (hz : -a < z.re) : HasSum
      (fun n : ℕ ↦ 1 / ((n : ℂ) + 1) - 1 / (t z + n))
      (digamma (t z) + Real.eulerMascheroniConstant) := by
    have hpos : 0 < (t z).re := by
      simp only [t, div_ofReal_re, add_re, ofReal_re]
      exact div_pos (by linarith) hd
    rw [digamma_eq_gaussSeries (ne_neg_natCast_of_re_pos hpos), neg_add_cancel_comm]
    exact (summable_gaussSeries (t z)).hasSum
  have h_one : -a < (1 : ℂ).re := by rw [one_re]; linarith
  have h := (((hg s hs).sub ((hg 0 (by simpa)).mul_left (1 - s))).sub
    ((hg 1 h_one).mul_left s)).div_const (d : ℂ)
  convert h using 1
  · ext n
    have hd₀ : (d : ℂ) ≠ 0 := ofReal_ne_zero.mpr hd.ne'
    have hp (z : ℂ) (hz : -a < z.re) : z + ↑(a + d * (n : ℝ)) ≠ 0 := by
      intro hzero
      have := congrArg Complex.re hzero
      simp at this
      nlinarith [mul_nonneg hd.le (Nat.cast_nonneg (α := ℝ) n)]
    have h0 := hp 0 (by simpa)
    have h1 := hp 1 h_one
    have hn : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero n)
    have harg (z : ℂ) : t z + n = (z + ↑(a + d * (n : ℝ))) / d := by
      push_cast [t]
      field_simp
      ring
    simp only [harg, gammaWeight, ofReal_div, ofReal_one, ofReal_mul, ofReal_add, ofReal_natCast]
    push_cast at h0 h1
    have hps := hp s hs
    push_cast at hps
    simp only [zero_add] at h0 ⊢
    have h1' : (a : ℂ) + d * n + 1 ≠ 0 := by rwa [add_comm _ 1]
    field_simp [hd₀, hps, h0, h1', hn]
    ring
  · simp only [t, zero_add]
    ring

/-- Upper-tail Mellin transform of the gamma correction, with the kernel denominator
cleared. The identity includes `s = 0` and `s = 1`, where the subtracted numerator vanishes. -/
theorem mul_integral_rieszGammaCorrection {a d : ℝ} {s : ℂ}
    (ha : 0 < a) (hd : 0 < d) (hs : -a < s.re) :
    s * (s - 1) * (∫ y : ℝ in Ioi 1, rieszGammaCorrection a d y * (y : ℂ) ^ (-s - 1)) =
      (digamma ((s + (a : ℂ)) / d) - (1 - s) * digamma ((a : ℂ) / d) -
        s * digamma ((1 + (a : ℂ)) / d)) / d := by
  let F := fun (n : ℕ) (y : ℝ) ↦ -(gammaWeight a d n : ℂ) * (y : ℂ) ^ (-s - ↑(a + d * n) - 1)
  have hExp (n : ℕ) : (-s - (↑(a + d * n) : ℂ) - 1).re < -1 := by
    simp only [sub_re, neg_re, ofReal_re, one_re]
    nlinarith [mul_nonneg hd.le (Nat.cast_nonneg (α := ℝ) n)]
  have hF (n : ℕ) : IntegrableOn (F n) (Ioi 1) :=
    (integrableOn_Ioi_cpow_of_lt (hExp n) zero_lt_one).const_mul _
  have heq (y : ℝ) (hy : 1 < y) :
      (∑' n, F n y) = rieszGammaCorrection a d y * (y : ℂ) ^ (-s - 1) := by
    rw [rieszGammaCorrection_def, ← tsum_mul_right]
    congr 1 with n
    have hexp : -s - (↑(a + d * n) : ℂ) - 1 = -↑(a + d * n) + (-s - 1) := by ring
    dsimp only [F]
    rw [hexp, cpow_add _ _ (ofReal_ne_zero.mpr (zero_lt_one.trans hy).ne')]
    push_cast [gammaWeight]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi (fun y hy ↦ (heq y hy).symm)]
  have hm : Summable (fun n ↦ ∫ y in Ioi (1 : ℝ), ‖F n y‖) := by
    refine ((summable_gammaWeight ha hd).abs.mul_right
      (∫ y : ℝ in Ioi 1, y ^ (-s.re - a - 1))).of_nonneg_of_le
      (fun _ ↦ integral_nonneg fun _ ↦ norm_nonneg _) fun n ↦ ?_
    rw [← integral_const_mul]
    apply setIntegral_mono_on (hF n).norm
      ((integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul _) measurableSet_Ioi
    intro y hy
    rw [norm_mul, norm_neg, norm_real, Real.norm_eq_abs,
      norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans hy)]
    gcongr
    · exact hy.le
    · simp only [sub_re, neg_re, ofReal_re, one_re]
      nlinarith [mul_nonneg hd.le (Nat.cast_nonneg (α := ℝ) n)]
  have hInt (n : ℕ) : (∫ y in Ioi 1, F n y) =
      -(gammaWeight a d n : ℂ) / (s + ↑(a + d * n)) := by
    have hexp : -s - (↑(a + d * n) : ℂ) - 1 + 1 = -(s + ↑(a + d * n)) := by ring
    simp only [F, integral_const_mul, integral_Ioi_cpow_of_lt (hExp n) zero_lt_one,
      ofReal_one, one_cpow, hexp, div_neg, neg_div, neg_neg, mul_one_div]
  rw [← integral_tsum_of_summable_integral_norm hF hm, ← tsum_mul_left]
  simpa only [hInt] using (hasSum_rieszGammaCorrection_resolvent ha hd hs).tsum_eq

/-- The strictly negative real-place poles of `Gammaℝ (s + a)` give the correction with
spacing `2` when `a > 0`. In particular `a = 1` gives the odd Dirichlet contribution, and
`a = 2` gives the even contribution after removing the pole at zero by the gamma recurrence. -/
theorem mul_integral_rieszGammaCorrection_eq_logDeriv_Gammaℝ {a : ℝ} {s : ℂ}
    (ha : 0 < a) (hs : -a < s.re) :
    s * (s - 1) * (∫ y : ℝ in Ioi 1, rieszGammaCorrection a 2 y * (y : ℂ) ^ (-s - 1)) =
      logDeriv Gammaℝ (s + a) - (1 - s) * logDeriv Gammaℝ a - s * logDeriv Gammaℝ (1 + a) := by
  have h (z : ℂ) (hz : 0 < z.re) :
      logDeriv Gammaℝ z = digamma (z / 2) / 2 - (Real.log Real.pi : ℂ) / 2 :=
    logDeriv_Gammaℝ (fun n ↦ by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using ne_neg_natCast_of_re_pos hz (2 * n))
  rw [h (s + a) (by simp; linarith), h a (by simpa), h (1 + a) (by simp; linarith),
    mul_integral_rieszGammaCorrection ha (by norm_num) hs]
  push_cast
  ring

/-- The strictly negative complex-place poles of `Gammaℂ (s + a)` give the correction with
spacing `1` when `a > 0`; at `a = 1` this excludes the unshifted factor's pole at zero. -/
theorem mul_integral_rieszGammaCorrection_eq_logDeriv_Gammaℂ {a : ℝ} {s : ℂ}
    (ha : 0 < a) (hs : -a < s.re) :
    s * (s - 1) * (∫ y : ℝ in Ioi 1, rieszGammaCorrection a 1 y * (y : ℂ) ^ (-s - 1)) =
      logDeriv Gammaℂ (s + a) - (1 - s) * logDeriv Gammaℂ a - s * logDeriv Gammaℂ (1 + a) := by
  rw [logDeriv_Gammaℂ (ne_neg_natCast_of_re_pos (by simp; linarith : 0 < (s + ↑a).re)),
    logDeriv_Gammaℂ (ne_neg_natCast_of_re_pos (by simpa : 0 < (a : ℂ).re)),
    logDeriv_Gammaℂ (ne_neg_natCast_of_re_pos (by simp; linarith : 0 < (1 + ↑a : ℂ).re)),
    mul_integral_rieszGammaCorrection ha zero_lt_one hs]
  simp only [ofReal_one, div_one]
  ring

end TauCeti
