/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The band and bottom-weight box for local theta gains

The local gain estimates exclude prime powers near the transition between the cap regimes. The
band must contain each local exclusion interval, yet have half-width at most `x⁻²` in relative
coordinates so that the excluded primes have small total logarithmic weight. The same budget
bounds the interval of bottom weights available for meeting all local depth constraints.

The band formula is from Levent Alpöge's `Formalism.MainNotions.G.rhoB` in
[`IsResidueClassZero.lean`][band].

[band]: https://github.com/leanprover-community/riemann-hypothesis/blob/40e56bab026552e089d7afcfeff08d2defb9c005/src/Formalism/SharpRestriction/GrowthBounds/IsResidueClassZero.lean
-/

public section

open Filter Real

namespace TauCeti

/-- Relative half-width of the band excluded in the local gain construction, where `δ` is the
top density, `Λ` is the logarithmic size, and `f` and `k` are the host degree and source rank. -/
noncomputable def thetaChainGainBand (x ε C δ Λ : ℝ) (f k : ℕ) : ℝ :=
  (4 * f * δ * x ^ ε + C * log x) * Λ / k

/-- Formula for the relative band half-width in terms of the scale and rank. -/
theorem thetaChainGainBand_def (x ε C δ Λ : ℝ) (f k : ℕ) :
    thetaChainGainBand x ε C δ Λ f k = (4 * f * δ * x ^ ε + C * log x) * Λ / k := (rfl)

/-- The explicit band half-width is at most `x⁻²` for all large `x`, uniformly over the host,
rank, density and logarithmic size in their bounds. The host exponent `A` may vary with `x`. -/
theorem eventually_thetaChainGainBand_le {ε : ℝ} (hε : ε < 1 / 6) (C : ℝ) :
    ∀ᶠ x : ℝ in atTop, ∀ {A δ Λ : ℝ} {f k : ℕ}, 0 ≤ A → δ ≤ 1 → 0 ≤ Λ →
      Λ ≤ x ^ (2 * ε) → (f : ℝ) ≤ 4 * x ^ A → x ^ (A + 5 / 2) ≤ k →
      thetaChainGainBand x ε C δ Λ f k ≤ x ^ (-2 : ℝ) := by
  have hgap : 0 < 1 / 3 - 2 * ε := by linarith
  have hlog := (isLittleO_log_rpow_atTop (r := 1 / 6) (by norm_num)).eventuallyLE
  filter_upwards [eventually_ge_atTop (1 : ℝ), hlog,
    (tendsto_rpow_atTop hgap).eventually_ge_atTop (16 + max C 0)] with x hx hlog hconst
  intro A δ Λ f k hA hδ hΛ hΛx hf hk
  have hx₀ : 0 < x := zero_lt_one.trans_le hx
  have hpow : x ^ ε ≤ x ^ (1 / 6 : ℝ) := rpow_le_rpow_of_exponent_le hx hε.le
  have hA₁ : 1 ≤ x ^ A := one_le_rpow hx hA
  have hbudget : 4 * f * δ * x ^ ε + C * log x ≤ (16 + max C 0) * (x ^ A * x ^ (1 / 6 : ℝ)) := by
    have htop : 4 * f * δ ≤ 16 * x ^ A := by
      calc
        _ ≤ (4 : ℝ) * f * 1 := mul_le_mul_of_nonneg_left hδ (by positivity)
        _ ≤ _ := by linarith
    have hlog' : C * log x ≤ max C 0 * (x ^ A * x ^ (1 / 6 : ℝ)) := by
      refine (mul_le_mul_of_nonneg_right (le_max_left C 0) (log_nonneg hx)).trans ?_
      gcongr
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (log_nonneg hx),
        abs_of_nonneg (rpow_nonneg hx₀.le _)] at hlog
      exact hlog.trans (le_mul_of_one_le_left (by positivity) hA₁)
    nlinarith only [hlog', mul_le_mul htop hpow (by positivity) (by positivity)]
  rw [thetaChainGainBand_def]
  calc
    _ ≤ ((16 + max C 0) * (x ^ A * x ^ (1 / 6 : ℝ))) * x ^ (2 * ε) / x ^ (A + 5 / 2) := by
      apply div_le_div_of_nonneg_left (by positivity) (rpow_pos_of_pos hx₀ _) hk |>.trans'
      exact div_le_div_of_nonneg_right
        (mul_le_mul hbudget hΛx hΛ (by positivity)) (Nat.cast_nonneg k)
    _ = (16 + max C 0) * (x ^ (A + (1 / 6 + 2 * ε)) / x ^ (A + 5 / 2)) := by
      rw [rpow_add hx₀ A (1 / 6 + 2 * ε), rpow_add hx₀ (1 / 6) (2 * ε)]
      ring
    _ = x ^ (-2 : ℝ) * ((16 + max C 0) / x ^ (1 / 3 - 2 * ε)) := by
      have hpowEq : x ^ (A + (1 / 6 + 2 * ε)) / x ^ (A + 5 / 2) =
          x ^ (-2 : ℝ) / x ^ (1 / 3 - 2 * ε) := by
        simp_rw [← rpow_sub hx₀]
        congr 1
        ring
      rw [hpowEq]
      ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity)
      ((div_le_one (rpow_pos_of_pos hx₀ _)).mpr hconst)

/-- Width of the permitted interval for a bottom-weight entry, where `b` is the base bottom
weight. -/
noncomputable def thetaChainBottomBox (x ε δ Λ b : ℝ) (f k : ℕ) : ℝ :=
  f * δ * x ^ ε * Λ * b / k

/-- Formula for the bottom-weight interval width. -/
theorem thetaChainBottomBox_def (x ε δ Λ b : ℝ) (f k : ℕ) :
    thetaChainBottomBox x ε δ Λ b f k = f * δ * x ^ ε * Λ * b / k := (rfl)

/-- Four times the relative width of the bottom-weight box accounts for the density term of the
band. The remaining term pays for the local depth cutoff. -/
theorem thetaChainGainBand_eq_add_bottomBox {x ε C δ Λ b : ℝ} (hb : b ≠ 0) (f k : ℕ) :
    thetaChainGainBand x ε C δ Λ f k =
      4 * (thetaChainBottomBox x ε δ Λ b f k / b) + C * log x * Λ / k := by
  simp only [thetaChainGainBand_def, thetaChainBottomBox_def, div_right_comm _ _ b,
    mul_div_cancel_right₀ _ hb]
  ring

/-- The input local exclusion half-width `2δ_I` is bounded by the global band half-width. -/
theorem two_mul_thetaChainLocalWidth_le_gainBand {x ε C δ Λ b H s : ℝ} {f k : ℕ}
    (hb : b ≠ 0) (hΛ : 0 ≤ Λ) (hs : 2 * H * s ≤ C * log x) :
    2 * (H * s * Λ / k + 2 * (thetaChainBottomBox x ε δ Λ b f k / b)) ≤
      thetaChainGainBand x ε C δ Λ f k := by
  rw [thetaChainGainBand_eq_add_bottomBox hb]
  have h := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hs hΛ) (Nat.cast_nonneg k)
  linarith only [h, (by ring : (2 * H * s) * Λ / k = 2 * (H * s * Λ / k))]

/-- If the logarithmic contribution is nonnegative, a band of half-width at most `2` makes the
bottom-weight interval at most half its base weight. -/
theorem thetaChainBottomBox_le_half {x ε C δ Λ b : ℝ} {f k : ℕ} (hb : 0 ≤ b)
    (hlog : 0 ≤ C * log x * Λ) (hband : thetaChainGainBand x ε C δ Λ f k ≤ 2) :
    thetaChainBottomBox x ε δ Λ b f k ≤ b / 2 := by
  rcases hb.eq_or_lt with heq | hb
  · simp [← heq, thetaChainBottomBox_def]
  rw [thetaChainGainBand_eq_add_bottomBox hb.ne'] at hband
  have hcost := div_nonneg hlog (Nat.cast_nonneg k)
  have hdiv : thetaChainBottomBox x ε δ Λ b f k / b ≤ 1 / 2 := by linarith
  exact ((div_le_iff₀ hb).mp hdiv).trans_eq (by ring)

/-- The bottom-weight box fits a good orbit's local depth requirement once `x^ε ≥ 80Y` and the
number `n` of selected tops on that orbit is at most `80 f δ`. -/
theorem mul_le_thetaChainBottomBox {x ε δ Λ b Y : ℝ} {f k n : ℕ} (hΛ : 0 ≤ Λ) (hb : 0 ≤ b)
    (hY : 0 ≤ Y) (hYx : 80 * Y ≤ x ^ ε) (hn : (n : ℝ) ≤ 80 * f * δ) :
    Y * n * Λ * b / k ≤ thetaChainBottomBox x ε δ Λ b f k := by
  have hδ : 0 ≤ (f : ℝ) * δ := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hbox : Y * n ≤ (f : ℝ) * δ * x ^ ε := by
    refine (mul_le_mul_of_nonneg_left hn hY).trans ?_
    convert mul_le_mul_of_nonneg_left hYx hδ using 1; ring
  rw [thetaChainBottomBox_def]
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hbox hΛ) hb) (Nat.cast_nonneg k)

end TauCeti
