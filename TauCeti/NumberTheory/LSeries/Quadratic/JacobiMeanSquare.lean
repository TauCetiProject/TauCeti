/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.GaussianTheta.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.SeriesMeanSquare
import TauCeti.NumberTheory.LSeries.Quadratic.GaussianPairBounds

/-!
# Mean squares of Jacobi twists of Gaussian theta series

Average over the numerator of the Jacobi symbol, with the odd part of the coefficient index
as denominator. The Gaussian pair bounds control products with square odd part and the
Pólya–Vinogradov weight for the other products. This yields a uniform second moment for
integrating tails of theta series of quadratic twists.

The estimate corresponds to `New.sum_sq_thetaSeries_jacobiSym_le` in
`Lib/Analytic/QuadraticTwist.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207/grh).
-/

public section

open Finset Real
open scoped Nat

namespace TauCeti

private theorem gaussianPair_jacobiMajorant_le (j : Fin 2) (X : ℕ) {c : ℕ → ℂ}
    (q : ℕ+ × ℕ+) (hc₁ : ‖c q.1‖ ≤ 1) (hc₂ : ‖c q.2‖ ≤ 1) (u : ℝ) :
    let w (n : ℕ+) : ℝ := ‖gaussianMonomial j (n * u)‖
    let m := ordCompl[2] ((q.1 : ℕ) * q.2)
    let b := (q.1 : ℝ) * q.2
    (‖c q.1‖ * w q.1) * (‖c q.2‖ * w q.2) *
        (if IsSquare m then (X : ℝ) else min X (2 * √m * (1 + log m))) ≤
      X * (if IsSquare m then w q.1 * w q.2 else 0) +
        2 * (w q.1 * w q.2 * (√b * (1 + log b))) := by
  intro w m b
  have hm₁ : (1 : ℝ) ≤ m := by
    exact_mod_cast Nat.one_le_of_lt (Nat.ordCompl_pos 2 (mul_ne_zero q.1.ne_zero q.2.ne_zero))
  have hmb : (m : ℝ) ≤ b := by
    dsimp only [m, b]
    exact_mod_cast Nat.ordCompl_le ((q.1 : ℕ) * q.2) 2
  have hw : (‖c q.1‖ * w q.1) * (‖c q.2‖ * w q.2) ≤ w q.1 * w q.2 := by
    dsimp only [w]
    exact mul_le_mul (mul_le_of_le_one_left (norm_nonneg _) hc₁)
      (mul_le_of_le_one_left (norm_nonneg _) hc₂) (by positivity) (by positivity)
  split_ifs with hsq
  · calc
      _ ≤ w q.1 * w q.2 * X := mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg _)
      _ ≤ _ := by
        rw [mul_comm (w q.1 * w q.2)]
        exact le_add_of_nonneg_right (by positivity [log_nonneg (hm₁.trans hmb)])
  · have hlog := log_le_log (zero_lt_one.trans_le hm₁) hmb
    have hroot := sqrt_le_sqrt hmb
    simp only [mul_zero, zero_add]
    calc
      _ ≤ (w q.1 * w q.2) * (2 * √m * (1 + log m)) :=
        mul_le_mul hw (min_le_right _ _) (by positivity [log_nonneg hm₁]) (by positivity)
      _ ≤ (w q.1 * w q.2) * (2 * √b * (1 + log b)) := by
        gcongr
      _ = _ := by ring

/-- The second moment of the normalized Gaussian theta series twisted by `J(-v | n°)` is
bounded by `C * max X u⁻² * u^(-2δ)` over `1 ≤ v ≤ X`, with `C` independent of the
coefficients, scale and numerator cutoff. Here `n°` is the odd part of `n`. -/
theorem exists_sum_norm_gaussianThetaSeries_jacobiSym_sq_le (j : Fin 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C ≥ 0, ∀ (X : ℕ) (c : ℕ → ℂ), (∀ n : ℕ+, ‖c n‖ ≤ 1) → ∀ u ≥ 0,
      (∑ v ∈ Icc 1 X, ‖gaussianThetaSeries j
        (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2) ≤
        C * max (X : ℝ) (u⁻¹ ^ 2) * u ^ (-2 * δ) := by
  classical
  obtain ⟨A, hA, hdiag⟩ := exists_summable_and_mul_tsum_gaussianMonomial_isSquare_ordCompl_le hδ
  obtain ⟨B, hB, hoff⟩ := exists_summable_and_mul_tsum_gaussianMonomial_sqrt_mul_log_le hδ
  refine ⟨A + 2 * B, by positivity, fun X c hc u hu ↦ ?_⟩
  rcases hu.eq_or_lt with rfl | hu
  · simp [gaussianThetaSeries_def, Real.zero_rpow (by linarith : -(2 * δ) ≠ 0)]
  let a (n : ℕ+) : ℂ := c n * gaussianMonomial j (n * u)
  let m (n : ℕ+) := ordCompl[2] n.val
  have hm (n : ℕ+) : Odd (m n) :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two n.ne_zero)
  let W (q : ℕ+ × ℕ+) : ℝ := ‖a q.1‖ * ‖a q.2‖ *
    (if IsSquare (m q.1 * m q.2) then (X : ℝ)
      else min X (2 * √(m q.1 * m q.2 : ℕ) * (1 + log (m q.1 * m q.2 : ℕ))))
  obtain ⟨hd, hdle⟩ := hdiag j u hu
  obtain ⟨ho, hole⟩ := hoff j u hu
  have hmajor := (hd.mul_left (X : ℝ)).add (ho.mul_left 2)
  have hpoint (q : ℕ+ × ℕ+) := gaussianPair_jacobiMajorant_le j X q (hc q.1) (hc q.2) u
  have hW : Summable W := by
    refine Summable.of_nonneg_of_le (fun q ↦ ?_) (fun q ↦ ?_) hmajor
    · have hq : (1 : ℝ) ≤ (m q.1 * m q.2 : ℕ) := by exact_mod_cast ((hm q.1).mul (hm q.2)).pos
      dsimp only [W]
      split_ifs <;> positivity [log_nonneg hq]
    · simpa only [W, a, m, Nat.ordCompl_mul, norm_mul, Complex.norm_real] using hpoint q
  have hsum := hW.tsum_le_tsum (fun q ↦ by
    simpa only [W, a, m, Nat.ordCompl_mul, norm_mul, Complex.norm_real] using hpoint q) hmajor
  rw [(hd.mul_left (X : ℝ)).tsum_add (ho.mul_left 2), tsum_mul_left, tsum_mul_left] at hsum
  have hscale : u ^ (-(2 + 2 * δ)) = u⁻¹ ^ 2 * u ^ (-(2 * δ)) := by
    rw [neg_add, rpow_add hu, rpow_neg hu.le, rpow_two, inv_pow]
  simp_rw [gaussianThetaSeries_def, gaussianTheta_def, norm_mul, Complex.norm_real,
    norm_of_nonneg (sqrt_nonneg u), mul_pow, sq_sqrt hu.le, ← mul_sum, mul_right_comm (c _)]
  calc
    _ ≤ u * ∑' q, W q :=
      mul_le_mul_of_nonneg_left
        (sum_norm_sq_tsum_jacobiSym_neg_le m a hm (summable_gaussianTheta hc hu).norm X) hu.le
    _ ≤ (X : ℝ) * (A * u ^ (-(2 * δ))) + 2 * (B * u ^ (-(2 + 2 * δ))) := by
      grw [hsum]
      rw [mul_add, mul_left_comm u (X : ℝ), mul_left_comm u 2]
      gcongr
    _ ≤ _ := by
      rw [hscale, neg_mul]
      calc
        _ ≤ max (X : ℝ) (u⁻¹ ^ 2) * (A * u ^ (-(2 * δ))) +
            2 * (B * (max (X : ℝ) (u⁻¹ ^ 2) * u ^ (-(2 * δ)))) := by
          gcongr
          · exact le_max_left _ _
          · exact le_max_right _ _
        _ = _ := by ring

/-- At scales `u ≥ 1 / T`, the Jacobi-twisted theta second moment over the numerators
`1 ≤ v ≤ T²` is at most `C * T² * u^(-2δ)`. -/
theorem exists_sum_norm_gaussianThetaSeries_jacobiSym_sq_le_cutoff
    (j : Fin 2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C ≥ 0, ∀ (c : ℕ → ℂ), (∀ n : ℕ+, ‖c n‖ ≤ 1) → ∀ {T : ℝ}, 0 ≤ T → ∀ {u : ℝ}, T⁻¹ ≤ u →
      (∑ v ∈ Icc 1 ⌊T ^ 2⌋₊, ‖gaussianThetaSeries j
        (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2) ≤
        C * T ^ 2 * u ^ (-2 * δ) := by
  obtain ⟨C, hC, h⟩ := exists_sum_norm_gaussianThetaSeries_jacobiSym_sq_le j hδ
  refine ⟨C, hC, fun c hc T hT u hu ↦ ?_⟩
  rcases hT.eq_or_lt with rfl | hT
  · simp
  have hu₀ := (inv_pos.mpr hT).trans_le hu
  refine (h _ c hc _ hu₀.le).trans ?_
  have hInv : u⁻¹ ≤ T := inv_le_of_inv_le₀ hT hu
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (max_le (Nat.floor_le (sq_nonneg T)) (pow_le_pow_left₀ (by positivity) hInv 2)) hC)
    (by positivity)

end TauCeti
