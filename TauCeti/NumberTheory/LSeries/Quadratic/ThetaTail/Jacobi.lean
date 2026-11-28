/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.Basic
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.SeriesMeanSquare
import TauCeti.NumberTheory.LSeries.Quadratic.GaussianPairBounds
import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.MeanSquare

/-!
# Mean bounds for Jacobi-twisted Gaussian theta series

Averaging the squared norms over Jacobi numerators splits the resulting pair sum into products
with square odd part and products with nonsquare odd part. The former use the trivial bound for
the numerator sum and the latter use Pólya–Vinogradov. Integrating the resulting second moment
bounds the sum of the joint theta tails used in zero detection for quadratic twists.

The estimates are those of `New.sum_sq_thetaSeries_jacobiSym_le` and
`New.sum_thetaTailIntegral_le` in `grh/src/Lib/Analytic/QuadraticTwist.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean/tree/72fead102f663d5c7a407964a13dc0cf9d977207).
-/

public section

open Real
open scoped Nat

namespace TauCeti

/-- Bound the theta correlation by the square-odd-part contribution plus the unrestricted
Gaussian pair weight for the Pólya–Vinogradov bound. -/
private theorem thetaPair_le {c : ℕ → ℂ} (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1)
    (j : Fin 2) (u : ℝ) (K : ℕ) (p : ℕ+ × ℕ+) :
    let x := gaussianMonomial j (p.1 * u)
    let y := gaussianMonomial j (p.2 * u)
    let m := ordCompl[2] ((p.1 : ℕ) * p.2)
    ‖c p.1 * (x : ℂ)‖ * ‖c p.2 * (y : ℂ)‖ *
        (if IsSquare m then (K : ℝ) else min K (2 * √m * (1 + log m))) ≤
      K * (if IsSquare m then ‖x‖ * ‖y‖ else 0) +
        2 * (‖x‖ * ‖y‖ * (√((p.1 : ℝ) * p.2) * (1 + log ((p.1 : ℝ) * p.2)))) := by
  intro x y m
  have hm₀ : 0 < m := Nat.ordCompl_pos 2 (mul_ne_zero p.1.ne_zero p.2.ne_zero)
  have hm₁ : (1 : ℝ) ≤ m := by exact_mod_cast hm₀
  have hm : (m : ℝ) ≤ (p.1 : ℝ) * p.2 := by
    exact_mod_cast Nat.le_of_dvd (Nat.mul_pos p.1.pos p.2.pos) (Nat.ordCompl_dvd _ 2)
  have hcoeff (n : ℕ+) (z : ℝ) : ‖c n * (z : ℂ)‖ ≤ ‖z‖ := by
    rw [norm_mul, Complex.norm_real]
    exact mul_le_of_le_one_left (norm_nonneg _) (hc n)
  have hprod : ‖c p.1 * (x : ℂ)‖ * ‖c p.2 * (y : ℂ)‖ ≤ ‖x‖ * ‖y‖ := by
    gcongr <;> apply hcoeff
  split_ifs with hsq
  · calc
      _ ≤ (‖x‖ * ‖y‖) * K := by gcongr
      _ ≤ _ := by
        rw [mul_comm (‖x‖ * ‖y‖)]
        exact le_add_of_nonneg_right (by positivity [log_nonneg (hm₁.trans hm)])
  · have hlog := log_le_log (zero_lt_one.trans_le hm₁) hm
    have hroot := sqrt_le_sqrt hm
    calc
      _ ≤ (‖x‖ * ‖y‖) * (2 * √m * (1 + log m)) := by
        apply mul_le_mul hprod (min_le_right _ _) _ (by positivity)
        exact le_min (by positivity) (by positivity [log_nonneg hm₁])
      _ ≤ (‖x‖ * ‖y‖) * (2 * √((p.1 : ℝ) * p.2) * (1 + log ((p.1 : ℝ) * p.2))) := by
        gcongr
      _ = _ := by ring

/-- For every `δ > 0`, the second moment of the Jacobi-twisted Gaussian theta series over
`1 ≤ v ≤ T²` is at most `C T² u⁻²ᵟ` at every scale `u ≥ 1/T`. The constant is uniform over
both parities and all coefficient sequences of norm at most one on positive indices. -/
theorem exists_sum_norm_gaussianThetaSeries_jacobiSym_sq_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (j : Fin 2) (c : ℕ → ℂ), (∀ n : ℕ+, ‖c n‖ ≤ 1) →
      ∀ {T u : ℝ}, 0 < T → T⁻¹ ≤ u →
        ∑ v ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, ‖gaussianThetaSeries j
          (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) u‖ ^ 2 ≤
          C * T ^ 2 * u ^ (-(2 * δ)) := by
  obtain ⟨A, hA, hdiag⟩ := exists_summable_and_mul_tsum_gaussianMonomial_isSquare_ordCompl_le hδ
  obtain ⟨B, hB, hoff⟩ := exists_summable_and_mul_tsum_gaussianMonomial_sqrt_mul_log_le hδ
  refine ⟨A + 2 * B, by positivity, fun j c hc T u hT hTu ↦ ?_⟩
  have hu := (inv_pos.mpr hT).trans_le hTu
  let K := ⌊T ^ 2⌋₊
  let a (n : ℕ+) := c n * (gaussianMonomial j (n * u) : ℂ)
  let m (n : ℕ+) := ordCompl[2] n.val
  have hm (n : ℕ+) : Odd (m n) :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two n.ne_zero)
  have hmoment := sum_norm_sq_tsum_jacobiSym_neg_le m a hm
    (summable_gaussianTheta (j := j) hc hu).norm K
  let w (p : ℕ+ × ℕ+) :=
    let b := ordCompl[2] ((p.1 : ℕ) * p.2)
    ‖a p.1‖ * ‖a p.2‖ * (if IsSquare b then (K : ℝ) else min K (2 * √b * (1 + log b)))
  obtain ⟨hd, hdle⟩ := hdiag j u hu
  obtain ⟨ho, hole⟩ := hoff j u hu
  have hpair := fun p ↦ thetaPair_le hc j u K p
  have hmajor := (hd.mul_left (K : ℝ)).add (ho.mul_left 2)
  have hw := Summable.of_nonneg_of_le (g := w) (fun p ↦ by
    have hp : (1 : ℝ) ≤ (m p.1 * m p.2 : ℕ) := by exact_mod_cast ((hm p.1).mul (hm p.2)).pos
    simp only [w, Nat.ordCompl_mul]
    split_ifs <;> positivity [log_nonneg hp]) hpair hmajor
  have hsum := hw.tsum_le_tsum hpair hmajor
  rw [(hd.mul_left (K : ℝ)).tsum_add (ho.mul_left 2), tsum_mul_left, tsum_mul_left] at hsum
  have hK : (K : ℝ) ≤ T ^ 2 := Nat.floor_le (sq_nonneg T)
  have hi : u ^ (-(2 + 2 * δ)) ≤ T ^ 2 * u ^ (-(2 * δ)) := by
    rw [neg_add, rpow_add hu, rpow_neg hu.le, rpow_two, ← inv_pow]
    gcongr
    simpa using (one_div_le_one_div_of_le (inv_pos.mpr hT) hTu)
  -- Squaring the theta normalization gives the common factor `u`.
  simp only [gaussianThetaSeries_def, gaussianTheta_def, norm_mul, Complex.norm_real,
    norm_of_nonneg (sqrt_nonneg u), mul_pow, sq_sqrt hu.le, ← Finset.mul_sum, mul_right_comm (c _)]
  calc
    _ ≤ u * ∑' p, w p := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      simpa only [w, Nat.ordCompl_mul, a, m] using hmoment
    _ ≤ (K : ℝ) * (A * u ^ (-(2 * δ))) + 2 * (B * u ^ (-(2 + 2 * δ))) := by
      grw [hsum]
      rw [mul_add, mul_left_comm u (K : ℝ), mul_left_comm u 2]
      gcongr
    _ ≤ _ := by
      calc
        _ ≤ T ^ 2 * (A * u ^ (-(2 * δ))) + 2 * (B * (T ^ 2 * u ^ (-(2 * δ)))) := by gcongr
        _ = _ := by ring

/-- For every `δ > 0`, the sum of the joint theta tails of the Jacobi twists over `1 ≤ v ≤ T²`
is at most `C T^(2 + δ)`. The constant is independent of `T`, the parity, and the unit-bounded
coefficient sequence. -/
theorem exists_sum_quadraticTwistGaussianThetaTailIntegral_jacobiSym_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (j : Fin 2) (c : ℕ → ℂ), (∀ n : ℕ+, ‖c n‖ ≤ 1) →
      ∀ {T : ℝ}, 0 < T →
        ∑ v ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, quadraticTwistGaussianThetaTailIntegral j
          (fun n ↦ c n * (jacobiSym (-(v : ℤ)) (ordCompl[2] n) : ℂ)) T ≤ C * T ^ (2 + δ) := by
  obtain ⟨C, hC, hmoment⟩ := exists_sum_norm_gaussianThetaSeries_jacobiSym_sq_le hδ
  refine ⟨2 * √C / δ, by positivity, fun j c hc T hT ↦ ?_⟩
  apply sum_quadraticTwistGaussianThetaTailIntegral_jacobiSym_le hT hδ hc
  intro b hb
  exact (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono fun _ hu ↦ by
    simpa only [neg_mul] using hmoment j b hb hT (Set.mem_Ioi.mp hu).le

end TauCeti
