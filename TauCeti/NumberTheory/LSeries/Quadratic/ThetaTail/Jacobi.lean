/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.Quadratic.ThetaTail.MeanSquare
import TauCeti.NumberTheory.LegendreSymbol.JacobiSymbol.SeriesMeanSquare
import TauCeti.NumberTheory.LSeries.Quadratic.GaussianPairBounds

/-!
# Averaging Gaussian theta tails over Jacobi numerators

For a fixed Gaussian scale, separate the pairs with square odd part from the other pairs.
The former use the trivial correlation bound, and the latter use Pólya–Vinogradov.
Integrating the resulting mean-square estimate gives a first moment for the joint tails,
including their Möbius-weighted terms.

The two estimates correspond to `New.sum_sq_thetaSeries_jacobiSym_le` and
`New.sum_thetaTailIntegral_le` in `grh/src/Lib/Analytic/QuadraticTwist.lean` of
[lsernau/grh-lean](https://github.com/lsernau/grh-lean), revision `72fead1`.
-/

public section

open MeasureTheory Real Set
open scoped Nat

namespace TauCeti

private theorem gaussianPair_correlation_le (j : Fin 2) (u : ℝ) (K : ℕ)
    {a : ℕ+ → ℂ} (ha : ∀ n : ℕ+, ‖a n‖ ≤ ‖gaussianMonomial j (n * u)‖)
    (p : ℕ+ × ℕ+) :
    let m := ordCompl[2] ((p.1 : ℕ) * p.2)
    let W := ‖gaussianMonomial j (p.1 * u)‖ * ‖gaussianMonomial j (p.2 * u)‖
    ‖a p.1‖ * ‖a p.2‖ * (if IsSquare m then (K : ℝ)
      else min K (2 * √m * (1 + log m))) ≤
      K * (if IsSquare m then W else 0) +
        2 * (W * (√((p.1 : ℝ) * p.2) * (1 + log ((p.1 : ℝ) * p.2)))) := by
  dsimp only
  let m := ordCompl[2] ((p.1 : ℕ) * p.2)
  have hm : 0 < m := Nat.ordCompl_pos 2 (mul_ne_zero p.1.ne_zero p.2.ne_zero)
  have h₁ : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have he : (m : ℝ) ≤ (p.1 : ℝ) * p.2 := by
    exact_mod_cast Nat.le_of_dvd (mul_pos p.1.pos p.2.pos) (Nat.ordCompl_dvd _ 2)
  split_ifs with h
  · refine (mul_le_mul_of_nonneg_right (mul_le_mul (ha _) (ha _) (norm_nonneg _)
      (norm_nonneg _)) (Nat.cast_nonneg K)).trans ?_
    rw [mul_comm _ ((K : ℝ))]
    exact le_add_of_nonneg_right (by positivity [log_nonneg (h₁.trans he)])
  · simp only [mul_zero, zero_add]
    refine (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans ?_
    calc
      _ = 2 * ((‖a p.1‖ * ‖a p.2‖) * (√m * (1 + log m))) := by ring
      _ ≤ _ := by gcongr <;> exact ha _

-- Compare the second moment with the two Gaussian pair sums before estimating their scale.
private theorem sum_norm_sq_gaussianThetaSeries_jacobiSym_le_pair_sums
    (j : Fin 2) {c : ℕ → ℂ} (hc : ∀ n : ℕ+, ‖c n‖ ≤ 1) {u : ℝ} (hu : 0 < u) (K : ℕ) :
    let W := fun p : ℕ+ × ℕ+ ↦ ‖gaussianMonomial j (p.1 * u)‖ * ‖gaussianMonomial j (p.2 * u)‖
    let D := fun p : ℕ+ × ℕ+ ↦ if IsSquare (ordCompl[2] ((p.1 : ℕ) * p.2)) then W p else 0
    let O := fun p : ℕ+ × ℕ+ ↦ W p * (√((p.1 : ℝ) * p.2) * (1 + log ((p.1 : ℝ) * p.2)))
    Summable D → Summable O →
      ∑ v ∈ Finset.Icc 1 K,
        ‖gaussianThetaSeries j (fun n ↦ c n * jacobiSym (-(v : ℤ)) (ordCompl[2] n)) u‖ ^ 2 ≤
        K * (u * ∑' p, D p) + 2 * (u * ∑' p, O p) := by
  classical
  intro W D O hd ho
  let m (n : ℕ+) := ordCompl[2] (n : ℕ)
  let a (n : ℕ+) := c n * (gaussianMonomial j (n * u) : ℂ)
  have hm (n : ℕ+) : Odd (m n) :=
    Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two n.ne_zero)
  have hmoment := sum_norm_sq_tsum_jacobiSym_neg_le m a hm (summable_gaussianTheta hc hu).norm K
  have ha (n : ℕ+) : ‖a n‖ ≤ ‖gaussianMonomial j (n * u)‖ := by
    dsimp [a]
    rw [norm_mul, Complex.norm_real]
    exact mul_le_of_le_one_left (norm_nonneg _) (hc n)
  have hθ (v : ℕ) :
      ‖gaussianThetaSeries j (fun n ↦ c n * jacobiSym (-(v : ℤ)) (ordCompl[2] n)) u‖ ^ 2 =
        u * ‖∑' n : ℕ+, a n * (jacobiSym (-(v : ℤ)) (m n) : ℂ)‖ ^ 2 := by
    rw [gaussianThetaSeries_def, norm_mul, mul_pow, Complex.norm_real,
      Real.norm_of_nonneg (sqrt_nonneg u), sq_sqrt hu.le, gaussianTheta_def]
    simp only [a, m, mul_right_comm (c _)]
  simp_rw [hθ, ← Finset.mul_sum]
  refine (mul_le_mul_of_nonneg_left hmoment hu.le).trans ?_
  calc
    _ ≤ u * ∑' p, ((K : ℝ) * D p + 2 * O p) := by
      apply mul_le_mul_of_nonneg_left _ hu.le
      let F (p : ℕ+ × ℕ+) := ‖a p.1‖ * ‖a p.2‖ *
        (if IsSquare (m p.1 * m p.2) then (K : ℝ)
          else min K (2 * √(m p.1 * m p.2 : ℕ) * (1 + log (m p.1 * m p.2 : ℕ))))
      have hpos (p) : 0 ≤ F p := by
        have h₁ : (1 : ℝ) ≤ (m p.1 * m p.2 : ℕ) := by
          exact_mod_cast ((hm p.1).mul (hm p.2)).pos
        dsimp only [F]
        split_ifs <;> positivity [log_nonneg h₁]
      have hle (p) : F p ≤ (K : ℝ) * D p + 2 * O p := by
        simpa only [F, D, O, W, m, ← Nat.ordCompl_mul] using
          gaussianPair_correlation_le j u K ha p
      have hsum : Summable (fun p ↦ (K : ℝ) * D p + 2 * O p) :=
        (hd.mul_left (K : ℝ)).add (ho.mul_left 2)
      exact (Summable.of_nonneg_of_le hpos hle hsum).tsum_le_tsum hle hsum
    _ = _ := by
      rw [Summable.tsum_add (hd.mul_left (K : ℝ)) (ho.mul_left 2)]
      simp only [tsum_mul_left]
      ring

/-- The second moment over `1 ≤ v ≤ T²` of the normalized Gaussian theta series with
coefficients `c(n) J(-v | n°)` is at most `C T² u⁻²ᵟ` for `u ≥ 1/T`. The constant is
uniform in the parity, scales and unit-bounded coefficients. -/
theorem exists_sum_norm_sq_gaussianThetaSeries_jacobiSym_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (j : Fin 2) {c : ℕ → ℂ}, (∀ n : ℕ+, ‖c n‖ ≤ 1) →
      ∀ {T u : ℝ}, 0 < T → T⁻¹ ≤ u →
        ∑ v ∈ Finset.Icc 1 ⌊T ^ 2⌋₊,
          ‖gaussianThetaSeries j (fun n ↦ c n * jacobiSym (-(v : ℤ)) (ordCompl[2] n)) u‖ ^ 2 ≤
          C * T ^ 2 * u ^ (-2 * δ) := by
  obtain ⟨A, hA, hdiag⟩ := exists_summable_and_mul_tsum_gaussianMonomial_isSquare_ordCompl_le hδ
  obtain ⟨B, hB, hoff⟩ := exists_summable_and_mul_tsum_gaussianMonomial_sqrt_mul_log_le hδ
  refine ⟨A + 2 * B, by positivity, fun j c hc T u hT hTu ↦ ?_⟩
  have hu := (inv_pos.mpr hT).trans_le hTu
  obtain ⟨hd, hds⟩ := hdiag j u hu
  obtain ⟨ho, hos⟩ := hoff j u hu
  have hK : (⌊T ^ 2⌋₊ : ℝ) ≤ T ^ 2 := Nat.floor_le (sq_nonneg _)
  have hscale : u ^ (-(2 + 2 * δ)) ≤ T ^ 2 * u ^ (-(2 * δ)) := by
    rw [neg_add, rpow_add hu, rpow_neg hu.le (2 : ℝ), rpow_two, ← inv_pow]
    have hi : u⁻¹ ≤ T := by simpa using inv_anti₀ (inv_pos.mpr hT) hTu
    gcongr
  refine (sum_norm_sq_gaussianThetaSeries_jacobiSym_le_pair_sums j hc hu _ hd ho).trans ?_
  have hdK := mul_le_mul_of_nonneg_left hds (Nat.cast_nonneg (α := ℝ) ⌊T ^ 2⌋₊)
  have hKA := mul_le_mul_of_nonneg_right hK (by positivity : 0 ≤ A * u ^ (-(2 * δ)))
  have hoT := hos.trans (mul_le_mul_of_nonneg_left hscale hB.le)
  have he : -(2 * δ) = -2 * δ := by ring
  rw [he] at hdK hKA hoT
  calc
    _ ≤ T ^ 2 * (A * u ^ (-2 * δ)) + 2 * (B * (T ^ 2 * u ^ (-2 * δ))) :=
      add_le_add (hdK.trans hKA) (mul_le_mul_of_nonneg_left hoT (by norm_num))
    _ = _ := by ring

/-- For coefficients bounded by one on positive indices, the summed joint Gaussian tails of
Jacobi twists over `1 ≤ v ≤ T²` are at most `C T^(2+δ)`, uniformly in the parity and `T > 0`. -/
theorem exists_sum_quadraticTwistGaussianThetaTailIntegral_jacobiSym_le {δ : ℝ} (hδ : 0 < δ) :
    ∃ C > 0, ∀ (j : Fin 2) {c : ℕ → ℂ}, (∀ n : ℕ+, ‖c n‖ ≤ 1) → ∀ {T : ℝ}, 0 < T →
      ∑ v ∈ Finset.Icc 1 ⌊T ^ 2⌋₊, quadraticTwistGaussianThetaTailIntegral j
        (fun n ↦ c n * jacobiSym (-(v : ℤ)) (ordCompl[2] n)) T ≤ C * T ^ (2 + δ) := by
  obtain ⟨C, hC, hm⟩ := exists_sum_norm_sq_gaussianThetaSeries_jacobiSym_le hδ
  refine ⟨2 * √C / δ, by positivity, fun j c hc T hT ↦ ?_⟩
  apply sum_quadraticTwistGaussianThetaTailIntegral_jacobiSym_le hT hδ hc
  intro b hb
  filter_upwards [ae_restrict_mem measurableSet_Ioi (μ := volume) (s := Ioi T⁻¹)] with u hu
  exact hm j hb hT (mem_Ioi.mp hu).le

end TauCeti
