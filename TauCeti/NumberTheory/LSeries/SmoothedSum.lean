/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.Analysis.MellinInversion
public import TauCeti.Analysis.MellinTransform.SmoothCutoff
public import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Smoothed coefficient sums as Mellin inverses

A Dirichlet series `∑ aᵢ pᵢ⁻ˢ` that converges absolutely on the line `Re s = σ` determines every
smoothed sum of its coefficients by a vertical integral. If `F` is integrable on that line, then
for `x > 0`

`∑ᵢ aᵢ · mellinInv σ F (pᵢ x) = mellinInv σ (fun s ↦ F(s) ∑ᵢ aᵢ pᵢ⁻ˢ) x`:

the weight `mellinInv σ F` evaluated at the points `pᵢ x` is summed against the coefficients by
multiplying `F` with the series. The interchange of the sum and the integral is justified by the
absolute convergence of the series on the line and the integrability of `F` there.

Two weights are recorded.

* For `F = Γ` Mellin inversion gives `e^{-y}` (`Complex.mellinInv_Gamma`), so the exponentially
  smoothed sum `∑ᵢ aᵢ e^{-pᵢ x}` is `mellinInv σ (fun s ↦ Γ(s) ∑ᵢ aᵢ pᵢ⁻ˢ) x`, the inverse of
  Mathlib's `hasSum_mellin`. Shifting the line of integration to the left of a pole of the series
  and estimating the shifted integral is the smoothing argument behind Goldfeld's proof of
  Siegel's lower bound for `L(1, χ)`.
* For `F` the Mellin transform of the smoothed cutoff `χ_ε = smoothCutoff ν ε` of a `C¹` bump `ν`,
  Mellin inversion gives `χ_ε` itself, so
  `∑ₙ a(n) χ_ε(n / X) = mellinInv σ (fun s ↦ L(a, s) · mellin χ_ε s) X⁻¹`, that is
  `(2πi)⁻¹ ∫_{(σ)} L(a, s) 𝓜χ_ε(s) Xˢ ds`. The sum is finite, since `χ_ε` vanishes at `0` and on
  `[2^ε, ∞)`. For coefficients with `|a(n)| ≤ B log(n + 1)` the smoothed sum differs from the sharp
  sum `∑_{n ≤ X} a(n)` by at most `3B (2εX + 1) log X`: the two weights agree off the window
  `(2^{-ε}X, 2^ε X)`, which holds at most `2εX + 1` integers. With `a = Λ` this compares the
  smoothed Chebyshev function with `ψ`. Moving the line of integration into a zero-free region
  of `L(a, s)` turns these identities into prime number theorems with an error term.

## Main results

* `TauCeti.hasSum_mul_mellinInv`: the smoothed sum of a general Dirichlet series against the
  weight `mellinInv σ F`.
* `TauCeti.LSeries.hasSum_mul_mellinInv`: the same formula for `LSeries`.
* `TauCeti.hasSum_mellinInv_Gamma_mul`, `TauCeti.LSeries.hasSum_mellinInv_Gamma_mul_LSeries`: the
  exponentially smoothed sums.
* `TauCeti.LSeries.hasSum_mul_smoothCutoff`: the sum `∑ₙ a(n) χ_ε(n / X)` as an inverse Mellin
  integral.
* `TauCeti.norm_sum_sub_tsum_mul_smoothCutoff_le`: comparison of the smoothed sum with the sharp
  sum.
* `TauCeti.norm_psi_sub_tsum_vonMangoldt_mul_smoothCutoff_le`: the same for `ψ`.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.9 (Siegel's theorem by smoothing with
  `Γ(s) xˢ`).
* A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd* blueprint, §4.5 (Definition 4.5.2,
  Theorems 4.5.2 and 4.5.3, the smoothed Chebyshev function),
  <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>.
-/

public section

open Real Set MeasureTheory Filter
open Complex hiding exp continuous_exp

namespace TauCeti

/-- **Smoothed sums of a Dirichlet series.** If `∑ aᵢ pᵢ⁻ˢ` converges absolutely on the line
`Re s = σ` and `F` is integrable on that line, then for `x > 0` the sum of the coefficients
weighted by `mellinInv σ F` at the points `pᵢ x` is the Mellin inverse on that line of
`F(s) ∑ᵢ aᵢ pᵢ⁻ˢ`. -/
theorem hasSum_mul_mellinInv {ι : Type*} [Countable ι] {a : ι → ℂ} {p : ι → ℝ} {σ : ℝ}
    {F : ℂ → ℂ} (hF : VerticalIntegrable F σ) (hp : ∀ i, a i = 0 ∨ 0 < p i)
    (h_sum : Summable fun i ↦ ‖a i‖ / p i ^ σ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun i ↦ a i * mellinInv σ F (p i * x))
      (mellinInv σ (fun s ↦ F s * ∑' i, a i / (p i : ℂ) ^ s) x) := by
  -- the `i`-th term of the integrand, written as a multiple of the integrand of `mellinInv σ F`
  set g : ι → ℝ → ℂ := fun i t ↦ a i * (((p i * x : ℝ) : ℂ) ^ (-(σ + t * I)) * F (σ + t * I))
  have hg (i : ι) (t : ℝ) : (x : ℂ) ^ (-(σ + t * I)) * (F (σ + t * I) *
      (a i / (p i : ℂ) ^ (σ + t * I))) = g i t := by
    rcases hp i with h | h
    · simp [g, h]
    simp only [g]
    rw [ofReal_mul, ofReal_mul_cpow h.le, cpow_neg (p i : ℂ)]
    field_simp
  have hint (i : ι) : Integrable (g i) := by
    rcases hp i with h | h
    · simp [g, h]
    simpa only [smul_eq_mul] using ((hF.integrable_cpow_smul (mul_pos h hx)).const_mul (a i))
  -- the integrals of the norms are `x^{-σ} ‖aᵢ‖ / pᵢ^σ` times the integral of `‖F‖` on the line
  have hnorm (i : ι) : ∫ t, ‖g i t‖ = x ^ (-σ) * (‖a i‖ / p i ^ σ) *
      ∫ t : ℝ, ‖F (σ + t * I)‖ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    rcases hp i with h | h
    · simp [g, h]
    simp only [g, norm_mul, norm_cpow_eq_rpow_re_of_pos (mul_pos h hx)]
    rw [show (-(↑σ + ↑t * I)).re = -σ by simp, Real.mul_rpow h.le hx.le, Real.rpow_neg h.le]
    field_simp
  have key := hasSum_integral_of_summable_integral_norm hint
    (by simpa only [hnorm] using (h_sum.mul_left _).mul_right _)
  -- the Mellin inverse is `1 / 2π` times the integral of the sum
  have hfull : mellinInv σ (fun s ↦ F s * ∑' i, a i / (p i : ℂ) ^ s) x =
      (1 / (2 * π)) • ∫ t, ∑' i, g i t := by
    rw [mellinInv]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    simp only [smul_eq_mul, ← hg, ← tsum_mul_left]
  rw [hfull]
  convert key.const_smul (1 / (2 * π)) using 1
  ext i
  simp only [g, mellinInv, smul_eq_mul, integral_const_mul]
  rw [mul_smul_comm]

/-- **Exponentially smoothed sums of a Dirichlet series.** If `∑ aᵢ pᵢ⁻ˢ` converges absolutely on
the line `Re s = σ > 0`, then for `x > 0` the exponentially smoothed sum `∑ᵢ aᵢ e^{-pᵢ x}` is the
Mellin inverse on that line of `Γ(s) ∑ᵢ aᵢ pᵢ⁻ˢ`. This is the inverse of `hasSum_mellin`. -/
theorem hasSum_mellinInv_Gamma_mul {ι : Type*} [Countable ι] {a : ι → ℂ} {p : ι → ℝ} {σ : ℝ}
    (hp : ∀ i, a i = 0 ∨ 0 < p i) (hσ : 0 < σ) (h_sum : Summable fun i ↦ ‖a i‖ / p i ^ σ)
    {x : ℝ} (hx : 0 < x) :
    HasSum (fun i ↦ a i * rexp (-p i * x))
      (mellinInv σ (fun s ↦ Gamma s * ∑' i, a i / (p i : ℂ) ^ s) x) := by
  have hΓ := verticalIntegrable_Gamma (σ := σ) fun n h ↦ by
    linarith [show (0 : ℝ) ≤ n from n.cast_nonneg]
  convert hasSum_mul_mellinInv hΓ hp h_sum hx using 1
  ext i
  rcases hp i with h | h
  · simp [h]
  · rw [mellinInv_Gamma hσ (mul_pos h hx), neg_mul]

/-- **Smoothed sums of an `LSeries`.** If `f 0 = 0` and the L-series of `f` converges absolutely on
the line `Re s = σ > 0`, then for `x > 0` the smoothed sum `∑ₙ f(n) e^{-n x}` is the Mellin
inverse on that line of `Γ(s) L(f, s)`. -/
theorem LSeries.hasSum_mellinInv_Gamma_mul_LSeries {f : ℕ → ℂ} (hf : f 0 = 0) {σ : ℝ}
    (hσ : 0 < σ) (hs : LSeriesSummable f σ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ f n * rexp (-n * x)) (mellinInv σ (fun s ↦ Gamma s * LSeries f s) x) := by
  have hp (n : ℕ) : f n = 0 ∨ 0 < (n : ℝ) := by
    rcases eq_or_ne n 0 with rfl | hn
    · exact Or.inl hf
    · exact Or.inr (by positivity)
  have h_sum : Summable fun n : ℕ ↦ ‖f n‖ / (n : ℝ) ^ σ := by
    refine hs.norm.congr fun n ↦ ?_
    rw [_root_.LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [hf]
    · simp [hn]
  convert hasSum_mellinInv_Gamma_mul hp hσ h_sum hx using 3 with s
  rw [LSeries_def₀ hf]
  simp

/-- **Smoothed sums of an `LSeries`.** If the L-series of `f` converges absolutely on the line
`Re s = σ` and `F` is integrable on that line, then for `x > 0` the sum `∑ₙ f(n) · w(n x)` with
the weight `w = mellinInv σ F` is the Mellin inverse on that line of `F(s) L(f, s)`. The value
`f 0` plays no role, since `w(0) = 0`. -/
theorem LSeries.hasSum_mul_mellinInv {f : ℕ → ℂ} {σ : ℝ} {F : ℂ → ℂ}
    (hF : VerticalIntegrable F σ) (hs : LSeriesSummable f σ) {x : ℝ} (hx : 0 < x) :
    HasSum (fun n : ℕ ↦ f n * mellinInv σ F (n * x))
      (mellinInv σ (fun s ↦ F s * LSeries f s) x) := by
  set a : ℕ → ℂ := fun n ↦ if n = 0 then 0 else f n
  have hp (n : ℕ) : a n = 0 ∨ 0 < (n : ℝ) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp [a]
    · exact Or.inr (by positivity)
  have h_sum : Summable fun n : ℕ ↦ ‖a n‖ / (n : ℝ) ^ σ := by
    refine hs.norm.congr fun n ↦ ?_
    rw [_root_.LSeries.norm_term_eq]
    rcases eq_or_ne n 0 with rfl | hn <;> simp [a, *]
  have hL (s : ℂ) : ∑' n : ℕ, a n / ((n : ℝ) : ℂ) ^ s = LSeries f s := by
    refine tsum_congr fun n ↦ ?_
    rw [_root_.LSeries.term_def]
    rcases eq_or_ne n 0 with rfl | hn <;> simp [a, *]
  convert TauCeti.hasSum_mul_mellinInv hF hp h_sum hx using 1
  · ext n
    rcases eq_or_ne n 0 with rfl | hn <;> simp [a, *]
  · simp only [hL]

/-- **The smoothed summatory function as an inverse Mellin integral.** Let `ν` be of class `C¹` on
`(0, ∞)` and supported in `[1/2, 2]`, `ε > 0`, and let the L-series of `f` converge absolutely on
the line `Re s = σ > 0`. For `X > 0` the sum of `f(n)` weighted by the smoothed cutoff
`χ_ε = smoothCutoff ν ε` at `n / X` is the inverse Mellin integral on that line of
`L(f, s) · mellin χ_ε s`, evaluated at `X⁻¹`: it is `(2πi)⁻¹ ∫_{(σ)} L(f, s) 𝓜χ_ε(s) Xˢ ds`. The
sum has finitely many nonzero terms, since `χ_ε` vanishes at `0` and on `[2^ε, ∞)`. -/
theorem LSeries.hasSum_mul_smoothCutoff {f : ℕ → ℂ} {ν : ℝ → ℝ} {ε σ X : ℝ}
    (hν : ContDiffOn ℝ 1 ν (Ioi 0)) (hνs : Function.support ν ⊆ Icc (1 / 2) 2) (hε : 0 < ε)
    (hσ : 0 < σ) (hs : LSeriesSummable f σ) (hX : 0 < X) :
    HasSum (fun n : ℕ ↦ f n * smoothCutoff ν ε (n / X))
      (mellinInv σ (fun s ↦ LSeries f s * mellin (fun x ↦ (smoothCutoff ν ε x : ℂ)) s) X⁻¹) := by
  have h := hasSum_mul_mellinInv (verticalIntegrable_mellin_smoothCutoff hν hνs hε hσ) hs
    (inv_pos.mpr hX)
  simp only [mul_comm (mellin _ _)] at h
  convert h using 1
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [mellinInv_mellin_smoothCutoff hν hνs hε hσ (by positivity), div_eq_mul_inv]

/-- For `0 ≤ ε ≤ 1`, `2^ε - 2^{-ε} ≤ 2ε`: by Bernoulli's inequality `2^ε ≤ 1 + ε`, and then
`2^{-ε} ≥ (1 + ε)⁻¹ ≥ 1 - ε`. -/
private lemma two_rpow_sub_two_rpow_neg_le {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (2 : ℝ) ^ ε - 2 ^ (-ε) ≤ 2 * ε := by
  have h1 : (2 : ℝ) ^ ε ≤ 1 + ε := by
    simpa [one_add_one_eq_two] using rpow_one_add_le_one_add_mul_self (s := 1) (by norm_num) hε0 hε1
  have hpos : (0 : ℝ) < 2 ^ ε := by positivity
  have h2 : 1 - ε ≤ (2 : ℝ) ^ (-ε) := by
    rw [rpow_neg zero_le_two, ← one_div, le_div_iff₀ hpos]
    nlinarith
  linarith

/-- The open interval `(⌊z⌋₊, ⌈y⌉₊)` of natural numbers has at most `y - z + 1` elements. -/
private lemma card_Ioo_floor_ceil_le {y z : ℝ} (hz : 0 ≤ z) (hzy : z ≤ y) :
    ((Finset.Ioo ⌊z⌋₊ ⌈y⌉₊).card : ℝ) ≤ y - z + 1 := by
  rw [Nat.card_Ioo, Nat.sub_sub]
  rcases le_or_gt ⌈y⌉₊ (⌊z⌋₊ + 1) with h | h
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero]
    linarith
  · rw [Nat.cast_sub h.le]
    push_cast
    linarith [Nat.ceil_lt_add_one (hz.trans hzy), Nat.lt_floor_add_one z]

/-- Outside the window `(2^{-ε}X, 2^ε X)` the sharp weight `1_{0 < n ≤ X}` and the smoothed weight
`χ_ε(n / X)` of a bump agree. -/
private lemma sharp_sub_smoothCutoff_eq_zero {ν : ℝ → ℝ} (hνs : Function.support ν ⊆ Icc (1 / 2) 2)
    (hνm : ∫ x in Ioi 0, ν x / x = 1) {ε X : ℝ} (hε : 0 < ε) (hX : 0 < X) (c : ℂ) {n : ℕ}
    (hn : (n : ℝ) ≤ 2 ^ (-ε) * X ∨ 2 ^ ε * X ≤ n) :
    (if n ∈ Finset.Ioc 0 ⌊X⌋₊ then c else 0) - c * smoothCutoff ν ε (n / X) = 0 := by
  have h1 : (1 : ℝ) < 2 ^ ε := one_lt_rpow (by norm_num) hε
  have h2 : (2 : ℝ) ^ (-ε) < 1 := rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  rcases hn with hn | hn
  · rcases eq_or_ne n 0 with rfl | hn0
    · simp
    have hmem : n ∈ Finset.Ioc 0 ⌊X⌋₊ :=
      Finset.mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hn0, Nat.le_floor (by nlinarith)⟩
    rw [smoothCutoff_eq_one hνs hνm hε (by positivity) ((div_le_iff₀ hX).mpr hn)]
    simp [hmem]
  · have hnot : n ∉ Finset.Ioc 0 ⌊X⌋₊ := fun h ↦ by
      have := (Nat.le_floor_iff hX.le).mp (Finset.mem_Ioc.mp h).2
      nlinarith
    rw [smoothCutoff_eq_zero hνs hε ((le_div_iff₀ hX).mpr hn)]
    simp [hnot]

/-- On the window the sharp and smoothed weights of a bump differ by at most `1`. -/
private lemma norm_sharp_sub_smoothCutoff_le {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x)
    (hνm : ∫ x in Ioi 0, ν x / x = 1) {ε X : ℝ} (hε : 0 < ε) (c : ℂ) (n : ℕ) :
    ‖(if n ∈ Finset.Ioc 0 ⌊X⌋₊ then c else 0) - c * smoothCutoff ν ε (n / X)‖ ≤ ‖c‖ := by
  have hχ0 := smoothCutoff_nonneg hν0 hε.le (n / X)
  have hχ1 := smoothCutoff_le_one hν0 hνm hε (n / X)
  split_ifs
  · rw [← mul_one_sub, norm_mul, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
    exact mul_le_of_le_one_right (norm_nonneg _) (by linarith)
  · rw [zero_sub, norm_neg, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hχ0]
    exact mul_le_of_le_one_right (norm_nonneg _) hχ1

/-- The difference of the sharp and the smoothed sum is a sum over the integers of the window
`(2^{-ε}X, 2^ε X)`. -/
private lemma sum_sub_tsum_mul_smoothCutoff_eq {f : ℕ → ℂ} {ν : ℝ → ℝ}
    (hνs : Function.support ν ⊆ Icc (1 / 2) 2) (hνm : ∫ x in Ioi 0, ν x / x = 1) {ε X : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 0 < X) :
    ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n - ∑' n : ℕ, f n * smoothCutoff ν ε (n / X) =
      ∑ n ∈ Finset.Ioo ⌊2 ^ (-ε) * X⌋₊ ⌈2 ^ ε * X⌉₊,
        ((if n ∈ Finset.Ioc 0 ⌊X⌋₊ then f n else 0) - f n * smoothCutoff ν ε (n / X)) := by
  have h2ε : (2 : ℝ) ^ ε ≤ 2 := by
    simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hε1
  set S := Finset.range (⌊2 * X⌋₊ + 1)
  have hmemT (n : ℕ) : n ∈ Finset.Ioo ⌊2 ^ (-ε) * X⌋₊ ⌈2 ^ ε * X⌉₊ ↔
      2 ^ (-ε) * X < n ∧ (n : ℝ) < 2 ^ ε * X := by
    rw [Finset.mem_Ioo, Nat.floor_lt (by positivity), Nat.lt_ceil]
  -- the smoothed weight vanishes beyond `2X`, so both sums are sums over `S`
  have hS (n : ℕ) (hn : n ∉ S) : f n * smoothCutoff ν ε (n / X) = 0 := by
    rw [Finset.mem_range, not_lt, Nat.add_one_le_iff, Nat.floor_lt (by positivity)] at hn
    rw [smoothCutoff_eq_zero hνs hε ((le_div_iff₀ hX).mpr (by nlinarith)), ofReal_zero, mul_zero]
  have hIS : Finset.Ioc 0 ⌊X⌋₊ ⊆ S := fun n hn ↦ Finset.mem_range.mpr
    (Nat.lt_succ_of_le ((Finset.mem_Ioc.mp hn).2.trans (Nat.floor_mono (by linarith))))
  have hTS : Finset.Ioo ⌊2 ^ (-ε) * X⌋₊ ⌈2 ^ ε * X⌉₊ ⊆ S := fun n hn ↦ Finset.mem_range.mpr
    (Nat.lt_succ_of_le (Nat.le_floor (by nlinarith [((hmemT n).mp hn).2])))
  have hI : ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n =
      ∑ n ∈ S, if n ∈ Finset.Ioc 0 ⌊X⌋₊ then f n else 0 := by
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hIS]
  rw [tsum_eq_sum hS, hI, ← Finset.sum_sub_distrib]
  -- off the window the two weights agree
  refine (Finset.sum_subset hTS fun n _ hn ↦ ?_).symm
  rw [hmemT, not_and_or, not_lt, not_lt] at hn
  exact sharp_sub_smoothCutoff_eq_zero hνs hνm hε hX (f n) hn

/-- **The smoothed sum against the sharp sum.** Let `ν` be a bump (`ν ≥ 0`, supported in
`[1/2, 2]`, of `dx/x`-mass `1`), `0 < ε ≤ 1` and `X ≥ 2`. If `‖f(n)‖ ≤ B log(n + 1)` for `n ≥ 1`,
then the sharp sum `∑_{0 < n ≤ X} f(n)` and the smoothed sum `∑ₙ f(n) χ_ε(n / X)` differ by at most
`3B (2εX + 1) log X`. The two weights agree off `(2^{-ε}X, 2^ε X)`, which holds at most
`2εX + 1` integers, and differ by at most `1` on it. -/
theorem norm_sum_sub_tsum_mul_smoothCutoff_le {f : ℕ → ℂ} {B : ℝ}
    (hf : ∀ n : ℕ, 1 ≤ n → ‖f n‖ ≤ B * Real.log (n + 1)) {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x)
    (hνs : Function.support ν ⊆ Icc (1 / 2) 2) (hνm : ∫ x in Ioi 0, ν x / x = 1) {ε X : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 2 ≤ X) :
    ‖∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n - ∑' n : ℕ, f n * smoothCutoff ν ε (n / X)‖ ≤
      3 * B * (2 * ε * X + 1) * Real.log X := by
  have hX0 : 0 < X := by linarith
  have hB : 0 ≤ B := by
    have h := (norm_nonneg _).trans (hf 1 le_rfl)
    norm_num at h
    exact nonneg_of_mul_nonneg_left h (Real.log_pos one_lt_two)
  have h2ε : (2 : ℝ) ^ ε ≤ 2 := by
    simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hε1
  set T := Finset.Ioo ⌊2 ^ (-ε) * X⌋₊ ⌈2 ^ ε * X⌉₊
  -- on the window each term is at most `‖f n‖ ≤ B log(2X + 1) ≤ 3 B log X`
  have hterm (n : ℕ) (hn : n ∈ T) : ‖(if n ∈ Finset.Ioc 0 ⌊X⌋₊ then f n else 0) -
      f n * smoothCutoff ν ε (n / X)‖ ≤ 3 * B * Real.log X := by
    rw [Finset.mem_Ioo, Nat.floor_lt (by positivity), Nat.lt_ceil] at hn
    have hn0 : 1 ≤ n := Nat.one_le_cast.mp (by
      have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn.1
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at this))
    have hlog : Real.log (n + 1) ≤ 3 * Real.log X := by
      have h3 : Real.log (X ^ 3) = 3 * Real.log X := by rw [Real.log_pow]; norm_num
      rw [← h3]
      have hn2X : (n : ℝ) < 2 * X := by nlinarith
      have hX3 : 4 * X ≤ X ^ 3 := by
        nlinarith [mul_nonneg (mul_nonneg hX0.le (sub_nonneg.2 hX)) (by linarith : (0 : ℝ) ≤ X + 2)]
      exact Real.log_le_log (by positivity) (by linarith)
    calc _ ≤ ‖f n‖ := norm_sharp_sub_smoothCutoff_le hν0 hνm hε (f n) n
      _ ≤ B * Real.log (n + 1) := hf n hn0
      _ ≤ 3 * B * Real.log X := by nlinarith
  have hcard : (T.card : ℝ) ≤ 2 * ε * X + 1 := by
    have hzy : 2 ^ (-ε) * X ≤ 2 ^ ε * X := by
      gcongr
      exacts [by norm_num, by linarith]
    have := card_Ioo_floor_ceil_le (by positivity) hzy
    nlinarith [two_rpow_sub_two_rpow_neg_le hε.le hε1]
  rw [sum_sub_tsum_mul_smoothCutoff_eq hνs hνm hε hε1 hX0]
  calc _ ≤ T.card * (3 * B * Real.log X) := by simpa using norm_sum_le_of_le T hterm
    _ ≤ (2 * ε * X + 1) * (3 * B * Real.log X) := by
        gcongr
        exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))
    _ = 3 * B * (2 * ε * X + 1) * Real.log X := by ring

/-- **The smoothed Chebyshev function against `ψ`.** For a bump `ν`, `0 < ε ≤ 1` and `X ≥ 2`, the
sum `∑ₙ Λ(n) χ_ε(n / X)` differs from Chebyshev's `ψ(X) = ∑_{n ≤ X} Λ(n)` by at most
`3 (2εX + 1) log X`. -/
theorem norm_psi_sub_tsum_vonMangoldt_mul_smoothCutoff_le {ν : ℝ → ℝ} (hν0 : ∀ x, 0 ≤ ν x)
    (hνs : Function.support ν ⊆ Icc (1 / 2) 2) (hνm : ∫ x in Ioi 0, ν x / x = 1) {ε X : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hX : 2 ≤ X) :
    ‖(Chebyshev.psi X : ℂ) -
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * smoothCutoff ν ε (n / X)‖ ≤
      3 * (2 * ε * X + 1) * Real.log X := by
  have hf (n : ℕ) (_ : 1 ≤ n) :
      ‖(ArithmeticFunction.vonMangoldt n : ℂ)‖ ≤ 1 * Real.log (n + 1) := by
    rw [norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
      one_mul]
    exact ArithmeticFunction.vonMangoldt_le_log.trans
      (Real.log_le_log (by positivity) (by linarith))
  simpa [Chebyshev.psi] using norm_sum_sub_tsum_mul_smoothCutoff_le hf hν0 hνs hνm hε hε1 hX

end TauCeti
