/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.NumberTheory.LSeries.Basic
public import TauCeti.Analysis.MellinInversion
public import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical

/-!
# Exponentially smoothed coefficient sums as Mellin inverses

A Dirichlet series `∑ aᵢ pᵢ⁻ˢ` that converges absolutely on the line `Re s = σ > 0` determines the
exponentially smoothed sum of its coefficients by a vertical integral against the Gamma function:

`∑ᵢ aᵢ e^{-pᵢ x} = (1 / 2π) ∫ Γ(σ + i t) x^{-(σ + i t)} ∑ᵢ aᵢ pᵢ^{-(σ + i t)} dt` for `x > 0`.

In the notation of Mathlib's Mellin transform the right side is
`mellinInv σ (fun s ↦ Γ(s) ∑ᵢ aᵢ pᵢ⁻ˢ) x`. This is the inverse of Mathlib's `hasSum_mellin`, which
computes the Mellin transform of `x ↦ ∑ᵢ aᵢ e^{-pᵢ x}` as `Γ(s) ∑ᵢ aᵢ pᵢ⁻ˢ`. The proof applies
the Mellin inversion formula for `Γ` (`Complex.mellinInv_Gamma`) term by term. The interchange of
the sum and the integral is justified by the absolute convergence of the series on the line and
the integrability of `Γ` there (`Complex.verticalIntegrable_Gamma`).

For an `LSeries` with `f 0 = 0` the formula reads
`∑ₙ f(n) e^{-n x} = mellinInv σ (fun s ↦ Γ(s) L(f, s)) x`. Shifting the line of integration to the
left of a pole of `L(f, s)` and estimating the shifted integral is the smoothing argument behind
Goldfeld's proof of Siegel's lower bound for `L(1, χ)`.

## Main results

* `TauCeti.hasSum_mellinInv_Gamma_mul`: the smoothed sum of a general Dirichlet series.
* `TauCeti.LSeries.hasSum_mellinInv_Gamma_mul_LSeries`: the same formula for `LSeries`.

## References

* D. Goldfeld, *A simple proof of Siegel's theorem*, Proc. Nat. Acad. Sci. USA 71 (1974), 1055.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.9 (Siegel's theorem by smoothing with
  `Γ(s) xˢ`).
-/

public section

open Real Set MeasureTheory Filter
open Complex hiding exp continuous_exp

namespace TauCeti

/-- **Smoothed sums of a Dirichlet series.** If `∑ aᵢ pᵢ⁻ˢ` converges absolutely on the line
`Re s = σ > 0`, then for `x > 0` the exponentially smoothed sum `∑ᵢ aᵢ e^{-pᵢ x}` is the Mellin
inverse on that line of `Γ(s) ∑ᵢ aᵢ pᵢ⁻ˢ`. This is the inverse of `hasSum_mellin`. -/
theorem hasSum_mellinInv_Gamma_mul {ι : Type*} [Countable ι] {a : ι → ℂ} {p : ι → ℝ} {σ : ℝ}
    (hp : ∀ i, a i = 0 ∨ 0 < p i) (hσ : 0 < σ) (h_sum : Summable fun i ↦ ‖a i‖ / p i ^ σ)
    {x : ℝ} (hx : 0 < x) :
    HasSum (fun i ↦ a i * rexp (-p i * x))
      (mellinInv σ (fun s ↦ Gamma s * ∑' i, a i / (p i : ℂ) ^ s) x) := by
  -- the `i`-th term of the integrand, written as a multiple of the integrand of `mellinInv σ Γ`
  set g : ι → ℝ → ℂ := fun i t ↦ a i * (((p i * x : ℝ) : ℂ) ^ (-(σ + t * I)) * Gamma (σ + t * I))
  have hg (i : ι) (t : ℝ) : (x : ℂ) ^ (-(σ + t * I)) * (Gamma (σ + t * I) *
      (a i / (p i : ℂ) ^ (σ + t * I))) = g i t := by
    rcases hp i with h | h
    · simp [g, h]
    simp only [g]
    rw [ofReal_mul, mul_cpow_ofReal_nonneg h.le hx.le, cpow_neg (p i : ℂ)]
    field_simp
  have hΓ := verticalIntegrable_Gamma (σ := σ) fun n h ↦ by
    linarith [show (0 : ℝ) ≤ n from n.cast_nonneg]
  have hint (i : ι) : Integrable (g i) := by
    rcases hp i with h | h
    · simp [g, h]
    simpa only [smul_eq_mul] using ((hΓ.integrable_cpow_smul (mul_pos h hx)).const_mul (a i))
  -- the integrals of the norms are `x^{-σ} ‖aᵢ‖ / pᵢ^σ` times the integral of `‖Γ‖` on the line
  have hnorm (i : ι) : ∫ t, ‖g i t‖ = x ^ (-σ) * (‖a i‖ / p i ^ σ) *
      ∫ t : ℝ, ‖Gamma (σ + t * I)‖ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    rcases hp i with h | h
    · simp [g, h]
    simp only [g, norm_mul, norm_cpow_eq_rpow_re_of_pos (mul_pos h hx)]
    rw [show (-(↑σ + ↑t * I)).re = -σ by simp, Real.mul_rpow h.le hx.le, Real.rpow_neg h.le]
    field_simp
  have key := hasSum_integral_of_summable_integral_norm hint
    (by simpa only [hnorm] using (h_sum.mul_left _).mul_right _)
  -- the integral of each term is `2π aᵢ e^{-pᵢ x}`
  have hterm (i : ι) : ∫ t, g i t = 2 * π * (a i * rexp (-p i * x)) := by
    rcases hp i with h | h
    · simp [g, h]
    simp only [g, integral_const_mul, integral_cpow_neg_mul_Gamma hσ (mul_pos h hx), neg_mul]
    push_cast
    ring
  -- the Mellin inverse is `1 / 2π` times the integral of the sum
  have hfull : mellinInv σ (fun s ↦ Gamma s * ∑' i, a i / (p i : ℂ) ^ s) x =
      (1 / (2 * π)) • ∫ t, ∑' i, g i t := by
    rw [mellinInv]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    simp only [smul_eq_mul, ← hg, ← tsum_mul_left]
  rw [hfull]
  convert key.const_smul (1 / (2 * π)) using 1
  ext i
  rw [hterm, real_smul]
  push_cast
  field_simp [pi_ne_zero]

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

end TauCeti
