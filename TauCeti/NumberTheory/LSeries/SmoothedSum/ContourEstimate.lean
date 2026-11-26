/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LSeries.SmoothedSum.Contour
import Mathlib.Analysis.Complex.ExponentialBounds
import TauCeti.Analysis.MellinTransform.EdgeBounds
import TauCeti.NumberTheory.LSeries.LogBoundedCoeff

/-!
# The smoothed coefficient sum near a simple pole

Let `χ_ε = smoothCutoff ν ε` be the smoothed cutoff of a `C¹` bump `ν` and let the L-series of `a`
agree on the line `Re s = σ₀ > 1` with `G(s) + r/(s - 1)`, where `G` is holomorphic on the
rectangle `[1 - η, σ₀] ×ℂ [-T, T]` (`0 < η < 1`, `η ≤ T`) and bounded there by `M`. If
`‖mellin χ_ε s‖ ≤ C / (|s| (1 + ε|s|))` on the strip `1 - η ≤ Re s ≤ σ₀`, as
`TauCeti.exists_norm_mellin_smoothCutoff_le` provides uniformly in `0 < ε ≤ 1`, and the L-series is
bounded by `L` on the tails `|t| > T` of the line `Re s = σ₀`, then for `x ≥ 1`

`‖∑ₙ a(n) χ_ε(n / x) - r · 𝓜χ_ε(1) · x‖ ≤ (2π)⁻¹ (2 L C x^{σ₀} / (εT)
  + 4 K x^{1-η} log(1 + T / (1 - η)) + 2 (σ₀ - 1 + η) K x^{σ₀} / (εT²))`, `K = C (M + ‖r‖ / η)`.

The three terms bound the vertical tails, the left edge and the two horizontal edges of the
contour of `TauCeti.LSeries.tsum_mul_smoothCutoff_eq_residue_add_contour`; on the edges
`|s - 1| ≥ η`, so `‖r / (s - 1)‖ ≤ ‖r‖ / η`. When `‖a(n)‖ ≤ B log(n + 1)`, the choice
`σ₀ = 1 + 1 / log x` gives `L = 8 B log² x` and `x^{σ₀} ≤ e x`. With `η` the width of a zero-free
region at height `T`, the left edge saves the factor `x^{-η}` against the main term.

## Main results

* `TauCeti.LSeries.norm_tsum_mul_smoothCutoff_sub_residue_le`: the estimate in terms of a bound
  `L` on the L-series on the tails of the line.
* `TauCeti.LSeries.norm_tsum_mul_smoothCutoff_sub_residue_le_of_norm_le_mul_log`: the estimate
  for coefficients `‖a(n)‖ ≤ B log(n + 1)` at `σ₀ = 1 + 1 / log x`.

## References

* A. Kontorovich, T. Tao et al., *PrimeNumberTheoremAnd* blueprint, §4.6 (the bounds of the
  integrals `I₁`–`I₉` and the medium-strength prime number theorem),
  <https://github.com/AlexKontorovich/PrimeNumberTheoremAnd>. The formalization in the Tau Ceti
  fork <https://github.com/TauCetiProject/PrimeNumberTheoremAnd>, file
  `PrimeNumberTheoremAnd/MediumPNT.lean` at revision `df0ccba` (`I1Bound` to `I9Bound` and
  `GenStrengthPNT`), carries out this estimate for `-ζ'/ζ`, with the nine pieces of the contour
  bounded separately.
-/

public section

open Set Complex MeasureTheory
open scoped Real Interval

namespace TauCeti.LSeries

variable {ν : ℝ → ℝ} {ε : ℝ}

/-- If `‖g‖ ≤ A` and `‖m‖ ≤ C / D`, then `‖g · m · xˢ‖ ≤ A C x^{Re s} / D` for `x ≥ 0`. -/
private lemma norm_mul_mul_cpow_le {g m s : ℂ} {A C D x : ℝ} (hx : 0 ≤ x) (hg : ‖g‖ ≤ A)
    (hm : ‖m‖ ≤ C / D) : ‖g * m * (x : ℂ) ^ s‖ ≤ A * C * x ^ s.re / D := by
  have hA : 0 ≤ A := (norm_nonneg g).trans hg
  have hCD : 0 ≤ C / D := (norm_nonneg m).trans hm
  have hp : ‖(x : ℂ) ^ s‖ ≤ x ^ s.re := by
    simpa [arg_ofReal_of_nonneg hx, abs_of_nonneg hx] using norm_cpow_le (x : ℂ) s
  rw [norm_mul, norm_mul]
  calc ‖g‖ * ‖m‖ * ‖(x : ℂ) ^ s‖ ≤ A * (C / D) * x ^ s.re := by gcongr
    _ = A * C * x ^ s.re / D := by ring

/-- If `‖g‖ ≤ M`, `‖m‖ ≤ C / D` and `|s - 1| ≥ η > 0`, then
`‖(g + r/(s - 1)) · m · xˢ‖ ≤ (M + ‖r‖/η) C x^{Re s} / D` for `x ≥ 0`. -/
private lemma norm_add_div_mul_mul_cpow_le {g m r s : ℂ} {x η C D M : ℝ} (hx : 0 ≤ x)
    (hη : 0 < η) (hg : ‖g‖ ≤ M) (hm : ‖m‖ ≤ C / D) (hs1 : η ≤ ‖s - 1‖) :
    ‖(g + r / (s - 1)) * m * (x : ℂ) ^ s‖ ≤ (M + ‖r‖ / η) * C * x ^ s.re / D := by
  refine norm_mul_mul_cpow_le hx ((norm_add_le _ _).trans (add_le_add hg ?_)) hm
  rw [norm_div]
  exact div_le_div_of_nonneg_left (norm_nonneg r) hη hs1

/-- A horizontal edge `Im s = τ`, `|τ| = T`, of the rectangle contributes at most
`(σ₀ - 1 + η) (M + ‖r‖/η) C x^{σ₀} / (εT²)`. -/
private lemma norm_horizontal_le {G : ℂ → ℂ} {r : ℂ} {x σ₀ η T τ C M : ℝ} (hε : 0 < ε)
    (hx : 1 ≤ x) (hη : 0 < η) (hσ : 1 - η ≤ σ₀) (hηT : η ≤ T) (hτ : |τ| = T)
    (hGb : ∀ s ∈ Icc (1 - η) σ₀ ×ℂ Icc (-T) T, ‖G s‖ ≤ M)
    (hC : ∀ s : ℂ, 1 - η ≤ s.re → s.re ≤ σ₀ →
      ‖mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖))) :
    ‖∫ σ in (1 - η)..σ₀, (G (σ + τ * I) + r / (σ + τ * I - 1)) *
        mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) (σ + τ * I) * (x : ℂ) ^ ((σ : ℂ) + τ * I)‖ ≤
      (σ₀ - (1 - η)) * ((M + ‖r‖ / η) * C) * x ^ σ₀ / (ε * T ^ 2) := by
  rw [← hτ, sq_abs]
  refine norm_intervalIntegral_horizontal_le
    (f := fun s ↦ (G s + r / (s - 1)) * mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) s * (x : ℂ) ^ s)
    hσ (fun h ↦ by rw [h, abs_zero] at hτ; linarith) hε hx fun σ hσ' ↦ ?_
  have hs1 : η ≤ ‖(σ : ℂ) + τ * I - 1‖ := calc
    η ≤ |τ| := hηT.trans_eq hτ.symm
    _ = |((σ : ℂ) + τ * I - 1).im| := by simp
    _ ≤ _ := abs_im_le_norm _
  have hs : (σ : ℂ) + τ * I ∈ Icc (1 - η) σ₀ ×ℂ Icc (-T) T :=
    mem_reProdIm.mpr ⟨by simpa using hσ', by simpa [abs_le] using hτ.le⟩
  simpa using norm_add_div_mul_mul_cpow_le (r := r) (by linarith) hη (hGb _ hs)
    (hC _ hs.1.1 hs.1.2) hs1

/-- The left edge `Re s = 1 - η`, `|Im s| ≤ T`, of the rectangle contributes at most
`4 (M + ‖r‖/η) C x^{1-η} log(1 + T / (1 - η))`. -/
private lemma norm_left_le {G : ℂ → ℂ} {r : ℂ} {x σ₀ η T C M : ℝ} (hε : 0 ≤ ε) (hx : 0 ≤ x)
    (hη : 0 < η) (hη1 : η < 1) (hσ : 1 - η ≤ σ₀) (hT : 0 ≤ T)
    (hGb : ∀ s ∈ Icc (1 - η) σ₀ ×ℂ Icc (-T) T, ‖G s‖ ≤ M)
    (hC : ∀ s : ℂ, 1 - η ≤ s.re → s.re ≤ σ₀ →
      ‖mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖))) :
    ‖∫ t in (-T)..T, (G ((1 - η : ℝ) + t * I) + r / ((1 - η : ℝ) + t * I - 1)) *
        mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) ((1 - η : ℝ) + t * I) *
        (x : ℂ) ^ (((1 - η : ℝ) : ℂ) + t * I)‖ ≤
      4 * ((M + ‖r‖ / η) * C * x ^ (1 - η)) * Real.log (1 + T / (1 - η)) := by
  refine norm_intervalIntegral_vertical_le
    (f := fun s ↦ (G s + r / (s - 1)) * mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) s * (x : ℂ) ^ s)
    (sub_pos.mpr hη1) hT fun t ht ↦ ?_
  have hs1 : η ≤ ‖((1 - η : ℝ) : ℂ) + t * I - 1‖ := by
    simpa [abs_of_pos hη] using abs_re_le_norm (((1 - η : ℝ) : ℂ) + t * I - 1)
  have hn : 0 < ‖((1 - η : ℝ) : ℂ) + t * I‖ := (sub_pos.mpr hη1).trans_le
    (by simpa using re_le_norm (((1 - η : ℝ) : ℂ) + t * I))
  have hs : ((1 - η : ℝ) : ℂ) + t * I ∈ Icc (1 - η) σ₀ ×ℂ Icc (-T) T :=
    mem_reProdIm.mpr ⟨by simpa using (⟨le_rfl, hσ⟩ : 1 - η ∈ Icc (1 - η) σ₀), by simpa using ht⟩
  have h := norm_add_div_mul_mul_cpow_le (r := r) hx hη (hGb _ hs) (hC _ hs.1.1 hs.1.2) hs1
  rw [show (((1 - η : ℝ) : ℂ) + t * I).re = 1 - η by simp] at h
  -- the decay factor `1 + ε|s| ≥ 1` is dropped; the bound is nonnegative, being at least `‖f s‖`
  have hD : 0 < ‖((1 - η : ℝ) : ℂ) + t * I‖ * (1 + ε * ‖((1 - η : ℝ) : ℂ) + t * I‖) := by
    positivity
  have hK : 0 ≤ (M + ‖r‖ / η) * C * x ^ (1 - η) := by
    simpa using (le_div_iff₀ hD).1 ((norm_nonneg _).trans h)
  exact h.trans (div_le_div_of_nonneg_left hK hn
    (le_mul_of_one_le_right hn.le (le_add_of_nonneg_right (by positivity))))

/-- **The smoothed sum near a simple pole.** Let `ν` be of class `C¹` on `(0, ∞)` and vanish there
off `[1/2, 2]`, `ε > 0`, `x ≥ 1`, `σ₀ > 1`, `0 < η < 1` and `η ≤ T`. Let `G` be continuous on
`[1 - η, σ₀] ×ℂ [-T, T]`, complex differentiable on its interior and bounded by `M` on it, and
let the L-series of `a` be summable at `σ₀`, equal to `G(s) + r/(s - 1)` on the line
`Re s = σ₀`, and bounded by `L` there for `|Im s| > T`. If
`‖mellin χ_ε s‖ ≤ C / (|s| (1 + ε|s|))` for `1 - η ≤ Re s ≤ σ₀`, then
`‖∑ₙ a(n) χ_ε(n / x) - r · 𝓜χ_ε(1) · x‖` is at most `(2π)⁻¹` times
`2 L C x^{σ₀} / (εT) + 4 K x^{1-η} log(1 + T / (1 - η)) + 2 (σ₀ - 1 + η) K x^{σ₀} / (εT²)`,
where `K = (M + ‖r‖/η) C`. -/
theorem norm_tsum_mul_smoothCutoff_sub_residue_le {a : ℕ → ℂ} {G : ℂ → ℂ} {r : ℂ}
    {x σ₀ η T C L M : ℝ} (hν : ContDiffOn ℝ 1 ν (Ioi 0))
    (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2) (hε : 0 < ε) (hx : 1 ≤ x)
    (hσ₀ : 1 < σ₀) (hη : 0 < η) (hη1 : η < 1) (hηT : η ≤ T) (hs : LSeriesSummable a σ₀)
    (hGc : ContinuousOn G (Icc (1 - η) σ₀ ×ℂ Icc (-T) T))
    (hGd : DifferentiableOn ℂ G (Ioo (1 - η) σ₀ ×ℂ Ioo (-T) T))
    (hGb : ∀ s ∈ Icc (1 - η) σ₀ ×ℂ Icc (-T) T, ‖G s‖ ≤ M)
    (hL : ∀ t : ℝ, LSeries a (σ₀ + t * I) = G (σ₀ + t * I) + r / (σ₀ + t * I - 1))
    (hLb : ∀ t : ℝ, T < |t| → ‖LSeries a (σ₀ + t * I)‖ ≤ L)
    (hC : ∀ s : ℂ, 1 - η ≤ s.re → s.re ≤ σ₀ →
      ‖mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖))) :
    ‖∑' n, a n * smoothCutoff ν ε (n / x) - r * mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) 1 * x‖ ≤
      (1 / (2 * π)) * (2 * (L * C * x ^ σ₀) / (ε * T) +
        4 * ((M + ‖r‖ / η) * C * x ^ (1 - η)) * Real.log (1 + T / (1 - η)) +
        2 * ((σ₀ - (1 - η)) * ((M + ‖r‖ / η) * C) * x ^ σ₀ / (ε * T ^ 2))) := by
  have hx0 : 0 ≤ x := by linarith
  have hT : 0 < T := hη.trans_le hηT
  set f : ℂ → ℂ := fun s ↦
    (G s + r / (s - 1)) * mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) s * (x : ℂ) ^ s with hf
  -- the vertical tails, where the integrand is `L(a, s) · mellin χ_ε s · xˢ`
  have htail := norm_integral_vertical_tail_le (f := f) (σ := σ₀) (K := L * C * x ^ σ₀) hε hT
    fun t ht ↦ by
      have h := norm_mul_mul_cpow_le (s := σ₀ + t * I) hx0 (hLb t ht)
        (hC (σ₀ + t * I) (by simpa using (by linarith : 1 - η ≤ σ₀)) (by simp))
      simpa [hf, ← hL] using h
  have hleft := norm_left_le (r := r) hε.le hx0 hη hη1 (by linarith) hT.le hGb hC
  have htop := norm_horizontal_le (r := r) (τ := T) hε hx hη (by linarith) hηT (abs_of_pos hT)
    hGb hC
  have hbot := norm_horizontal_le (r := r) (τ := -T) hε hx hη (by linarith) hηT
    (by rw [abs_neg, abs_of_pos hT]) hGb hC
  have hneg (σ : ℝ) : (σ : ℂ) - T * I = σ + ((-T : ℝ) : ℂ) * I := by push_cast; ring
  rw [tsum_mul_smoothCutoff_eq_residue_add_contour hν hνs hε hx0 (by linarith) (by linarith)
    hσ₀ hT hs hGc hGd hL (fun _ ↦ rfl), add_sub_cancel_left, norm_mul]
  simp only [hneg]
  calc _ ≤ ‖1 / (2 * (π : ℂ))‖ * (‖∫ t in {t : ℝ | T < |t|}, f (σ₀ + t * I)‖ +
          ‖∫ t in (-T)..T, f ((1 - η : ℝ) + t * I)‖ +
          (‖∫ σ in (1 - η)..σ₀, f (σ + T * I)‖ + ‖∫ σ in (1 - η)..σ₀, f (σ + (-T : ℝ) * I)‖)) := by
        gcongr
        refine (norm_add₃_le).trans (add_le_add le_rfl ?_)
        rw [norm_div, norm_I, div_one]
        exact norm_sub_le _ _
    _ ≤ _ := by
        rw [show ‖1 / (2 * (π : ℂ))‖ = 1 / (2 * π) by simp [abs_of_pos Real.pi_pos],
          two_mul (_ / _)]
        gcongr

/-- **The smoothed sum near a simple pole, for logarithmically bounded coefficients.** Let
`‖a(n)‖ ≤ B log(n + 1)` for `n ≥ 1`, let `ν` be of class `C¹` on `(0, ∞)` and vanish there off
`[1/2, 2]`, `ε > 0`, `x ≥ 2`, `0 < η < 1` and `η ≤ T`, and put `σ₀ = 1 + 1 / log x`. Let `G` be
continuous on `[1 - η, σ₀] ×ℂ [-T, T]`, complex differentiable on its interior and bounded by `M`
on it, with `L(a, s) = G(s) + r/(s - 1)` on the line `Re s = σ₀`. If
`‖mellin χ_ε s‖ ≤ C / (|s| (1 + ε|s|))` for `1 - η ≤ Re s ≤ σ₀`, then
`‖∑ₙ a(n) χ_ε(n / x) - r · 𝓜χ_ε(1) · x‖` is at most `(2π)⁻¹` times
`16 e B C x log² x / (εT) + 4 K x^{1-η} log(1 + T / (1 - η)) + 2 e (1 / log x + η) K x / (εT²)`,
where `K = (M + ‖r‖/η) C`. -/
theorem norm_tsum_mul_smoothCutoff_sub_residue_le_of_norm_le_mul_log {a : ℕ → ℂ} {B : ℝ}
    (ha : ∀ n : ℕ, 1 ≤ n → ‖a n‖ ≤ B * Real.log (n + 1)) {G : ℂ → ℂ} {r : ℂ} {x η T C M : ℝ}
    (hν : ContDiffOn ℝ 1 ν (Ioi 0)) (hνs : Function.support ν ∩ Ioi 0 ⊆ Icc (1 / 2) 2)
    (hε : 0 < ε) (hx : 2 ≤ x) (hη : 0 < η) (hη1 : η < 1) (hηT : η ≤ T)
    (hGc : ContinuousOn G (Icc (1 - η) (1 + (Real.log x)⁻¹) ×ℂ Icc (-T) T))
    (hGd : DifferentiableOn ℂ G (Ioo (1 - η) (1 + (Real.log x)⁻¹) ×ℂ Ioo (-T) T))
    (hGb : ∀ s ∈ Icc (1 - η) (1 + (Real.log x)⁻¹) ×ℂ Icc (-T) T, ‖G s‖ ≤ M)
    (hL : ∀ s : ℂ, s.re = 1 + (Real.log x)⁻¹ → LSeries a s = G s + r / (s - 1))
    (hC : ∀ s : ℂ, 1 - η ≤ s.re → s.re ≤ 1 + (Real.log x)⁻¹ →
      ‖mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) s‖ ≤ C / (‖s‖ * (1 + ε * ‖s‖))) :
    ‖∑' n, a n * smoothCutoff ν ε (n / x) - r * mellin (fun y ↦ (smoothCutoff ν ε y : ℂ)) 1 * x‖ ≤
      (1 / (2 * π)) * (2 * (8 * B * Real.log x ^ 2 * C * (Real.exp 1 * x)) / (ε * T) +
        4 * ((M + ‖r‖ / η) * C * x ^ (1 - η)) * Real.log (1 + T / (1 - η)) +
        2 * (((Real.log x)⁻¹ + η) * ((M + ‖r‖ / η) * C) * (Real.exp 1 * x) / (ε * T ^ 2))) := by
  have hx0 : 0 < x := by linarith
  have hlog : 2⁻¹ ≤ Real.log x := ((by norm_num : (2 : ℝ)⁻¹ < 0.6931471803).trans
    Real.log_two_gt_d9).le.trans (Real.log_le_log two_pos hx)
  have hlog0 : 0 < (Real.log x)⁻¹ := inv_pos.mpr (by linarith)
  have hlog2 : (Real.log x)⁻¹ ≤ 2 := inv_le_of_inv_le₀ two_pos hlog
  have hre (t : ℝ) : (((1 + (Real.log x)⁻¹ : ℝ) : ℂ) + t * I).re = 1 + (Real.log x)⁻¹ := by simp
  have hLb (t : ℝ) (_ : T < |t|) : ‖LSeries a ((1 + (Real.log x)⁻¹ : ℝ) + t * I)‖ ≤
      8 * B / ((Real.log x)⁻¹) ^ 2 := by
    have h := norm_LSeries_le_of_norm_le_mul_log ha
      (s := ((1 + (Real.log x)⁻¹ : ℝ) : ℂ) + t * I) (by rw [hre]; linarith)
      (by rw [hre]; linarith)
    rwa [hre, add_sub_cancel_left] at h
  have h := norm_tsum_mul_smoothCutoff_sub_residue_le (x := x) (σ₀ := 1 + (Real.log x)⁻¹) hν hνs
    hε (by linarith) (by linarith) hη hη1 hηT
    (LSeriesSummable_of_norm_le_mul_log ha (by rw [ofReal_re]; linarith)) hGc hGd hGb
    (fun t ↦ hL _ (hre t)) hLb hC
  have hT : 0 < T := hη.trans_le hηT
  have hB := nonneg_of_norm_le_mul_log ha
  have hC0 : 0 ≤ C := by
    have h := hC 1 (by rw [one_re]; linarith) (by rw [one_re]; linarith)
    rw [norm_one, one_mul, mul_one] at h
    simpa using (le_div_iff₀ (by positivity)).1 ((norm_nonneg _).trans h)
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hGb 1 (mem_reProdIm.mpr
    ⟨by rw [one_re]; constructor <;> linarith, by rw [one_im]; constructor <;> linarith⟩))
  have hxσ : x ^ (1 + (Real.log x)⁻¹) ≤ Real.exp 1 * x := by
    rw [Real.rpow_add hx0, Real.rpow_one, mul_comm]
    exact mul_le_mul_of_nonneg_right Real.rpow_inv_log_le_exp_one hx0.le
  refine h.trans ?_
  rw [inv_pow, div_inv_eq_mul, add_sub_sub_cancel]
  gcongr

end TauCeti.LSeries
