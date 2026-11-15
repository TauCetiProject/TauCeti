/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinInversion
public import TauCeti.Analysis.Contour.Residue.Basic
import TauCeti.Analysis.Contour.Residue.Rectangle
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Integrability and contour shifting of the Mellin inversion integral

Mathlib's `mellinInv σ f y` is `(1 / 2π) ∫ y^{-(σ + i t)} • f(σ + i t) dt`. This file records that
the integrand is integrable whenever `f` is integrable on the vertical line `Re s = σ` and
`y > 0`, since `t ↦ y^{-(σ + i t)}` is continuous of constant norm `y^{-σ}`.

When `f` is analytic across the closed vertical strip `σ₁ ≤ Re s ≤ σ₂` off a finite set `S` that
avoids the boundary lines `Re s = σ₁` and `Re s = σ₂`, meromorphic at the points of `S` in the open
strip `σ₁ < Re s < σ₂`, integrable on both vertical lines, and its horizontal segment integrals at
height `±T` tend to `0` as `T → ∞`, applying `TauCeti.Contour.integral_boundary_rect_eq_sum_residue`
on `[σ₁, σ₂] × [-T, T]` and letting `T → ∞` shifts the line of integration:

`mellinInv σ₂ f x = mellinInv σ₁ f x + ∑_{s ∈ S, σ₁ < Re s < σ₂} Res_s (z ↦ x^{-z} f(z))`.

Because `‖x^{-(u + i t)}‖ = x^{-u}` is bounded on `[[σ₁, σ₂]]`, any uniform bound on `‖f‖` along
horizontal segments that tends to `0` discharges the horizontal-edge hypotheses.

## Main results

* `Complex.VerticalIntegrable.integrable_cpow_smul`: the integrand of the Mellin inversion
  integral of a vertically integrable function is integrable.
* `Complex.tendsto_integral_cpow_mul_zero_of_norm_le`: uniform decay of `f` on horizontal segments
  makes the horizontal Mellin segment integrals tend to `0`.
* `Complex.mellinInv_eq_mellinInv_add_sum_residue`: shifting the vertical line of `mellinInv`
  across finitely many poles in a vertical strip.
-/

public section

open Real Set MeasureTheory Filter
open scoped Topology Interval
open Complex hiding exp continuous_exp

namespace Complex

/-- If `f` is integrable on the vertical line `Re s = σ`, then so is the integrand
`t ↦ y^{-(σ + i t)} • f(σ + i t)` of the Mellin inversion integral `mellinInv σ f y`, for
`y > 0`. -/
theorem VerticalIntegrable.integrable_cpow_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {σ : ℝ} (hf : VerticalIntegrable f σ) {y : ℝ} (hy : 0 < y) :
    Integrable fun t : ℝ ↦ (y : ℂ) ^ (-(σ + t * I)) • f (σ + t * I) := by
  -- `t ↦ y^{-(σ + i t)}` is continuous of constant norm `y^{-σ}`
  refine hf.bdd_smul (y ^ (-σ)) ?_ (Eventually.of_forall fun t ↦ ?_)
  · exact (Continuous.const_cpow (by fun_prop)
      (Or.inl (ofReal_ne_zero.mpr hy.ne'))).aestronglyMeasurable
  · rw [norm_cpow_eq_rpow_re_of_pos hy]
    simp

/-- On a compact real interval `[[σ₁, σ₂]]`, `‖x ^ (-z)‖ = x ^ (-Re z)` is bounded by
`max (x ^ (-σ₁)) (x ^ (-σ₂))` for `x > 0`, so uniform decay of `f` along horizontal segments makes
the horizontal Mellin segment integrals tend to `0`. -/
theorem tendsto_integral_cpow_mul_zero_of_norm_le {f : ℂ → ℂ} {b y : ℝ → ℝ}
    {σ₁ σ₂ x : ℝ} (hx : 0 < x) (hb : Tendsto b atTop (𝓝 0))
    (hf : ∀ᶠ T in atTop, ∀ u ∈ [[σ₁, σ₂]], ‖f (u + y T * I)‖ ≤ b T) :
    Tendsto (fun T : ℝ ↦ ∫ u : ℝ in σ₁..σ₂, (x : ℂ) ^ (-((u : ℂ) + y T * I)) * f (u + y T * I))
      atTop (𝓝 0) := by
  set M : ℝ := max (x ^ (-σ₁)) (x ^ (-σ₂))
  have hM0 : 0 ≤ M := le_max_of_le_left (Real.rpow_nonneg hx.le _)
  have hxM {u : ℝ} (hu : u ∈ [[σ₁, σ₂]]) : x ^ (-u) ≤ M := by
    rcases mem_uIcc.mp hu with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases le_total x 1 with hx1 | hx1
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1 (by linarith)).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)).trans (le_max_right _ _)
  have hlim : Tendsto (fun T : ℝ ↦ M * b T * |σ₂ - σ₁|) atTop (𝓝 0) := by
    simpa using (hb.const_mul M).mul_const |σ₂ - σ₁|
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [hf] with T hT
  refine intervalIntegral.norm_integral_le_of_norm_le_const fun u hu ↦ ?_
  have hu' : u ∈ [[σ₁, σ₂]] := uIoc_subset_uIcc hu
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  have hre : (-((u : ℂ) + y T * I)).re = -u := by simp
  rw [hre]
  exact mul_le_mul (hxM hu') (hT u hu') (norm_nonneg _) hM0

open scoped Classical in
/-- Once `T` exceeds the imaginary parts of all points of `S`, the boundary of
`[σ₁, σ₂] × [-T, T]` avoids `S` and captures precisely the points of `S` with `σ₁ < Re s < σ₂`. -/
private theorem eventually_rectangle_poles {S : Finset ℂ} {σ₁ σ₂ : ℝ} (hσ : σ₁ ≤ σ₂)
    (hS : ∀ s ∈ S, s.re ≠ σ₁ ∧ s.re ≠ σ₂) :
    ∀ᶠ T : ℝ in atTop, 0 < T ∧
      (∀ s ∈ S, s ∉ frontier (Rectangle ((σ₁ : ℂ) - T * I) ((σ₂ : ℂ) + T * I))) ∧
      (S.filter (· ∈ Rectangle ((σ₁ : ℂ) - T * I) ((σ₂ : ℂ) + T * I)) =
        S.filter (fun s ↦ s.re ∈ Ioo σ₁ σ₂)) := by
  set B : ℝ := ∑ s ∈ S, |s.im|
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  filter_upwards [eventually_gt_atTop B] with T hTB
  have hT0 : 0 < T := hB0.trans_lt hTB
  have him {s : ℂ} (hs : s ∈ S) : |s.im| < T :=
    (Finset.single_le_sum (fun _ _ ↦ abs_nonneg _) hs).trans_lt hTB
  refine ⟨hT0, fun s hs hfr ↦ ?_, Finset.filter_congr fun s hs ↦ ?_⟩
  · rw [frontier_rectangle] at hfr
    have him' := abs_lt.mp (him hs)
    rcases hfr with ⟨-, h1⟩ | ⟨h1, -⟩
    · have h1' : s.im = -T ∨ s.im = T := by simpa using h1
      rcases h1' with h1' | h1' <;> linarith
    · have h1' : s.re = σ₁ ∨ s.re = σ₂ := by simpa using h1
      exact h1'.elim (hS s hs).1 (hS s hs).2
  · have hre_le : ((σ₁ : ℂ) - T * I).re ≤ ((σ₂ : ℂ) + T * I).re := by simp [hσ]
    have him_le : ((σ₁ : ℂ) - T * I).im ≤ ((σ₂ : ℂ) + T * I).im := by simp; linarith
    rw [mem_rectangle_iff hre_le him_le]
    have hzre : ((σ₁ : ℂ) - T * I).re = σ₁ := by simp
    have hwre : ((σ₂ : ℂ) + T * I).re = σ₂ := by simp
    have hzim : ((σ₁ : ℂ) - T * I).im = -T := by simp
    have hwim : ((σ₂ : ℂ) + T * I).im = T := by simp
    rw [hzre, hwre, hzim, hwim]
    have him' := abs_lt.mp (him hs)
    exact ⟨fun ⟨⟨h1, h2⟩, _⟩ ↦ ⟨lt_of_le_of_ne h1 (hS s hs).1.symm,
      lt_of_le_of_ne h2 (hS s hs).2⟩,
      fun ⟨h1, h2⟩ ↦ ⟨⟨h1.le, h2.le⟩, him'.1.le, him'.2.le⟩⟩

open scoped Classical in
/-- **Contour shifting for the Mellin inversion integral.** Let `σ₁ ≤ σ₂` and `x > 0`. Suppose `f`
is analytic at every point of the closed strip `σ₁ ≤ Re z ≤ σ₂` outside `S`, meromorphic at every
point of `S` in the open strip `σ₁ < Re s < σ₂`, no point of `S` lies on `Re s = σ₁` or
`Re s = σ₂`, `f` is vertically integrable at `σ₁` and `σ₂`, and the horizontal Mellin segment
integrals at height `±T` tend to `0` as `T → ∞`. Then

`mellinInv σ₂ f x = mellinInv σ₁ f x + ∑_{s ∈ S, σ₁ < Re s < σ₂} Res_s (z ↦ x^{-z} f(z))`. -/
theorem mellinInv_eq_mellinInv_add_sum_residue {f : ℂ → ℂ} {S : Finset ℂ}
    {σ₁ σ₂ x : ℝ} (hσ : σ₁ ≤ σ₂) (hx : 0 < x)
    (hf : ∀ z : ℂ, z.re ∈ Icc σ₁ σ₂ → z ∉ S → AnalyticAt ℂ f z)
    (hmero : ∀ s ∈ S, s.re ∈ Ioo σ₁ σ₂ → MeromorphicAt f s)
    (hS : ∀ s ∈ S, s.re ≠ σ₁ ∧ s.re ≠ σ₂)
    (hint₁ : VerticalIntegrable f σ₁) (hint₂ : VerticalIntegrable f σ₂)
    (htop : Tendsto (fun T : ℝ ↦ ∫ u : ℝ in σ₁..σ₂, (x : ℂ) ^ (-((u : ℂ) + T * I)) * f (u + T * I))
      atTop (𝓝 0))
    (hbot : Tendsto (fun T : ℝ ↦ ∫ u : ℝ in σ₁..σ₂, (x : ℂ) ^ (-((u : ℂ) - T * I)) * f (u - T * I))
      atTop (𝓝 0)) :
    mellinInv σ₂ f x = mellinInv σ₁ f x +
      ∑ s ∈ S with s.re ∈ Ioo σ₁ σ₂, TauCeti.Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * f z) s := by
  set g : ℂ → ℂ := fun z ↦ (x : ℂ) ^ (-z) * f z
  have hx_an (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ (-w)) z :=
    (Differentiable.analyticAt (fun _ ↦
      differentiableAt_id.neg.const_cpow (Or.inl (ofReal_ne_zero.mpr hx.ne'))) z)
  have hev : ∀ᶠ T : ℝ in atTop,
      ((2 * Real.pi : ℂ)⁻¹ * ∫ y : ℝ in (-T)..T, g (σ₂ + y * I)) -
        ((2 * Real.pi : ℂ)⁻¹ * ∫ y : ℝ in (-T)..T, g (σ₁ + y * I)) +
        ((∫ u : ℝ in σ₁..σ₂, g (u - T * I)) -
          ∫ u : ℝ in σ₁..σ₂, g (u + T * I)) / (2 * Real.pi * I) =
      ∑ s ∈ S with s.re ∈ Ioo σ₁ σ₂, TauCeti.Contour.residue g s := by
    filter_upwards [eventually_rectangle_poles hσ hS] with T ⟨_, hfr, hfilt⟩
    set z : ℂ := (σ₁ : ℂ) - T * I
    set w : ℂ := (σ₂ : ℂ) + T * I
    have hzre : z.re = σ₁ := by simp [z]
    have hwre : w.re = σ₂ := by simp [w]
    have hzim : z.im = -T := by simp [z]
    have hwim : w.im = T := by simp [w]
    have hg_an : ∀ p ∈ Rectangle z w, p ∉ S → AnalyticAt ℂ g p := fun p hp hpS ↦ by
      rw [mem_rectangle_iff (by linarith) (by linarith), hzre, hwre] at hp
      exact (hx_an p).mul (hf p hp.1 hpS)
    have hg_mero : ∀ s ∈ S, s ∈ Rectangle z w → MeromorphicAt g s := fun s hsS hsR ↦ by
      have hs' := Finset.mem_filter.mp (hfilt ▸ Finset.mem_filter.mpr ⟨hsS, hsR⟩)
      exact (hx_an s).meromorphicAt.mul (hmero s hsS hs'.2)
    have hrect := TauCeti.Contour.integral_boundary_rect_eq_sum_residue
      (by linarith) (by linarith) hg_an hg_mero hfr
    rw [hzre, hwre, hzim, hwim, hfilt] at hrect
    simp only [ofReal_neg, neg_mul, ← sub_eq_add_neg] at hrect
    have hpi : (2 * (Real.pi : ℂ) * I) ≠ 0 := by simp [Real.pi_ne_zero]
    apply mul_right_injective₀ hpi
    calc _ = (∫ u : ℝ in σ₁..σ₂, g (u - T * I)) - (∫ u : ℝ in σ₁..σ₂, g (u + T * I)) +
          I * (∫ y : ℝ in (-T)..T, g (σ₂ + y * I)) -
          I * (∫ y : ℝ in (-T)..T, g (σ₁ + y * I)) := by
            field_simp [Real.pi_ne_zero]; ring
      _ = _ := hrect
  have hv₂ := (intervalIntegral_tendsto_integral (hint₂.integrable_cpow_smul hx)
    tendsto_neg_atTop_atBot tendsto_id).const_mul (2 * Real.pi : ℂ)⁻¹
  have hv₁ := (intervalIntegral_tendsto_integral (hint₁.integrable_cpow_smul hx)
    tendsto_neg_atTop_atBot tendsto_id).const_mul (2 * Real.pi : ℂ)⁻¹
  have hlim := (hv₂.sub hv₁).add ((hbot.sub htop).div_const (2 * Real.pi * I))
  have heq := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  simp only [sub_zero, zero_div, add_zero] at heq
  have hm (σ : ℝ) : mellinInv σ f x = (2 * Real.pi : ℂ)⁻¹ * ∫ y : ℝ, g (σ + y * I) := by
    simp [mellinInv, g, real_smul]
  rw [hm σ₂, hm σ₁]
  linear_combination heq

end Complex
