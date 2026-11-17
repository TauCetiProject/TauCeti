/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.MellinInversion
public import TauCeti.Analysis.Contour.Residue.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.Contour.Residue.Rectangle
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Norm bounds, contour shifts, and the first-order cutoff for Mellin inversion

Mathlib's `mellinInv σ f y` is `(1 / 2π) ∫ y^{-(σ + i t)} • f(σ + i t) dt`. For `y > 0`, the factor
`t ↦ y^{-(σ + i t)}` is continuous of constant norm `y^{-σ}`. Hence the integrand is integrable
whenever `f` is integrable on the vertical line `Re s = σ`, and the norm of `mellinInv σ f y` is at
most `(y^{-σ} / 2π) ∫ ‖f(σ + i t)‖ dt`.

When `f : ℂ → ℂ` is meromorphic in a strip `σ₀ ≤ Re z ≤ σ₁` with finitely many poles `S` inside the
open strip `σ₀ < Re z < σ₁`, integrable on both boundary lines, and decays on horizontal segments at
heights `±T`, applying
`TauCeti.Contour.integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue`
to `z ↦ x^{-z} f(z)` shifts the Mellin inversion contour across `S`:

`mellinInv σ₁ f x = mellinInv σ₀ f x + ∑_{s ∈ S} Res_s (z ↦ x^{-z} f(z))`.

This file also evaluates the Mellin inverse of the first-order Perron kernel `1 / (s(s + 1))`. The
kernel is used for sums smoothed by `1 - n/x`. The migration motivating this computation
is the Prime Number Theorem and more project by Alex Kontorovich, Terence Tao and contributors,
`PrimeNumberTheoremAnd/PerronFormula.lean` (`Perron.formulaLtOne`, `Perron.formulaGtOne`). The proof
here composes Mathlib's interval-power Mellin transforms and Mellin inversion, independently of
that project's contour argument.

## Main results

* `Complex.VerticalIntegrable.integrable_cpow_smul`: the integrand of `mellinInv σ f y` is
  integrable for `y > 0` when `VerticalIntegrable f σ`.
* `TauCeti.mellinInv_zero`: `mellinInv σ f 0 = 0`.
* `TauCeti.norm_mellinInv_le`: `‖mellinInv σ f x‖ ≤ (x^{-σ} / 2π) ∫ ‖f(σ + i t)‖ dt` for `x ≥ 0`.
* `TauCeti.mellinInv_sub_mellinInv_eq_sum_residue`: shifting `mellinInv` from `σ₁` to `σ₀` for
  `x ≥ 0` when the horizontal segment integrals tend to `0`.
* `TauCeti.mellinInv_eq_mellinInv_add_sum_residue_of_norm_le`: shifting `mellinInv` for `x ≥ 0`
  under a uniform norm decay bound on horizontal segments.
* `TauCeti.verticalIntegrable_inv_mul_add_one`: `1 / (s(s+1))` is integrable on lines avoiding
  `Re s = 0, -1`, including negative lines.
* `TauCeti.mellinInv_inv_mul_add_one`: its inverse Mellin transform is `max (1 - x) 0` for
  positive `x`, on every line `Re s = c > 0`.
* `TauCeti.integrable_cpow_div_mul_add_one`: absolute convergence of `x^s / (s(s+1))` for
  `x ≥ 0` on every line avoiding the two poles.
* `TauCeti.integral_cpow_div_mul_add_one`: its integral is `2π * max (1 - 1/x) 0` for
  positive `x` and `c`. At the cutoff `x = 1` this value is zero.

## References

* E. C. Titchmarsh, *The Theory of Functions*, §9.5.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.9.
-/

public section

open Real Set MeasureTheory Filter
open scoped Interval Topology
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

end Complex

namespace TauCeti

/-- At `x = 0`, `mellinInv σ f 0 = 0` for every `σ` and `f`, since `0^{-(σ + i y)} = 0` for every
`y ≠ 0`. -/
@[simp]
theorem mellinInv_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : ℝ) (f : ℂ → E) : mellinInv σ f 0 = 0 := by
  have hae : (fun y : ℝ ↦ ((0 : ℝ) : ℂ) ^ (-(σ + y * I)) • f (σ + y * I)) =ᵐ[volume]
      fun _ ↦ (0 : E) := by
    filter_upwards [ae_iff.mpr (by simp : volume {y : ℝ | ¬ y ≠ 0} = 0)] with y hy
    have hne : -(σ + y * I) ≠ 0 := fun h ↦ hy (by simpa using congrArg im h)
    rw [ofReal_zero, zero_cpow hne, zero_smul]
  rw [mellinInv, integral_congr_ae hae, integral_zero, smul_zero]

/-- For `x ≥ 0`, the Mellin inverse on `Re s = σ` satisfies
`‖mellinInv σ f x‖ ≤ (x^{-σ} / 2π) ∫ ‖f(σ + i t)‖ dt`. No integrability assumption on `f` is needed,
as non-integrable integrands have Bochner integral `0`. -/
theorem norm_mellinInv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (σ : ℝ) (f : ℂ → E) {x : ℝ} (hx : 0 ≤ x) :
    ‖mellinInv σ f x‖ ≤ x ^ (-σ) / (2 * π) * ∫ t : ℝ, ‖f (σ + t * I)‖ := by
  rcases hx.eq_or_lt with rfl | hx
  · rw [mellinInv_zero, norm_zero]
    exact mul_nonneg (div_nonneg (Real.rpow_nonneg le_rfl _) (by positivity))
      (integral_nonneg fun _ ↦ norm_nonneg _)
  rw [mellinInv, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hnorm (t : ℝ) :
      ‖(x : ℂ) ^ (-(σ + t * I)) • f (σ + t * I)‖ = x ^ (-σ) * ‖f (σ + t * I)‖ := by
    rw [norm_smul, norm_cpow_eq_rpow_re_of_pos hx]
    simp
  calc (1 / (2 * π)) * ‖∫ y : ℝ, (x : ℂ) ^ (-(σ + y * I)) • f (σ + y * I)‖
      ≤ (1 / (2 * π)) * ∫ y : ℝ, ‖(x : ℂ) ^ (-(σ + y * I)) • f (σ + y * I)‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = x ^ (-σ) / (2 * π) * ∫ t : ℝ, ‖f (σ + t * I)‖ := by
        simp_rw [hnorm, integral_const_mul]
        ring

/-- **Shifting a Mellin inversion contour across poles.** Let `σ₀ ≤ σ₁` and `x ≥ 0`. Suppose `f` is
analytic on `σ₀ ≤ Re z ≤ σ₁` away from a finite set `S` contained in `σ₀ < Re z < σ₁`, meromorphic
at each point of `S`, and vertically integrable on `Re z = σ₀` and `Re z = σ₁`. If the horizontal
segment integrals of `z ↦ x^{-z} f(z)` at heights `±T` tend to `0` as `T → +∞`, then
`mellinInv σ₁ f x - mellinInv σ₀ f x` equals the sum of the residues of `z ↦ x^{-z} f(z)` over
`S`. -/
theorem mellinInv_sub_mellinInv_eq_sum_residue
    {f : ℂ → ℂ} {S : Finset ℂ} {σ₀ σ₁ x : ℝ} (hσ : σ₀ ≤ σ₁) (hx : 0 ≤ x)
    (hf : ∀ z : ℂ, z.re ∈ Icc σ₀ σ₁ → z ∉ S → AnalyticAt ℂ f z)
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hS : ∀ s ∈ S, s.re ∈ Ioo σ₀ σ₁)
    (hint₀ : VerticalIntegrable f σ₀) (hint₁ : VerticalIntegrable f σ₁)
    (hbot : Tendsto
      (fun T : ℝ ↦ ∫ u : ℝ in σ₀..σ₁, (x : ℂ) ^ (-((u : ℂ) - T * I)) * f (u - T * I))
      atTop (𝓝 0))
    (htop : Tendsto
      (fun T : ℝ ↦ ∫ u : ℝ in σ₀..σ₁, (x : ℂ) ^ (-((u : ℂ) + T * I)) * f (u + T * I))
      atTop (𝓝 0)) :
    mellinInv σ₁ f x - mellinInv σ₀ f x =
      ∑ s ∈ S, Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * f z) s := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have hx_slit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hcpow (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ (-w)) z :=
    analyticAt_const.cpow (by fun_prop) hx_slit
  have hshift := Contour.integral_add_mul_I_sub_integral_add_mul_I_eq_two_pi_mul_sum_residue
    (f := fun z ↦ (x : ℂ) ^ (-z) * f z) hσ
    (fun z hz hzS ↦ (hcpow z).mul (hf z hz hzS))
    (fun s hs ↦ (hcpow s).meromorphicAt.mul (hmero s hs)) hS
    (by simpa only [VerticalIntegrable, smul_eq_mul] using hint₀.integrable_cpow_smul hx)
    (by simpa only [VerticalIntegrable, smul_eq_mul] using hint₁.integrable_cpow_smul hx)
    hbot htop
  rw [mellinInv, mellinInv, ← smul_sub, real_smul]
  simp only [smul_eq_mul, hshift]
  push_cast
  field_simp [pi_ne_zero]

/-- **Shifting a Mellin inversion contour under uniform horizontal decay.** If `‖f(u ± i T)‖ ≤ B T`
on `u ∈ [σ₀, σ₁]` eventually as `T → +∞` with `B T → 0`, then for `x ≥ 0` the horizontal segment
integrals vanish and
`mellinInv σ₁ f x = mellinInv σ₀ f x + ∑ s ∈ S, residue (fun z ↦ x^{-z} f z) s`. -/
theorem mellinInv_eq_mellinInv_add_sum_residue_of_norm_le
    {f : ℂ → ℂ} {S : Finset ℂ} {σ₀ σ₁ x : ℝ} {B : ℝ → ℝ} (hσ : σ₀ ≤ σ₁) (hx : 0 ≤ x)
    (hf : ∀ z : ℂ, z.re ∈ Icc σ₀ σ₁ → z ∉ S → AnalyticAt ℂ f z)
    (hmero : ∀ s ∈ S, MeromorphicAt f s)
    (hS : ∀ s ∈ S, s.re ∈ Ioo σ₀ σ₁)
    (hint₀ : VerticalIntegrable f σ₀) (hint₁ : VerticalIntegrable f σ₁)
    (hB : Tendsto B atTop (𝓝 0))
    (hbound : ∀ᶠ (T : ℝ) in atTop, ∀ u ∈ Icc σ₀ σ₁,
      ‖f ((u : ℂ) + T * I)‖ ≤ B T ∧ ‖f ((u : ℂ) - T * I)‖ ≤ B T) :
    mellinInv σ₁ f x =
      mellinInv σ₀ f x + ∑ s ∈ S, Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * f z) s := by
  set M : ℝ := max (x ^ (-σ₀)) (x ^ (-σ₁))
  have hM0 : 0 ≤ M := le_max_of_le_left (Real.rpow_nonneg hx _)
  have hcpow {z : ℂ} (hre : z.re ∈ Icc σ₀ σ₁) (him : z.im ≠ 0) : ‖(x : ℂ) ^ (-z)‖ ≤ M := by
    rcases hx.eq_or_lt with rfl | hx
    · have hne : -z ≠ 0 := fun h ↦ him (by simpa using congrArg im h)
      simpa [zero_cpow hne] using hM0
    · rw [norm_cpow_eq_rpow_re_of_pos hx, neg_re]
      rcases le_or_gt 1 x with hx1 | hx1
      · exact (Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg hre.1)).trans (le_max_left _ _)
      · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1.le (neg_le_neg hre.2)).trans
          (le_max_right _ _)
  have hseg {s : ℝ → ℂ} (hre : ∀ T u : ℝ, ((u : ℂ) + s T).re = u)
      (him : ∀ᶠ T in atTop, ∀ u : ℝ, ((u : ℂ) + s T).im ≠ 0)
      (hg : ∀ᶠ T in atTop, ∀ u ∈ Icc σ₀ σ₁, ‖f ((u : ℂ) + s T)‖ ≤ B T) :
      Tendsto (fun T : ℝ ↦ ∫ u : ℝ in σ₀..σ₁,
        (x : ℂ) ^ (-((u : ℂ) + s T)) * f ((u : ℂ) + s T)) atTop (𝓝 0) :=
    intervalIntegral.tendsto_integral_nhds_zero_of_ae_norm_le (by simpa using hB.const_mul M) <|
      (him.and hg).mono fun T ⟨hTim, hTB⟩ ↦ Eventually.of_forall fun u hu ↦ by
        have hu' : u ∈ Icc σ₀ σ₁ := Ioc_subset_Icc_self (by rwa [uIoc_of_le hσ] at hu)
        rw [norm_mul]
        exact mul_le_mul (hcpow (by simpa [hre T u] using hu') (hTim u)) (hTB u hu')
          (norm_nonneg _) hM0
  rw [← sub_eq_iff_eq_add']
  refine mellinInv_sub_mellinInv_eq_sum_residue hσ hx hf hmero hS hint₀ hint₁ ?_ ?_
  · simpa only [sub_eq_add_neg] using hseg (s := fun T ↦ -(T * I)) (by simp)
      ((eventually_ne_atTop (0 : ℝ)).mono fun T hT u ↦ by simpa using hT)
      (hbound.mono fun T hT u hu ↦ (hT u hu).2)
  · exact hseg (s := fun T ↦ T * I) (by simp)
      ((eventually_ne_atTop (0 : ℝ)).mono fun T hT u ↦ by simpa using hT)
      (hbound.mono fun T hT u hu ↦ (hT u hu).1)

/-- The kernel `1 / (s(s+1))` is integrable on each vertical line avoiding its two poles. -/
theorem verticalIntegrable_inv_mul_add_one {c : ℝ} (hc : c ≠ 0) (hc1 : c ≠ -1) :
    VerticalIntegrable (fun s : ℂ ↦ (s * (s + 1))⁻¹) c := by
  let d := min |c| |c + 1|
  have h1 : c + 1 ≠ 0 := by simpa using sub_ne_zero.mpr hc1
  have hd : 0 < d := lt_min (abs_pos.mpr hc) (abs_pos.mpr h1)
  have hmajor : Integrable (fun t : ℝ ↦ (d ^ 2 + t ^ 2)⁻¹) := by
    simpa only [add_comm] using (integrable_inv_sq_add_sq hd.ne')
  refine hmajor.mono' (by fun_prop) (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [norm_inv, norm_mul]
  have hnorm (a : ℝ) (ha : d ≤ |a|) :
      Real.sqrt (d ^ 2 + t ^ 2) ≤ ‖(a : ℂ) + t * I‖ := by
    apply (Real.sqrt_le_left (norm_nonneg _)).mpr
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    nlinarith only [ha, hd.le, sq_abs a]
  have hshift : (c : ℂ) + t * I + 1 = ((c + 1 : ℝ) : ℂ) + t * I := by
    push_cast
    ring
  apply inv_anti₀ (by positivity)
  calc
    d ^ 2 + t ^ 2 = (Real.sqrt (d ^ 2 + t ^ 2)) ^ 2 :=
      (Real.sq_sqrt (by positivity)).symm
    _ ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖ := by
      rw [sq, hshift]
      exact mul_le_mul (hnorm c (min_le_left _ _)) (hnorm (c + 1) (min_le_right _ _))
        (Real.sqrt_nonneg _) (norm_nonneg _)

/-- The inverse Mellin transform of `1 / (s(s+1))` is the continuous first-order cutoff. -/
theorem mellinInv_inv_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    mellinInv c (fun s : ℂ ↦ (s * (s + 1))⁻¹) x = (max (1 - x) 0 : ℝ) := by
  have hm (t : ℝ) : mellin (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) ((c : ℂ) + t * I) =
      ((((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))⁻¹) :=
    (hasMellin_max_one_sub_zero (by simpa using hc)).2
  have hv : VerticalIntegrable (mellin (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ))) c := by
    simpa only [VerticalIntegrable, hm] using
      verticalIntegrable_inv_mul_add_one hc.ne' (by linarith)
  have h := mellinInv_mellin_eq c (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) hx
    (hasMellin_max_one_sub_zero (by simpa using hc)).1 hv (by fun_prop)
  rw [mellinInv] at h ⊢
  simpa only [hm] using h

private lemma riesz_integrand_eq {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ (-s) • (s * (s + 1))⁻¹ = (x : ℂ) ^ s / (s * (s + 1)) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx, Complex.cpow_neg, inv_inv,
    smul_eq_mul, ← div_eq_mul_inv]

/-- The first-order Perron kernel is absolutely integrable for `x ≥ 0` on every line away from
`Re s = 0, -1`. At `x = 0` the integrand vanishes. -/
theorem integrable_cpow_div_mul_add_one {c x : ℝ} (hc : c ≠ 0) (hc1 : c ≠ -1) (hx : 0 ≤ x) :
    Integrable (fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) := by
  rcases hx.eq_or_lt with rfl | hx
  · have hz (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
      intro h
      apply hc
      simpa using congrArg Complex.re h
    apply (integrable_zero ℝ ℂ volume).congr
    exact Filter.Eventually.of_forall fun t ↦ by
      simp only [Pi.zero_apply, Complex.ofReal_zero, Complex.zero_cpow (hz t), zero_div]
  · simpa only [riesz_integrand_eq hx.le] using
      (verticalIntegrable_inv_mul_add_one hc hc1).integrable_cpow_smul (inv_pos.mpr hx)

/-- The integral of `x^s / (s(s+1))` on a positive vertical line is the continuous cutoff
weight times `2π`. In particular, its value at `x = 1` is zero. -/
theorem integral_cpow_div_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) =
      ((2 * π : ℝ) : ℂ) * (max (1 - x⁻¹) 0 : ℝ) := by
  have h := mellinInv_inv_mul_add_one hc (inv_pos.mpr hx)
  simp only [mellinInv, riesz_integrand_eq hx.le] at h
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero pi_ne_zero
  apply (inv_mul_eq_iff_eq_mul₀ hπ).mp
  simpa only [Complex.real_smul, one_div, Complex.ofReal_inv] using h

end TauCeti
