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

/-!
# Integrability, norm bounds, and contour shifts of Mellin inversion integrals

Mathlib's `mellinInv σ f y` is `(1 / 2π) ∫ y^{-(σ + i t)} • f(σ + i t) dt`. For `y > 0`, the factor
`t ↦ y^{-(σ + i t)}` is continuous of constant norm `y^{-σ}`. Hence the integrand is integrable
whenever `f` is integrable on the vertical line `Re s = σ`, and the norm of `mellinInv σ f y` is at
most `(y^{-σ} / 2π) ∫ ‖f(σ + i t)‖ dt`.

When `f : ℂ → ℂ` is meromorphic in a strip `σ₀ ≤ Re z ≤ σ₁` with finitely many poles `S` inside the
open strip `σ₀ < Re z < σ₁`, integrable on both boundary lines, and decays on horizontal segments at
heights `±T`, applying
`TauCeti.Contour.verticalIntegral_sub_verticalIntegral_eq_two_pi_mul_sum_residue`
to `z ↦ x^{-z} f(z)` shifts the Mellin inversion contour across `S`:

`mellinInv σ₁ f x = mellinInv σ₀ f x + ∑_{s ∈ S} Res_s (z ↦ x^{-z} f(z))`.

## Main results

* `Complex.VerticalIntegrable.integrable_cpow_smul`: the integrand of `mellinInv σ f y` is
  integrable for `y > 0` when `VerticalIntegrable f σ`.
* `Complex.mellinInv_zero`: `mellinInv σ f 0 = 0`.
* `Complex.norm_mellinInv_le`: `‖mellinInv σ f x‖ ≤ (x^{-σ} / 2π) ∫ ‖f(σ + i t)‖ dt` for `x ≥ 0`.
* `Complex.mellinInv_sub_mellinInv_eq_sum_residue`: shifting `mellinInv` from `σ₁` to `σ₀` for
  `x ≥ 0` when the horizontal segment integrals tend to `0`.
* `Complex.mellinInv_eq_mellinInv_add_sum_residue_of_norm_le`: shifting `mellinInv` for `x ≥ 0`
  under a uniform norm decay bound on horizontal segments.

## References

* E. C. Titchmarsh, *The Theory of Functions*, §9.5.
* H. Iwaniec, E. Kowalski, *Analytic Number Theory*, §5.9.
-/

public section

open Real Set MeasureTheory Filter
open scoped Topology
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

private lemma residue_zero_cpow_mul (f : ℂ → ℂ) (s : ℂ) :
    TauCeti.Contour.residue (fun z ↦ (0 : ℂ) ^ (-z) * f z) s = 0 := by
  have hz0 : ∀ᶠ z in 𝓝[≠] s, z ≠ 0 := by
    rcases eq_or_ne s 0 with rfl | hs
    · exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds hs)
  have heq : (fun z ↦ (0 : ℂ) ^ (-z) * f z) =ᶠ[𝓝[≠] s] fun _ ↦ (0 : ℂ) := by
    filter_upwards [hz0] with z hz
    rw [zero_cpow (neg_ne_zero.mpr hz), zero_mul]
  exact (TauCeti.Contour.residue_congr_nhdsNE heq).trans
    (TauCeti.Contour.residue_eq_zero_of_analyticAt analyticAt_const)

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
      ∑ s ∈ S, TauCeti.Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * f z) s := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [residue_zero_cpow_mul]
  have hx_slit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hcpow (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ (-w)) z :=
    analyticAt_const.cpow (by fun_prop) hx_slit
  have hshift := TauCeti.Contour.verticalIntegral_sub_verticalIntegral_eq_two_pi_mul_sum_residue
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
      mellinInv σ₀ f x + ∑ s ∈ S, TauCeti.Contour.residue (fun z ↦ (x : ℂ) ^ (-z) * f z) s := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [residue_zero_cpow_mul]
  have hx_slit : (x : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.mpr hx
  have hcpow (z : ℂ) : AnalyticAt ℂ (fun w : ℂ ↦ (x : ℂ) ^ (-w)) z :=
    analyticAt_const.cpow (by fun_prop) hx_slit
  set M : ℝ := max (x ^ (-σ₀)) (x ^ (-σ₁))
  have hrpow {u : ℝ} (hu : u ∈ Icc σ₀ σ₁) : x ^ (-u) ≤ M := by
    rcases le_or_gt 1 x with hx1 | hx1
    · exact (Real.rpow_le_rpow_of_exponent_le hx1 (neg_le_neg hu.1)).trans (le_max_left _ _)
    · exact (Real.rpow_le_rpow_of_exponent_ge hx hx1.le (neg_le_neg hu.2)).trans (le_max_right _ _)
  have hshift := TauCeti.Contour.verticalIntegral_sub_verticalIntegral_eq_of_norm_le
    (f := fun z ↦ (x : ℂ) ^ (-z) * f z) (B := fun T ↦ M * B T) hσ
    (fun z hz hzS ↦ (hcpow z).mul (hf z hz hzS))
    (fun s hs ↦ (hcpow s).meromorphicAt.mul (hmero s hs)) hS
    (by simpa only [VerticalIntegrable, smul_eq_mul] using hint₀.integrable_cpow_smul hx)
    (by simpa only [VerticalIntegrable, smul_eq_mul] using hint₁.integrable_cpow_smul hx)
    (by simpa using hB.const_mul M)
    (hbound.mono fun T hT u hu ↦ by
      refine ⟨?_, ?_⟩
      · rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, show (-((u : ℂ) + T * I)).re = -u by simp]
        exact mul_le_mul (hrpow hu) (hT u hu).1 (norm_nonneg _) (by positivity)
      · rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx, show (-((u : ℂ) - T * I)).re = -u by simp]
        exact mul_le_mul (hrpow hu) (hT u hu).2 (norm_nonneg _) (by positivity))
  rw [← sub_eq_iff_eq_add', mellinInv, mellinInv, ← smul_sub, real_smul]
  simp only [smul_eq_mul, hshift]
  push_cast
  field_simp [pi_ne_zero]

end Complex
