/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Fourier transforms of mollifiers

If an integrable function `f` is supported in the closed ball of radius `r` about `0`, then its
Fourier transform at `b` is within `2π ‖b‖ r ∫ ‖f‖` of its integral
(`Real.norm_fourier_sub_integral_le`). So the Fourier transforms of functions with bounded `L¹`
norms whose supports shrink to `0` converge at every frequency to the limit of their integrals
(`Real.tendsto_fourier_of_support_subset`).

A mollifier is a nonnegative function `ρ` of integral one; its Fourier transform is bounded by
one (`Real.norm_fourier_ofReal_le_one`). If `ρ` is supported in the closed ball of radius `r`
about `0`, then `𝓕 ρ (b)` is within `2π ‖b‖ r` of one (`Real.norm_fourier_ofReal_sub_one_le`), so
the Fourier transforms of mollifiers concentrating at `0` tend to one at every frequency
(`Real.tendsto_fourier_ofReal_one`): in the Fourier picture, they approximate the point mass.
-/

public section

noncomputable section

open Complex Filter Function Metric Set MeasureTheory
open scoped Topology FourierTransform RealInnerProductSpace Real

namespace Real

variable {D F : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- The Fourier transform at `b` of a function supported in the closed ball of radius `r` about
`0` is within `2π ‖b‖ r ∫ ‖f‖` of its integral. -/
theorem norm_fourier_sub_integral_le {f : D → F} {r : ℝ} (hf : support f ⊆ closedBall 0 r)
    (b : D) : ‖𝓕 f b - ∫ y, f y‖ ≤ 2 * π * ‖b‖ * r * ∫ y, ‖f y‖ := by
  rcases lt_or_ge r 0 with hr | hr
  · have h0 : f = 0 := by
      ext y
      by_contra hy
      exact (closedBall_eq_empty.2 hr).subset (hf hy)
    simp [h0, Real.fourier_eq]
  by_cases hint : Integrable f
  swap
  · rw [Real.fourier_eq, integral_undef ((Real.fourierIntegral_convergent_iff b).not.2 hint),
      integral_undef hint, sub_zero, norm_zero]
    exact mul_nonneg (by positivity) (integral_nonneg fun _ ↦ norm_nonneg _)
  rw [Real.fourier_eq, ← integral_sub ((Real.fourierIntegral_convergent_iff b).2 hint) hint,
    ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.norm.const_mul _) (Eventually.of_forall fun y ↦ ?_)
  by_cases hy : f y = 0
  · simp [hy]
  have hyr : ‖y‖ ≤ r := by simpa using hf hy
  rw [Circle.smul_def, show ((𝐞 (-⟪y, b⟫) : Circle) : ℂ) • f y - f y =
      (((𝐞 (-⟪y, b⟫) : Circle) : ℂ) - 1) • f y by rw [sub_smul, one_smul], norm_smul]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (f y))
  -- `𝐞 (-⟪y, b⟫) = exp (i (-2π ⟪y, b⟫))`, at distance at most `2π |⟪y, b⟫|` from one.
  have hexp : ((𝐞 (-⟪y, b⟫) : Circle) : ℂ) = Complex.exp (I * ((-(2 * π * ⟪y, b⟫) : ℝ) : ℂ)) := by
    rw [Real.fourierChar_apply]
    push_cast
    ring_nf
  rw [hexp]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  calc 2 * π * |⟪y, b⟫| ≤ 2 * π * (‖y‖ * ‖b‖) := by
        gcongr
        exact abs_real_inner_le_norm y b
    _ ≤ 2 * π * (r * ‖b‖) := by gcongr
    _ = 2 * π * ‖b‖ * r := by ring

/-- If the supports of `f i` shrink to `0`, their `L¹` norms stay bounded and their integrals
tend to `v`, then their Fourier transforms tend to `v` at every frequency. -/
theorem tendsto_fourier_of_support_subset {ι : Type*} {l : Filter ι} {f : ι → D → F}
    {r : ι → ℝ} {M : ℝ} {v : F} (hfr : ∀ᶠ i in l, support (f i) ⊆ closedBall 0 (r i))
    (hr : Tendsto r l (𝓝 0)) (hM : ∀ᶠ i in l, ∫ y, ‖f i y‖ ≤ M)
    (hv : Tendsto (fun i ↦ ∫ y, f i y) l (𝓝 v)) (b : D) :
    Tendsto (fun i ↦ 𝓕 (f i) b) l (𝓝 v) := by
  have hlim : Tendsto (fun i ↦ 2 * π * ‖b‖ * |r i| * M) l (𝓝 0) := by
    simpa using (hr.abs.const_mul (2 * π * ‖b‖)).mul_const M
  have hsub : Tendsto (fun i ↦ 𝓕 (f i) b - ∫ y, f i y) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
    filter_upwards [hfr, hM] with i hi hMi
    refine (norm_fourier_sub_integral_le hi b).trans ?_
    calc 2 * π * ‖b‖ * r i * ∫ y, ‖f i y‖ ≤ 2 * π * ‖b‖ * |r i| * ∫ y, ‖f i y‖ := by
          gcongr
          exact le_abs_self _
      _ ≤ 2 * π * ‖b‖ * |r i| * M := by gcongr
  simpa using hsub.add hv

/-- The Fourier transform of a nonnegative function of integral one is bounded by one. -/
theorem norm_fourier_ofReal_le_one {ρ : D → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y, ρ y = 1) (b : D) : ‖𝓕 (fun y ↦ (ρ y : ℂ)) b‖ ≤ 1 := by
  refine (Real.norm_fourier_le_integral_norm _ b).trans_eq ?_
  simp_rw [Complex.norm_real, Real.norm_of_nonneg (hρ0 _), hρ1]

/-- The Fourier transform of a nonnegative function of integral one supported in the closed ball
of radius `r` about `0` is within `2π ‖b‖ r` of one at `b`. -/
theorem norm_fourier_ofReal_sub_one_le {ρ : D → ℝ} (hρ0 : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y, ρ y = 1) {r : ℝ} (hρr : support ρ ⊆ closedBall 0 r) (b : D) :
    ‖𝓕 (fun y ↦ (ρ y : ℂ)) b - 1‖ ≤ 2 * π * ‖b‖ * r := by
  have h := norm_fourier_sub_integral_le (f := fun y ↦ (ρ y : ℂ))
    (fun y hy ↦ hρr (by simpa using hy)) b
  simpa only [integral_complex_ofReal, hρ1, ofReal_one, Complex.norm_real,
    Real.norm_of_nonneg (hρ0 _), mul_one] using h

/-- The Fourier transforms of nonnegative functions of integral one whose supports shrink to `0`
tend to one at every frequency. -/
theorem tendsto_fourier_ofReal_one {ι : Type*} {l : Filter ι} {ρ : ι → D → ℝ}
    {r : ι → ℝ} (hρ0 : ∀ᶠ i in l, ∀ y, 0 ≤ ρ i y) (hρ1 : ∀ᶠ i in l, ∫ y, ρ i y = 1)
    (hρr : ∀ᶠ i in l, support (ρ i) ⊆ closedBall 0 (r i)) (hr : Tendsto r l (𝓝 0)) (b : D) :
    Tendsto (fun i ↦ 𝓕 (fun y ↦ (ρ i y : ℂ)) b) l (𝓝 1) := by
  refine tendsto_fourier_of_support_subset (M := 1)
    (hρr.mono fun i hi y hy ↦ hi (by simpa using hy)) hr ?_ ?_ b
  · filter_upwards [hρ0, hρ1] with i h0 h1
    simp_rw [Complex.norm_real, Real.norm_of_nonneg (h0 _), h1, le_rfl]
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [hρ1] with i h1
    rw [integral_complex_ofReal, h1, ofReal_one]

end Real
