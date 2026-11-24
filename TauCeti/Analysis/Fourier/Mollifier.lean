/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import TauCeti.Analysis.Fourier.FourierCharDeriv

/-!
# Fourier transforms of mollifiers

If an integrable function `f` is supported in the closed ball of radius `r` about `0`, then its
Fourier transform at `b` is within `2π ‖b‖ r ∫ ‖f‖` of its integral
(`Real.norm_fourier_sub_integral_le`). So the Fourier transforms of functions with bounded `L¹`
norms whose supports shrink to `0` converge at every frequency to the limit of their integrals
(`Real.tendsto_fourier_of_support_subset`). In particular, the Fourier transforms of mollifiers,
nonnegative functions of integral one, concentrating at `0` tend to one at every frequency: in the
Fourier picture, they approximate the point mass.
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
  -- `‖𝐞 ⟪-b, y⟫ • f y - 𝐞 ⟪-b, 0⟫ • f y‖ ≤ 2π ‖-b‖ ‖y - 0‖ ‖f y‖`.
  have h := norm_fourierChar_smul_sub_fourierChar_smul_le (-b) y 0 (f y)
  rw [inner_zero_right, AddChar.map_zero_eq_one, one_smul, inner_neg_left, real_inner_comm y b,
    norm_neg, sub_zero] at h
  exact h.trans (by gcongr)

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

end Real
