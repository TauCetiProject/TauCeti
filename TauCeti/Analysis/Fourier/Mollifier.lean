/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fourier transforms of mollifiers and of tensor products

A mollifier is a nonnegative function `ρ` of integral one; its Fourier transform is bounded by
one (`Real.norm_fourier_ofReal_le_one`). If `ρ` is supported in the closed ball of radius `r`
about `0`, then `𝓕 ρ (b)` is within `2π ‖b‖ r` of one (`Real.norm_fourier_ofReal_sub_one_le`), so
the Fourier transforms of mollifiers concentrating at `0` tend to one at every frequency
(`Real.tendsto_fourier_ofReal_one`): in the Fourier picture, they approximate the point mass.

On the Euclidean product `WithLp 2 (E × D)` the Fourier transform of a tensor product
`(x, y) ↦ f x * g y` is the product of the Fourier transforms of `f` and `g`
(`Real.fourier_prod_mul`), by Fubini's theorem. Together, these describe the Fourier transform of
`ψ ⊗ ρ` as `ρ` concentrates at `0`, which is how a distribution on `E × D` is restricted to
`E × {0}`.
-/

public section

noncomputable section

open Complex Filter Function Metric Set MeasureTheory WithLp
open scoped Topology FourierTransform RealInnerProductSpace Real

namespace Real

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D]

/-- The Fourier transform of `(x, y) ↦ f x * g y` on the Euclidean product `WithLp 2 (E × D)` is
the product of the Fourier transforms of `f` and `g`. -/
theorem fourier_prod_mul (f : E → ℂ) (g : D → ℂ) (ζ : WithLp 2 (E × D)) :
    𝓕 (fun p : WithLp 2 (E × D) ↦ f p.fst * g p.snd) ζ = 𝓕 f ζ.fst * 𝓕 g ζ.snd := by
  simp only [Real.fourier_eq]
  rw [← (WithLp.volume_preserving_symm_measurableEquiv_toLp_prod E D).symm.integral_comp',
    ← integral_prod_mul, ← Measure.volume_eq_prod]
  congr 1
  ext q
  simp only [MeasurableEquiv.symm_symm, MeasurableEquiv.coe_toLp, toLp_fst, toLp_snd,
    prod_inner_apply, neg_add, AddChar.map_add_eq_mul, Circle.smul_def, Circle.coe_mul,
    smul_eq_mul, ofLp_fst, ofLp_snd]
  ring

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
  have hint : Integrable ρ := Integrable.of_integral_ne_zero (by rw [hρ1]; exact one_ne_zero)
  have hintc : Integrable fun y ↦ (ρ y : ℂ) := hint.ofReal
  have h1 : (1 : ℂ) = ∫ y, (ρ y : ℂ) := by rw [integral_complex_ofReal, hρ1, ofReal_one]
  have hdiff : 𝓕 (fun y ↦ (ρ y : ℂ)) b - 1 =
      ∫ y, (𝐞 (-⟪y, b⟫) • (ρ y : ℂ) - (ρ y : ℂ)) := by
    rw [integral_sub ((Real.fourierIntegral_convergent_iff b).2 hintc) hintc, ← h1,
      Real.fourier_eq]
  rw [hdiff]
  refine (norm_integral_le_of_norm_le (hint.const_mul (2 * π * ‖b‖ * r))
    (Eventually.of_forall fun y ↦ ?_)).trans_eq (by rw [integral_const_mul, hρ1, mul_one])
  by_cases hy : ρ y = 0
  · simp [hy]
  have hyr : ‖y‖ ≤ r := by simpa using hρr hy
  -- `𝐞 (-⟪y, b⟫) = exp (i (-2π ⟪y, b⟫))`, at distance at most `2π |⟪y, b⟫|` from one.
  have hfac : 𝐞 (-⟪y, b⟫) • (ρ y : ℂ) - (ρ y : ℂ) =
      (Complex.exp (I * ((-(2 * π * ⟪y, b⟫) : ℝ) : ℂ)) - 1) * (ρ y : ℂ) := by
    rw [Circle.smul_def, Real.fourierChar_apply]
    push_cast
    ring_nf
  rw [hfac, norm_mul, Complex.norm_real, Real.norm_of_nonneg (hρ0 y), mul_comm _ (ρ y),
    mul_comm _ (ρ y)]
  refine mul_le_mul_of_nonneg_left (Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_) (hρ0 y)
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  calc 2 * π * |⟪y, b⟫| ≤ 2 * π * (‖y‖ * ‖b‖) := by
        gcongr
        exact abs_real_inner_le_norm y b
    _ ≤ 2 * π * (r * ‖b‖) := by gcongr
    _ = 2 * π * ‖b‖ * r := by ring

/-- The Fourier transforms of nonnegative functions of integral one whose supports shrink to `0`
tend to one at every frequency. -/
theorem tendsto_fourier_ofReal_one {ι : Type*} {l : Filter ι} {ρ : ι → D → ℝ}
    {r : ι → ℝ} (hρ0 : ∀ᶠ i in l, ∀ y, 0 ≤ ρ i y) (hρ1 : ∀ᶠ i in l, ∫ y, ρ i y = 1)
    (hρr : ∀ᶠ i in l, support (ρ i) ⊆ closedBall 0 (r i)) (hr : Tendsto r l (𝓝 0)) (b : D) :
    Tendsto (fun i ↦ 𝓕 (fun y ↦ (ρ i y : ℂ)) b) l (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hlim : Tendsto (fun i ↦ 2 * π * ‖b‖ * r i) l (𝓝 0) := by
    simpa using hr.const_mul (2 * π * ‖b‖)
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _) ?_ hlim
  filter_upwards [hρ0, hρ1, hρr] with i h0 h1 hr using norm_fourier_ofReal_sub_one_le h0 h1 hr b

end Real
