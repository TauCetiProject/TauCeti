/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.ContDiff.Convolution
public import TauCeti.Analysis.PDE.HeatKernel.Bounds

/-!
# The heat convolution solves the heat equation

Let `g` be a measurable, essentially bounded function on a finite-dimensional real inner product
space `E`, with values in a real normed space (a Banach space, for the two derivative formulas).
The candidate solution of the Cauchy problem `∂ₜu = Δu`, `u(0, ·) = g`, is
`u(t, x) = (K_t ⋆ g)(x)`, where `K_t` is the heat kernel. The initial condition holds pointwise
at every point `x₀` where `g` is continuous (for `F` a Banach space): `u(t, x) → g(x₀)` as
`(t, x) → (0⁺, x₀)`, which is `TauCeti.tendsto_heatKernel_convolution`. At points where `g` is
discontinuous no such limit is asserted. This file proves the equation:

* `u(t, ·)` is smooth for every `t > 0`, however rough `g` is;
* `Δu(t, ·) = ΔK_t ⋆ g`, and `∂ₜu(t, x) = (ΔK_t ⋆ g)(x)`, so `∂ₜu = Δu` for `t > 0`.

Both derivatives are taken under the integral sign. In space, every derivative of `K_t` is
dominated, uniformly on unit translates, by a multiple of `K_{4t}`
(`TauCeti.exists_integrable_norm_iteratedFDeriv_heatKernel_add_le`), and this feeds the general
smoothness theorem `TauCeti.contDiff_convolution_left_of_dominated`. In time, `∂ₜK_s = ΔK_s` is
dominated for `s` near `t` by a multiple of `K_{4t}`.

## Main declarations

* `TauCeti.contDiff_heatKernel_convolution`: `K_t ⋆ g` is smooth for `t > 0`.
* `TauCeti.laplacian_heatKernel_convolution`: `Δ (K_t ⋆ g) = ΔK_t ⋆ g`.
* `TauCeti.hasDerivAt_heatKernel_convolution`: **the heat equation**
  `∂ₜ (K_t ⋆ g)(x) = Δ (K_t ⋆ g)(x)` for `t > 0`.

## References

* L. C. Evans, *Partial Differential Equations*, Section 2.3.1, Theorem 1.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap InnerProductSpace Laplacian MeasureTheory Metric Module Real Set
open scoped Convolution ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {g : E → F} {M t : ℝ}

/-- **Smoothing by the heat kernel.** For `t > 0` and `g` measurable and essentially bounded,
`K_t ⋆ g` is smooth. -/
theorem contDiff_heatKernel_convolution (ht : 0 < t) (hg : AEStronglyMeasurable g)
    (hM : ∀ᵐ y, ‖g y‖ ≤ M) : ContDiff ℝ ∞ (heatKernel t ⋆ g) :=
  contDiff_convolution_left_of_dominated (lsmul ℝ ℝ) (contDiff_heatKernel t)
    (fun k _ => exists_integrable_norm_iteratedFDeriv_heatKernel_add_le ht k) hg hM

/-- **The Laplacian of a heat convolution.** For `t > 0` and `g` measurable and essentially
bounded, `Δ (K_t ⋆ g) = ΔK_t ⋆ g`. -/
theorem laplacian_heatKernel_convolution [CompleteSpace F] (ht : 0 < t)
    (hg : AEStronglyMeasurable g) (hM : ∀ᵐ y, ‖g y‖ ≤ M) (x : E) :
    Δ (heatKernel t ⋆ g) x = (Δ (heatKernel t : E → ℝ) ⋆ g) x := by
  obtain ⟨C, hC⟩ := exists_norm_iteratedFDeriv_heatKernel_le (E := E) ht 2
  have hD₂ : Integrable (iteratedFDeriv ℝ 2 (heatKernel t : E → ℝ)) :=
    ((integrable_heatKernel (by positivity)).const_mul C).mono'
      ((contDiff_heatKernel t (k := ∞)).continuous_iteratedFDeriv (m := 2)
        (by simp)).aestronglyMeasurable
      (ae_of_all _ hC)
  -- The Laplacian is the continuous linear functional `Λ A = ∑ i, A (bᵢ, bᵢ)` of the Hessian.
  set Λ : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => E) F →L[ℝ] F :=
    ∑ i, ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 => E) F
      ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i]
  have hΛ : ∀ A, Λ A = ∑ i, A ![stdOrthonormalBasis ℝ E i, stdOrthonormalBasis ℝ E i] :=
    fun A => by simp [Λ]
  rw [laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  dsimp only
  rw [iteratedFDeriv_convolution_left_of_dominated
    (lsmul ℝ ℝ) (N := ⊤) (contDiff_heatKernel t)
    (fun k _ => exists_integrable_norm_iteratedFDeriv_heatKernel_add_le ht k) hg hM le_top,
    ← hΛ, convolution_def, ← integral_comp_comm Λ
      (convolutionExists_of_integrable_of_ae_norm_le _ hD₂ hg hM x), convolution_def]
  congr 1 with y
  rw [hΛ, laplacian_eq_iteratedFDeriv_stdOrthonormalBasis, lsmul_apply, Finset.sum_smul]
  simp

omit [MeasurableSpace E] [BorelSpace E] in
/-- For `s` within a factor two of `t`, the time derivative `∂ₛK_s = ΔK_s` of the heat kernel is
dominated by a fixed multiple of `K_{4t}`. -/
private theorem exists_abs_laplacian_heatKernel_le (ht : 0 < t) :
    ∃ B, 0 ≤ B ∧ ∀ s, t / 2 < s → s ≤ 2 * t → ∀ y : E,
      |Δ (heatKernel s : E → ℝ) y| ≤ B * heatKernel (2 * (2 * t)) y := by
  have h2t : 0 < 2 * t := by positivity
  obtain ⟨C, hC⟩ := exists_one_add_norm_pow_mul_heatKernel_le (E := E) h2t 2
  have hC₀ : 0 ≤ C := (mul_nonneg_iff_of_pos_right (heatKernel_pos (E := E) (by positivity) 0)).1
    ((mul_nonneg (by positivity) (heatKernel_pos h2t 0).le).trans (hC 0))
  set d : ℝ := (finrank ℝ E : ℝ)
  refine ⟨(1 / t ^ 2 + d / t) * 4 ^ (d / 2) * C, by positivity, fun s hs hs' y => ?_⟩
  have hs₀ : 0 < s := by linarith
  have hKs := heatKernel_pos hs₀ y
  -- `ΔK_s = (‖y‖² / (4s²) - n / (2s)) K_s`, and the coefficient is `O((1 + ‖y‖)²)` uniformly.
  have hcoef : |‖y‖ ^ 2 / (4 * s ^ 2) - d / (2 * s)| ≤ (1 / t ^ 2 + d / t) * (1 + ‖y‖) ^ 2 := by
    have h₁ : ‖y‖ ^ 2 / (4 * s ^ 2) ≤ ‖y‖ ^ 2 / t ^ 2 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) (by nlinarith)
    have h₂ : d / (2 * s) ≤ d / t := div_le_div_of_nonneg_left (by positivity) ht (by linarith)
    have h₃ : ‖y‖ ^ 2 ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
    have h₄ : 1 ≤ (1 + ‖y‖) ^ 2 := by nlinarith [norm_nonneg y]
    refine (abs_sub _ _).trans ?_
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    calc ‖y‖ ^ 2 / (4 * s ^ 2) + d / (2 * s) ≤ ‖y‖ ^ 2 / t ^ 2 + d / t := add_le_add h₁ h₂
      _ ≤ (1 + ‖y‖) ^ 2 / t ^ 2 + d / t * (1 + ‖y‖) ^ 2 :=
          add_le_add (div_le_div_of_nonneg_right h₃ (by positivity))
            (le_mul_of_one_le_right (by positivity) h₄)
      _ = (1 / t ^ 2 + d / t) * (1 + ‖y‖) ^ 2 := by ring
  have hKcomp : heatKernel s y ≤ 4 ^ (d / 2) * heatKernel (2 * t) y :=
    (heatKernel_le_mul_heatKernel hs₀ hs' y).trans <| mul_le_mul_of_nonneg_right
      (rpow_le_rpow (by positivity) ((div_le_iff₀ hs₀).2 (by linarith)) (by positivity))
      (heatKernel_pos h2t y).le
  rw [laplacian_heatKernel, abs_mul, abs_of_pos hKs]
  calc |‖y‖ ^ 2 / (4 * s ^ 2) - d / (2 * s)| * heatKernel s y
      ≤ (1 / t ^ 2 + d / t) * (1 + ‖y‖) ^ 2 * (4 ^ (d / 2) * heatKernel (2 * t) y) :=
        mul_le_mul hcoef hKcomp hKs.le (by positivity)
    _ = (1 / t ^ 2 + d / t) * 4 ^ (d / 2) * ((1 + ‖y‖) ^ 2 * heatKernel (2 * t) y) := by ring
    _ ≤ (1 / t ^ 2 + d / t) * 4 ^ (d / 2) * (C * heatKernel (2 * (2 * t)) y) :=
        mul_le_mul_of_nonneg_left (hC y) (by positivity)
    _ = (1 / t ^ 2 + d / t) * 4 ^ (d / 2) * C * heatKernel (2 * (2 * t)) y := by ring

/-- **The heat equation.** For `t > 0` and `g` measurable and essentially bounded, the function
`u(s, x) = (K_s ⋆ g)(x)` satisfies `∂ₜu(t, x) = Δu(t, x)`. -/
theorem hasDerivAt_heatKernel_convolution [CompleteSpace F] (ht : 0 < t)
    (hg : AEStronglyMeasurable g) (hM : ∀ᵐ y, ‖g y‖ ≤ M) (x : E) :
    HasDerivAt (fun s => (heatKernel s ⋆ g) x) (Δ (heatKernel t ⋆ g) x) t := by
  obtain ⟨B, hB₀, hB⟩ := exists_abs_laplacian_heatKernel_le (E := E) ht
  have hg' : ∀ᵐ y, ‖g (x - y)‖ ≤ M :=
    (quasiMeasurePreserving_sub_left_of_right_invariant (volume : Measure E) x).ae hM
  have hball : ∀ s ∈ ball t (t / 2), t / 2 < s ∧ s ≤ 2 * t := fun s hs => by
    rw [mem_ball, Real.dist_eq, abs_lt] at hs
    constructor <;> linarith [hs.1, hs.2]
  have hΔ : Continuous (Δ (heatKernel t : E → ℝ)) := by
    rw [show Δ (heatKernel t : E → ℝ) = fun y => (‖y‖ ^ 2 / (4 * t ^ 2) -
      finrank ℝ E / (2 * t)) * heatKernel t y from funext (laplacian_heatKernel t)]
    exact (((continuous_norm.pow 2).div_const _).sub continuous_const).mul
      (contDiff_heatKernel t (k := 0)).continuous
  rw [laplacian_heatKernel_convolution ht hg hM x]
  simp only [convolution_def]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds t (half_pos ht))
    (F' := fun s y => lsmul ℝ ℝ (Δ (heatKernel s : E → ℝ) y) (g (x - y)))
    (bound := fun y => B * heatKernel (2 * (2 * t)) y * M)
    (Filter.Eventually.of_forall fun s => (contDiff_heatKernel s (k := 0)).continuous
      |>.aestronglyMeasurable.convolution_integrand_snd (lsmul ℝ ℝ) hg x)
    (convolutionExists_of_integrable_of_ae_norm_le _ (integrable_heatKernel ht) hg hM x)
    (hΔ.aestronglyMeasurable.convolution_integrand_snd (lsmul ℝ ℝ) hg x) ?_
    (((integrable_heatKernel (by positivity)).const_mul B).mul_const M) ?_).2
  · filter_upwards [hg'] with y hy s hs
    rw [lsmul_apply, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul (hB s (hball s hs).1 (hball s hs).2 y) hy (norm_nonneg _)
      (mul_nonneg hB₀ (heatKernel_pos (by positivity) y).le)
  · refine Filter.Eventually.of_forall fun y s hs => ?_
    simpa only [lsmul_apply] using
      (hasDerivAt_heatKernel (by linarith [(hball s hs).1]) y).smul_const (g (x - y))

end TauCeti
