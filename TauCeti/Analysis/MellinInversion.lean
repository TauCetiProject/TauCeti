/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Integrability and sector holomorphy of Mellin–Barnes vertical integrals

Mathlib's `mellinInv σ f y` is `(1 / 2π) ∫ y^{-(σ + i t)} • f(σ + i t) dt` for real `y > 0`. This
file records that its integrand is integrable whenever `f` is integrable on the vertical line
`Re s = σ`, and extends convergence and holomorphy to complex arguments `w` in sectors of the slit
plane: if `g : ℝ → E` decays faster than `exp (-θ' |y|)` for every `θ' < θ`, then the vertical
Mellin–Barnes integral `w ↦ ∫ w^{σ + i y} • g y dy` converges and is complex differentiable on the
open sector `{w ∈ slitPlane | |arg w| < θ}`, and in particular on all of `slitPlane` when `θ = π`.

## Main results

* `Complex.VerticalIntegrable.integrable_cpow_smul`: the integrand of the Mellin inversion
  integral of a vertically integrable function is integrable for `y > 0`.
* `TauCeti.integrable_cpow_vertical_smul`: `y ↦ w^{σ + i y} • g y` is integrable whenever `w ≠ 0`,
  `|arg w| < θ`, and `‖g y‖ ≤ C exp (-θ |y|)`.
* `TauCeti.differentiableOn_integral_cpow_vertical_smul_sector` and
  `TauCeti.differentiableOn_integral_cpow_vertical_smul`: complex differentiability of
  `w ↦ ∫ w^{σ + i y} • g y dy` on `{w ∈ slitPlane | |arg w| < θ}` and on `slitPlane`.
-/

public section

open Real MeasureTheory Filter Set
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

end Complex

namespace TauCeti

/-- If `w ≠ 0`, `|arg w| < θ`, and `‖g y‖ ≤ C exp (-θ |y|)`, then `y ↦ w^{σ + i y} • g y` is
integrable on `ℝ`. -/
theorem integrable_cpow_vertical_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {g : ℝ → E} (hg : AEStronglyMeasurable g) {w : ℂ} (hw : w ≠ 0) (σ : ℝ) {C θ : ℝ}
    (hθ : |w.arg| < θ) (hbound : ∀ y : ℝ, ‖g y‖ ≤ C * Real.exp (-θ * |y|)) :
    Integrable fun y : ℝ ↦ w ^ ((σ : ℂ) + y * I) • g y := by
  have hcont : Continuous fun y : ℝ ↦ w ^ ((σ : ℂ) + y * I) := by
    simp_rw [cpow_def_of_ne_zero hw]
    fun_prop
  set C₁ : ℝ := max C 0
  refine ((integrable_exp_neg_mul_abs (sub_pos.2 hθ)).const_mul (‖w‖ ^ σ * C₁)).mono'
    (hcont.aestronglyMeasurable.smul hg) (Eventually.of_forall fun y ↦ ?_)
  rw [norm_smul, norm_cpow_of_ne_zero hw, div_eq_mul_inv, ← Real.exp_neg]
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
    add_zero, add_im, mul_im, zero_add]
  have harg : Real.exp (-(w.arg * y)) ≤ Real.exp (|w.arg| * |y|) := by
    refine Real.exp_le_exp.2 ?_
    calc -(w.arg * y) ≤ |-(w.arg * y)| := le_abs_self _
      _ = |w.arg| * |y| := by rw [abs_neg, abs_mul]
  have hg_le : ‖g y‖ ≤ C₁ * Real.exp (-θ * |y|) :=
    (hbound y).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le)
  calc ‖w‖ ^ σ * Real.exp (-(w.arg * y)) * ‖g y‖
      ≤ (‖w‖ ^ σ * Real.exp (|w.arg| * |y|)) * (C₁ * Real.exp (-θ * |y|)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left harg (by positivity)) hg_le
          (norm_nonneg _) (by positivity)
    _ = ‖w‖ ^ σ * C₁ * Real.exp (-((θ - |w.arg|) * |y|)) := by
        rw [mul_mul_mul_comm, ← Real.exp_add]
        congr 2
        ring

/-- **Sector holomorphy of vertical Mellin–Barnes integrals.** If `g : ℝ → E` is almost-everywhere
strongly measurable and satisfies `‖g y‖ ≤ C exp (-θ' |y|)` for every `θ' < θ`, then
`w ↦ ∫ w^{σ + i y} • g y dy` is complex differentiable on `{w ∈ slitPlane | |arg w| < θ}`. -/
theorem differentiableOn_integral_cpow_vertical_smul_sector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} (hg : AEStronglyMeasurable g) (σ θ : ℝ)
    (hbound : ∀ θ' < θ, ∃ C : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * Real.exp (-θ' * |y|)) :
    DifferentiableOn ℂ (fun w : ℂ ↦ ∫ y : ℝ, w ^ ((σ : ℂ) + y * I) • g y)
      {w ∈ slitPlane | |w.arg| < θ} := by
  rintro w₀ ⟨hw₀, harg₀⟩
  -- Choose nested angles `|arg w₀| < θ₁ < θ₂ < θ` and a small open neighborhood `U` of `w₀`.
  have hw₀_ne : w₀ ≠ 0 := slitPlane_ne_zero hw₀
  have hw₀_pos : 0 < ‖w₀‖ := norm_pos_iff.2 hw₀_ne
  set θ₁ : ℝ := (|w₀.arg| + θ) / 2
  set θ₂ : ℝ := (θ₁ + θ) / 2
  set δ : ℝ := (θ₂ - θ₁) / 2
  have hθ₁ : |w₀.arg| < θ₁ := by dsimp [θ₁]; linarith
  have hθ₂ : θ₂ < θ := by dsimp [θ₂, θ₁]; linarith
  have hδ : 0 < δ := by dsimp [δ, θ₂, θ₁]; linarith
  obtain ⟨C, hC⟩ := hbound θ₂ hθ₂
  set C₁ : ℝ := max C 0
  set B : ℝ := max ((‖w₀‖ / 2) ^ (σ - 1)) ((3 * ‖w₀‖ / 2) ^ (σ - 1))
  have hB : 0 ≤ B := le_trans (by positivity) (le_max_left _ _)
  let U : Set ℂ := slitPlane ∩ (Metric.ball w₀ (‖w₀‖ / 2) ∩ {w : ℂ | |w.arg| < θ₁})
  have hU : U ∈ 𝓝 w₀ :=
    Filter.inter_mem (isOpen_slitPlane.mem_nhds hw₀)
      (Filter.inter_mem (Metric.ball_mem_nhds w₀ (half_pos hw₀_pos))
        (((continuousAt_arg hw₀).norm).eventually (gt_mem_nhds hθ₁)))
  let F : ℂ → ℝ → E := fun w y ↦ w ^ ((σ : ℂ) + y * I) • g y
  let F' : ℂ → ℝ → E := fun w y ↦ (((σ : ℂ) + y * I) * w ^ ((σ : ℂ) + y * I - 1)) • g y
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (F w) volume := by
    filter_upwards [hU] with w hw
    have hw_ne : w ≠ 0 := slitPlane_ne_zero hw.1
    have hcont : Continuous fun y : ℝ ↦ w ^ ((σ : ℂ) + y * I) := by
      simp_rw [cpow_def_of_ne_zero hw_ne]
      fun_prop
    exact hcont.aestronglyMeasurable.smul hg
  have hF_int : Integrable (F w₀) volume :=
    integrable_cpow_vertical_smul hg hw₀_ne σ (by dsimp [θ₂, θ₁]; linarith) hC
  have hF'_meas : AEStronglyMeasurable (F' w₀) volume := by
    have hcont : Continuous fun y : ℝ ↦ ((σ : ℂ) + y * I) * w₀ ^ ((σ : ℂ) + y * I - 1) := by
      have hpow : Continuous fun y : ℝ ↦ w₀ ^ ((σ : ℂ) + y * I - 1) := by
        simp_rw [cpow_def_of_ne_zero hw₀_ne]
        fun_prop
      exact (by fun_prop : Continuous fun y : ℝ ↦ (σ : ℂ) + y * I).mul hpow
    exact hcont.aestronglyMeasurable.smul hg
  -- Uniformly dominate `‖F' w y‖` on `U` by `K exp (-(δ * |y|))`.
  set K : ℝ := (|σ| + 1) * (1 / δ + 1) * B * C₁
  have h_bound : ∀ᵐ y : ℝ ∂volume, ∀ w ∈ U, ‖F' w y‖ ≤ K * Real.exp (-(δ * |y|)) := by
    refine Eventually.of_forall fun y w ⟨hw_slit, hw_ball, hw_arg⟩ ↦ ?_
    have hw_ne : w ≠ 0 := slitPlane_ne_zero hw_slit
    have hw_dist : ‖w - w₀‖ < ‖w₀‖ / 2 := mem_ball_iff_norm.1 hw_ball
    have hw_lo : ‖w₀‖ / 2 ≤ ‖w‖ := by
      have := norm_sub_norm_le w₀ w
      rw [norm_sub_rev] at this
      linarith
    have hw_hi : ‖w‖ ≤ 3 * ‖w₀‖ / 2 := by
      have := norm_sub_norm_le w w₀
      linarith
    have hB_le : ‖w‖ ^ (σ - 1) ≤ B := by
      rcases le_total 0 (σ - 1) with hp | hp
      · exact (Real.rpow_le_rpow (norm_nonneg w) hw_hi hp).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_nonpos (half_pos hw₀_pos) hw_lo hp).trans (le_max_left _ _)
    have hs_norm : ‖(σ : ℂ) + y * I‖ ≤ (|σ| + 1) * (1 + |y|) := by
      calc ‖(σ : ℂ) + y * I‖ ≤ ‖(σ : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
        _ = |σ| + |y| := by simp
        _ ≤ (|σ| + 1) * (1 + |y|) := by nlinarith [abs_nonneg σ, abs_nonneg y]
    have hlin_exp : 1 + |y| ≤ (1 / δ + 1) * Real.exp (δ * |y|) := by
      have h1 : 1 + δ * |y| ≤ Real.exp (δ * |y|) := by linarith [Real.add_one_le_exp (δ * |y|)]
      have h2 : 1 + |y| ≤ (1 / δ + 1) * (1 + δ * |y|) := by
        have hδ0 : δ ≠ 0 := hδ.ne'
        have : (1 / δ + 1) * (1 + δ * |y|) = 1 / δ + 1 + |y| + δ * |y| := by field_simp; ring
        rw [this]
        have : 0 ≤ 1 / δ := by positivity
        nlinarith [abs_nonneg y]
      exact h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
    have hpow_norm : ‖w ^ ((σ : ℂ) + y * I - 1)‖ ≤ B * Real.exp (θ₁ * |y|) := by
      rw [norm_cpow_of_ne_zero hw_ne, div_eq_mul_inv, ← Real.exp_neg]
      simp only [sub_re, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, one_re, sub_im, add_im, mul_im, zero_add, one_im, sub_zero]
      have harg : Real.exp (-(w.arg * y)) ≤ Real.exp (θ₁ * |y|) := by
        refine Real.exp_le_exp.2 ?_
        calc -(w.arg * y) ≤ |-(w.arg * y)| := le_abs_self _
          _ = |w.arg| * |y| := by rw [abs_neg, abs_mul]
          _ ≤ θ₁ * |y| := mul_le_mul_of_nonneg_right hw_arg.le (abs_nonneg y)
      exact mul_le_mul hB_le harg (Real.exp_pos _).le hB
    have hg_le : ‖g y‖ ≤ C₁ * Real.exp (-θ₂ * |y|) :=
      (hC y).trans (mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.exp_pos _).le)
    have hcoeff : ‖((σ : ℂ) + y * I) * w ^ ((σ : ℂ) + y * I - 1)‖ ≤
        ((|σ| + 1) * (1 / δ + 1) * B) * Real.exp ((δ + θ₁) * |y|) := by
      rw [norm_mul]
      calc ‖(σ : ℂ) + y * I‖ * ‖w ^ ((σ : ℂ) + y * I - 1)‖
          ≤ ((|σ| + 1) * ((1 / δ + 1) * Real.exp (δ * |y|))) * (B * Real.exp (θ₁ * |y|)) :=
            mul_le_mul (hs_norm.trans (mul_le_mul_of_nonneg_left hlin_exp (by positivity)))
              hpow_norm (norm_nonneg _) (by positivity)
        _ = ((|σ| + 1) * (1 / δ + 1) * B) * (Real.exp (δ * |y|) * Real.exp (θ₁ * |y|)) := by ring
        _ = _ := by rw [← Real.exp_add]; ring_nf
    dsimp only [F']
    rw [norm_smul]
    calc ‖((σ : ℂ) + y * I) * w ^ ((σ : ℂ) + y * I - 1)‖ * ‖g y‖
        ≤ (((|σ| + 1) * (1 / δ + 1) * B) * Real.exp ((δ + θ₁) * |y|)) *
            (C₁ * Real.exp (-θ₂ * |y|)) :=
          mul_le_mul hcoeff hg_le (norm_nonneg _) (by positivity)
      _ = K * (Real.exp ((δ + θ₁) * |y|) * Real.exp (-θ₂ * |y|)) := by dsimp [K]; ring
      _ = K * Real.exp (-(δ * |y|)) := by
          rw [← Real.exp_add]
          congr 2
          dsimp [δ]
          ring
  -- Differentiate under the integral sign.
  have h_diff : ∀ᵐ y : ℝ ∂volume, ∀ w ∈ U, HasDerivAt (F · y) (F' w y) w :=
    Eventually.of_forall fun y w hw ↦
      ((hasStrictDerivAt_cpow_const hw.1).hasDerivAt).smul_const (g y)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU hF_meas hF_int hF'_meas h_bound
    ((integrable_exp_neg_mul_abs hδ).const_mul K)
    h_diff).2.differentiableAt.differentiableWithinAt

/-- **Slit-plane holomorphy of vertical Mellin–Barnes integrals.** If `g : ℝ → E` is
almost-everywhere strongly measurable and satisfies `‖g y‖ ≤ C exp (-θ' |y|)` for every `θ' < π`,
then `w ↦ ∫ w^{σ + i y} • g y dy` is complex differentiable on `slitPlane`. -/
theorem differentiableOn_integral_cpow_vertical_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} (hg : AEStronglyMeasurable g) (σ : ℝ)
    (hbound : ∀ θ' < π, ∃ C : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * Real.exp (-θ' * |y|)) :
    DifferentiableOn ℂ (fun w : ℂ ↦ ∫ y : ℝ, w ^ ((σ : ℂ) + y * I) • g y) slitPlane := by
  have h := differentiableOn_integral_cpow_vertical_smul_sector hg σ π hbound
  rwa [sep_eq_self_iff_mem_true.2 fun w hw ↦ abs_arg_lt_pi_of_mem_slitPlane hw] at h

end TauCeti
