/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Barnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Mellin–Barnes integral representations of the Gauss hypergeometric function

This file establishes vertical-line convergence and holomorphy on `Complex.slitPlane` for
Mellin–Barnes integrals, and evaluates the two classical Mellin–Barnes integrals for the
regularized Gauss hypergeometric function ([DLMF 15.6.6–15.6.7](https://dlmf.nist.gov/15.6#E6)):

1. **DLMF 15.6.6** (in `-z`, on the cut plane `-z ∈ Complex.slitPlane`):
   `(2π Γ(a) Γ(b))⁻¹ ∫ Γ(a + σ + i y) Γ(b + σ + i y) Γ(-σ - i y) (Γ(c + σ + i y))⁻¹`
   `  (-z)^{σ + i y} dy`.
   By Stirling's vertical-line estimates (`TauCeti.exists_norm_Gamma_add_mul_I_le_exp_neg` and
   `TauCeti.exists_norm_inv_Gamma_add_mul_I_le_exp`), the integrand decays exponentially at rate
   `π - |arg (-z)| > 0`. The integral is holomorphic in `z` on `-z ∈ slitPlane` and entire in `c`.
   For `Re b < Re c` and `-min(Re a, Re b) < σ < 0`, it equals `Complex.eulerIntegral a b c z`,
   proved by inserting the Mellin–Barnes integral of `(1 + x t)^{-a}` into Euler's integral for
   `z = -x < 0`, applying Fubini's theorem, and extending to `-z ∈ slitPlane` by the identity
   principle on the slit plane (`AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq`).

2. **DLMF 15.6.7** (in `1 - z`, on the cut plane `1 - z ∈ Complex.slitPlane`):
   `(2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫ Γ(a + σ + i y) Γ(b + σ + i y)`
   `  Γ(c - a - b - σ - i y) Γ(-σ - i y) (1 - z)^{σ + i y} dy`.
   The four Gamma factors decay at rate `2π`, giving exponential decay at rate
   `2π - |arg (1 - z)| > π > 0` and holomorphy in `z` on `1 - z ∈ slitPlane`. On the open unit
   disk `‖z‖ < 1`, when `-min(Re a, Re b) < σ < min(0, Re (c - a - b))`, this integral equals
   `Complex.regularizedGaussHGFun a b c z`, proved by expanding `(1 - z)^{σ + i y}` in powers of
   `z` on `‖z‖ < 1 / 2`, integrating term by term via dominated convergence and Barnes's first
   lemma (`Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`), and extending
   to `‖z‖ < 1` by the identity theorem.

## Main results

* `Complex.integrable_mul_cpow_vertical`: vertical-line integrability of `g(y) w^{σ + i y}` on
  `Complex.slitPlane` for any continuous kernel `g` decaying at exponential rate `α ≥ π`.
* `Complex.differentiableOn_integral_mul_cpow_vertical`: holomorphy of
  `w ↦ ∫ g(y) w^{σ + i y} dy` on `Complex.slitPlane`.
* `Complex.integrable_mellinBarnes_neg`: integrability of the DLMF 15.6.6 integrand on every
  pole-avoiding vertical line for `-z ∈ slitPlane`.
* `Complex.differentiableOn_mellinBarnes_neg`: holomorphy of the DLMF 15.6.6 integral in `z` on
  `{z | -z ∈ slitPlane}`.
* `Complex.differentiable_mellinBarnes_neg_param_c`: entireness of the DLMF 15.6.6 integral in `c`.
* `Complex.eulerIntegral_eq_mellinBarnes`: DLMF 15.6.6 for `Complex.eulerIntegral` when
  `Re b < Re c`, `-z ∈ slitPlane`, and `-min(Re a, Re b) < σ < 0`.
* `Complex.integrable_mellinBarnes_one_sub`: integrability of the DLMF 15.6.7 integrand on every
  pole-avoiding vertical line for `1 - z ∈ slitPlane`.
* `Complex.differentiableOn_mellinBarnes_one_sub`: holomorphy of the DLMF 15.6.7 integral in `z`
  on `{z | 1 - z ∈ slitPlane}`.
* `Complex.regularizedGaussHGFun_eq_mellinBarnes_one_sub`: DLMF 15.6.7 for
  `Complex.regularizedGaussHGFun` on `‖z‖ < 1` when `-min(Re a, Re b) < σ < min(0, Re (c - a - b))`.

## References

* NIST Digital Library of Mathematical Functions, equations 15.6.6 and 15.6.7.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.5.
-/

public section

noncomputable section

open Real Set MeasureTheory Filter
open Complex hiding exp continuous_exp log
open scoped Nat Topology

namespace Complex

/-! ### Slit-plane Mellin–Barnes convergence and holomorphy -/

private lemma norm_cpow_vertical_le (w : ℂ) (σ y : ℝ) :
    ‖w ^ ((σ : ℂ) + y * I)‖ ≤ ‖w‖ ^ σ * Real.exp (|arg w| * |y|) := by
  refine (norm_cpow_le w ((σ : ℂ) + y * I)).trans ?_
  simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_zero,
    add_zero, add_im, mul_im, zero_add, div_eq_mul_inv, ← Real.exp_neg]
  gcongr
  simpa [abs_mul] using neg_le_abs (arg w * y)

/-- Locally around any `w₀ ∈ slitPlane`, `w` stays in `slitPlane` with `|arg w|` bounded strictly
below `π` and `‖w‖ ^ (σ - 1)` bounded above. -/
private lemma exists_ball_slitPlane_arg_bound {w₀ : ℂ} (hw₀ : w₀ ∈ slitPlane) (σ : ℝ) :
    ∃ r > 0, ∃ θ < π, ∃ M > 0, ∀ w ∈ Metric.ball w₀ r,
      w ∈ slitPlane ∧ |arg w| ≤ θ ∧ ‖w‖ ^ (σ - 1) ≤ M := by
  have hlt : |arg w₀| < π := abs_arg_lt_pi_of_mem_slitPlane hw₀
  set θ : ℝ := (|arg w₀| + π) / 2
  have hθ : θ < π := by dsimp [θ]; linarith
  have harg0 : |arg w₀| < θ := by dsimp [θ]; linarith
  have hw0_pos : 0 < ‖w₀‖ := norm_pos_iff.mpr (slitPlane_ne_zero hw₀)
  set M : ℝ := ‖w₀‖ ^ (σ - 1) + 1
  have hM : 0 < M := add_pos_of_nonneg_of_pos (Real.rpow_nonneg (norm_nonneg w₀) _) one_pos
  have h1 : ∀ᶠ w in 𝓝 w₀, w ∈ slitPlane := isOpen_slitPlane.mem_nhds hw₀
  have h2 : ∀ᶠ w in 𝓝 w₀, |arg w| < θ :=
    (continuousAt_arg hw₀).abs.eventually (Iio_mem_nhds harg0)
  have h3 : ∀ᶠ w in 𝓝 w₀, ‖w‖ ^ (σ - 1) < M := by
    have hcont : ContinuousAt (fun w : ℂ ↦ ‖w‖ ^ (σ - 1)) w₀ :=
      continuous_norm.continuousAt.rpow_const (Or.inl hw0_pos.ne')
    exact hcont.eventually (Iio_mem_nhds (by dsimp [M]; linarith))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and (h2.and h3))
  exact ⟨r, hr, θ, hθ, M, hM, fun w hw ↦
    ⟨(hball w hw).1, (hball w hw).2.1.le, (hball w hw).2.2.le⟩⟩

/-- Vertical-line integrability of `y ↦ g y * w ^ (σ + i y)` on `Complex.slitPlane` for any
continuous kernel `g` decaying at exponential rate `α ≥ π`. -/
theorem integrable_mul_cpow_vertical {g : ℝ → ℂ} {α : ℝ} (hα : π ≤ α) (hg_cont : Continuous g)
    (hg_decay : ∀ ε > 0, ∃ C : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * Real.exp (-((α - ε) * |y|)))
    {w : ℂ} (hw : w ∈ slitPlane) (σ : ℝ) :
    Integrable fun y : ℝ ↦ g y * w ^ ((σ : ℂ) + y * I) := by
  have hθ : |arg w| < π := abs_arg_lt_pi_of_mem_slitPlane hw
  set ε : ℝ := (α - |arg w|) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hgb⟩ := hg_decay ε hε
  have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hgb 0)
  have hpow_cont : Continuous fun y : ℝ ↦ w ^ ((σ : ℂ) + y * I) :=
    continuous_iff_continuousAt.mpr fun y ↦
      ContinuousAt.cpow continuousAt_const (by fun_prop) hw
  refine ((TauCeti.integrable_exp_neg_mul_abs hε).const_mul (C * ‖w‖ ^ σ)).mono'
    (hg_cont.mul hpow_cont).aestronglyMeasurable (.of_forall fun y ↦ ?_)
  rw [norm_mul]
  have hb2 := norm_cpow_vertical_le w σ y
  calc ‖g y‖ * ‖w ^ ((σ : ℂ) + y * I)‖
      ≤ (C * Real.exp (-((α - ε) * |y|))) * (‖w‖ ^ σ * Real.exp (|arg w| * |y|)) := by
        gcongr
        exact hgb y
    _ = C * ‖w‖ ^ σ * (Real.exp (-((α - ε) * |y|)) * Real.exp (|arg w| * |y|)) := by ring
    _ = C * ‖w‖ ^ σ * Real.exp (-(ε * |y|)) := by
        rw [← Real.exp_add]
        congr 2
        dsimp [ε]
        ring

/-- Holomorphy on `Complex.slitPlane` of the Mellin–Barnes vertical integral
`w ↦ ∫ y, g y * w ^ (σ + i y)` for any continuous kernel `g` decaying at exponential rate
`α ≥ π`. -/
theorem differentiableOn_integral_mul_cpow_vertical {g : ℝ → ℂ} {α : ℝ} (hα : π ≤ α)
    (hg_cont : Continuous g)
    (hg_decay : ∀ ε > 0, ∃ C : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * Real.exp (-((α - ε) * |y|)))
    (σ : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ ↦ ∫ y : ℝ, g y * w ^ ((σ : ℂ) + y * I)) slitPlane := by
  intro w₀ hw₀
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨r, hr, θ, hθ, M, hM, hball⟩ := exists_ball_slitPlane_arg_bound hw₀ σ
  set ε : ℝ := (α - θ) / 3
  have hε : 0 < ε := by dsimp [ε]; linarith
  obtain ⟨C, hgb⟩ := hg_decay ε hε
  have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hgb 0)
  let F : ℂ → ℝ → ℂ := fun w y ↦ g y * w ^ ((σ : ℂ) + y * I)
  let F' : ℂ → ℝ → ℂ := fun w y ↦ g y * (((σ : ℂ) + y * I) * w ^ ((σ : ℂ) + y * I - 1))
  set K : ℝ := C * (|σ| + ε⁻¹) * M
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (F w) volume := by
    filter_upwards [Metric.ball_mem_nhds w₀ hr] with w hw
    exact (integrable_mul_cpow_vertical hα hg_cont hg_decay (hball w hw).1 σ).1
  have hF_int : Integrable (F w₀) volume :=
    integrable_mul_cpow_vertical hα hg_cont hg_decay hw₀ σ
  have hF'_meas : AEStronglyMeasurable (F' w₀) volume := by
    have hpow : Continuous fun y : ℝ ↦ w₀ ^ ((σ : ℂ) + y * I - 1) :=
      continuous_iff_continuousAt.mpr fun y ↦
        ContinuousAt.cpow continuousAt_const (by fun_prop) hw₀
    exact (hg_cont.mul ((by fun_prop : Continuous fun y : ℝ ↦ (σ : ℂ) + y * I).mul
      hpow)).aestronglyMeasurable
  have h_bound : ∀ᵐ y ∂volume, ∀ w ∈ Metric.ball w₀ r, ‖F' w y‖ ≤ K * Real.exp (-(ε * |y|)) := by
    refine .of_forall fun y w hw ↦ ?_
    obtain ⟨_, harg, hnorm_w⟩ := hball w hw
    have hb1 : ‖g y‖ ≤ C * Real.exp (-((α - ε) * |y|)) := hgb y
    have hb2 : ‖(σ : ℂ) + y * I‖ ≤ (|σ| + ε⁻¹) * Real.exp (ε * |y|) := by
      have h1 : ‖(σ : ℂ) + y * I‖ ≤ |σ| + |y| := by
        calc ‖(σ : ℂ) + y * I‖ ≤ ‖(σ : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
          _ = |σ| + |y| := by simp
      have hexp1 : 1 ≤ Real.exp (ε * |y|) := Real.one_le_exp (by positivity)
      have hexp2 : |y| ≤ ε⁻¹ * Real.exp (ε * |y|) := by
        have h := Real.add_one_le_exp (ε * |y|)
        rw [inv_mul_eq_div, le_div_iff₀' hε]
        linarith
      calc ‖(σ : ℂ) + y * I‖ ≤ |σ| + |y| := h1
        _ ≤ |σ| * Real.exp (ε * |y|) + ε⁻¹ * Real.exp (ε * |y|) := by nlinarith [abs_nonneg σ]
        _ = (|σ| + ε⁻¹) * Real.exp (ε * |y|) := by ring
    have hb3 : ‖w ^ ((σ : ℂ) + y * I - 1)‖ ≤ M * Real.exp (θ * |y|) := by
      have hexp_eq : (σ : ℂ) + y * I - 1 = ((σ - 1 : ℝ) : ℂ) + y * I := by push_cast; ring
      rw [hexp_eq]
      calc ‖w ^ (((σ - 1 : ℝ) : ℂ) + y * I)‖
          ≤ ‖w‖ ^ (σ - 1) * Real.exp (|arg w| * |y|) := norm_cpow_vertical_le w (σ - 1) y
        _ ≤ M * Real.exp (θ * |y|) := by gcongr
    simp only [F', norm_mul]
    calc ‖g y‖ * (‖(σ : ℂ) + y * I‖ * ‖w ^ ((σ : ℂ) + y * I - 1)‖)
        ≤ (C * Real.exp (-((α - ε) * |y|))) *
            (((|σ| + ε⁻¹) * Real.exp (ε * |y|)) * (M * Real.exp (θ * |y|))) := by gcongr
      _ = K * (Real.exp (-((α - ε) * |y|)) * Real.exp (ε * |y|) * Real.exp (θ * |y|)) := by
          simp only [K]; ring
      _ = K * Real.exp (-(ε * |y|)) := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 2
          dsimp [ε]
          ring
  have h_diff : ∀ᵐ y ∂volume, ∀ w ∈ Metric.ball w₀ r, HasDerivAt (F · y) (F' w y) w := by
    refine .of_forall fun y w hw ↦ ?_
    have hcpow : HasDerivAt (fun z : ℂ ↦ z ^ ((σ : ℂ) + y * I))
        (((σ : ℂ) + y * I) * w ^ ((σ : ℂ) + y * I - 1)) w := by
      simpa using (hasDerivAt_id w).cpow_const (c := (σ : ℂ) + y * I)
        (mem_slitPlane_iff.mp (hball w hw).1)
    exact hcpow.const_mul (g y)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds w₀ hr) hF_meas
    hF_int hF'_meas h_bound ((TauCeti.integrable_exp_neg_mul_abs hε).const_mul K)
    h_diff).2.differentiableAt

/-! ### DLMF 15.6.6: convergence, holomorphy, and evaluation via Euler's integral -/

private lemma continuous_mellinBarnes_neg_kernel (a b c : ℂ) {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ := by
  have hG1 : Continuous fun y : ℝ ↦ Gamma (a + (σ + y * I)) := by
    simpa only [add_assoc] using continuous_Gamma_add_mul_I (a := a + σ) (by simpa using haσ)
  have hG2 : Continuous fun y : ℝ ↦ Gamma (b + (σ + y * I)) := by
    simpa only [add_assoc] using continuous_Gamma_add_mul_I (a := b + σ) (by simpa using hbσ)
  have hG3 : Continuous fun y : ℝ ↦ Gamma (-(σ + y * I)) := by
    simpa only [neg_add, ← sub_eq_add_neg] using
      continuous_Gamma_sub_mul_I (a := -(σ : ℂ)) (by simpa using hσ)
  have hG4 : Continuous fun y : ℝ ↦ (Gamma (c + (σ + y * I)))⁻¹ :=
    differentiable_one_div_Gamma.continuous.comp (by fun_prop)
  exact ((hG1.mul hG2).mul hG3).mul hG4

private lemma exists_norm_mellinBarnes_neg_kernel_le (a b c : ℂ) {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
          (Gamma (c + (σ + y * I)))⁻¹‖ ≤ C * Real.exp (-((π - ε) * |y|)) := by
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨C₁, hC₁, h₁⟩ :=
    TauCeti.exists_norm_Gamma_add_mul_I_le_exp_neg (a + σ) (by simpa using haσ) hε4
  obtain ⟨C₂, hC₂, h₂⟩ :=
    TauCeti.exists_norm_Gamma_add_mul_I_le_exp_neg (b + σ) (by simpa using hbσ) hε4
  obtain ⟨C₃, hC₃, h₃⟩ :=
    TauCeti.exists_norm_Gamma_sub_mul_I_le_exp_neg (-(σ : ℂ)) (by simpa using hσ) hε4
  obtain ⟨C₄, _, h₄⟩ := TauCeti.exists_norm_inv_Gamma_add_mul_I_le_exp (c + σ) hε4
  refine ⟨C₁ * C₂ * C₃ * C₄, fun y ↦ ?_⟩
  have hb1 : ‖Gamma (a + (σ + y * I))‖ ≤ C₁ * Real.exp (-((π / 2 - ε / 4) * |y|)) := by
    simpa only [add_assoc] using h₁ y
  have hb2 : ‖Gamma (b + (σ + y * I))‖ ≤ C₂ * Real.exp (-((π / 2 - ε / 4) * |y|)) := by
    simpa only [add_assoc] using h₂ y
  have hb3 : ‖Gamma (-(σ + y * I))‖ ≤ C₃ * Real.exp (-((π / 2 - ε / 4) * |y|)) := by
    have heq : -((σ : ℂ) + y * I) = -(σ : ℂ) - y * I := by ring
    simpa only [heq] using h₃ y
  have hb4 : ‖(Gamma (c + (σ + y * I)))⁻¹‖ ≤ C₄ * Real.exp ((π / 2 + ε / 4) * |y|) := by
    simpa only [add_assoc] using h₄ y
  simp only [norm_mul]
  calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ * ‖Gamma (-(σ + y * I))‖ *
        ‖(Gamma (c + (σ + y * I)))⁻¹‖
      ≤ (C₁ * Real.exp (-((π / 2 - ε / 4) * |y|))) *
          (C₂ * Real.exp (-((π / 2 - ε / 4) * |y|))) *
          (C₃ * Real.exp (-((π / 2 - ε / 4) * |y|))) *
          (C₄ * Real.exp ((π / 2 + ε / 4) * |y|)) := by gcongr
    _ = C₁ * C₂ * C₃ * C₄ *
          (Real.exp (-((π / 2 - ε / 4) * |y|)) * Real.exp (-((π / 2 - ε / 4) * |y|)) *
          Real.exp (-((π / 2 - ε / 4) * |y|)) * Real.exp ((π / 2 + ε / 4) * |y|)) := by ring
    _ = C₁ * C₂ * C₃ * C₄ * Real.exp (-((π - ε) * |y|)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-- Integrability of the DLMF 15.6.6 Mellin–Barnes integrand on every pole-avoiding vertical line
`Re s = σ` for `-z ∈ Complex.slitPlane`. No pole-avoidance hypothesis is needed on `c` because
`(Γ(c + s))⁻¹` is entire. -/
theorem integrable_mellinBarnes_neg (a b c : ℂ) {z : ℂ} (hz : -z ∈ slitPlane) {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) :=
  integrable_mul_cpow_vertical le_rfl (continuous_mellinBarnes_neg_kernel a b c haσ hbσ hσ)
    (fun _ hε ↦ exists_norm_mellinBarnes_neg_kernel_le a b c haσ hbσ hσ hε) hz σ

/-- Holomorphy of the DLMF 15.6.6 Mellin–Barnes integral in `z` on the cut plane
`{z | -z ∈ Complex.slitPlane}`. -/
theorem differentiableOn_mellinBarnes_neg (a b c : ℂ) {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    DifferentiableOn ℂ (fun z : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I))
      {z : ℂ | -z ∈ slitPlane} :=
  (differentiableOn_integral_mul_cpow_vertical le_rfl
    (continuous_mellinBarnes_neg_kernel a b c haσ hbσ hσ)
    (fun _ hε ↦ exists_norm_mellinBarnes_neg_kernel_le a b c haσ hbσ hσ hε) σ).comp
    differentiable_neg.differentiableOn (fun _ hz ↦ hz)

/-- Entireness of the DLMF 15.6.6 Mellin–Barnes integral in the lower parameter `c`. -/
theorem differentiable_mellinBarnes_neg_param_c (a b : ℂ) {z : ℂ} (hz : -z ∈ slitPlane)
    {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Differentiable ℂ fun c : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  intro c₀
  have hθ : |arg (-z)| < π := abs_arg_lt_pi_of_mem_slitPlane hz
  set ε : ℝ := (π - |arg (-z)|) / 5
  have hε : 0 < ε := by dsimp [ε]; linarith
  have haσ' : ∀ n : ℕ, (a + σ).re ≠ -n := by simpa using haσ
  have hbσ' : ∀ n : ℕ, (b + σ).re ≠ -n := by simpa using hbσ
  have hσ' : ∀ n : ℕ, (-(σ : ℂ)).re ≠ -n := by simpa using hσ
  obtain ⟨C₁, hC₁, h₁⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le_exp_neg (a + σ) haσ' hε
  obtain ⟨C₂, hC₂, h₂⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le_exp_neg (b + σ) hbσ' hε
  obtain ⟨C₃, hC₃, h₃⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le_exp_neg (-(σ : ℂ)) hσ' hε
  obtain ⟨C₄, _, h₄⟩ :=
    TauCeti.exists_norm_deriv_inv_Gamma_add_mul_I_le_exp_on_closedBall (c₀ + σ) 1 hε
  let g : ℝ → ℂ := fun y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
      (-z) ^ ((σ : ℂ) + y * I)
  let F : ℂ → ℝ → ℂ := fun c y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
      (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ ((σ : ℂ) + y * I)
  let F' : ℂ → ℝ → ℂ := fun c y ↦
    g y * deriv (fun w : ℂ ↦ (Gamma (w + (σ + y * I)))⁻¹) c
  set K : ℝ := C₁ * C₂ * C₃ * C₄ * ‖-z‖ ^ σ
  have hF_meas : ∀ᶠ c in 𝓝 c₀, AEStronglyMeasurable (F c) volume :=
    .of_forall fun c ↦ (integrable_mellinBarnes_neg a b c hz haσ hbσ hσ).1
  have hF_int : Integrable (F c₀) volume :=
    integrable_mellinBarnes_neg a b c₀ hz haσ hbσ hσ
  have hF'_meas : AEStronglyMeasurable (F' c₀) volume := by
    have hcont_g : Continuous g := by
      have hG1 : Continuous fun y : ℝ ↦ Gamma (a + (σ + y * I)) := by
        simpa only [add_assoc] using continuous_Gamma_add_mul_I haσ'
      have hG2 : Continuous fun y : ℝ ↦ Gamma (b + (σ + y * I)) := by
        simpa only [add_assoc] using continuous_Gamma_add_mul_I hbσ'
      have hG3 : Continuous fun y : ℝ ↦ Gamma (-(σ + y * I)) := by
        simpa only [neg_add, ← sub_eq_add_neg] using continuous_Gamma_sub_mul_I hσ'
      have hpow : Continuous fun y : ℝ ↦ (-z) ^ ((σ : ℂ) + y * I) :=
        continuous_iff_continuousAt.mpr fun y ↦
          ContinuousAt.cpow continuousAt_const (by fun_prop) hz
      exact ((hG1.mul hG2).mul hG3).mul hpow
    have hderiv_eq : ∀ y : ℝ, deriv (fun w : ℂ ↦ (Gamma (w + (σ + y * I)))⁻¹) c₀ =
        deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (c₀ + (σ + y * I)) := fun y ↦ by
      have hd := (differentiable_one_div_Gamma (c₀ + (σ + y * I))).hasDerivAt.comp c₀
        ((hasDerivAt_id c₀).add_const ((σ : ℂ) + y * I))
      simpa [Function.comp_def] using hd.deriv
    have hcont_d : Continuous fun y : ℝ ↦ deriv (fun w : ℂ ↦ (Gamma (w + (σ + y * I)))⁻¹) c₀ := by
      simp_rw [hderiv_eq]
      exact (differentiable_one_div_Gamma.contDiff (n := ⊤)).continuous_deriv (by simp)
        |>.comp (by fun_prop)
    exact (hcont_g.mul hcont_d).aestronglyMeasurable
  -- Uniform exponential bound for the derivative integrand on `ball c₀ 1`.
  have h_bound : ∀ᵐ y ∂volume, ∀ c ∈ Metric.ball c₀ 1, ‖F' c y‖ ≤ K * Real.exp (-(ε * |y|)) := by
    refine .of_forall fun y c hc ↦ ?_
    have hb1 : ‖Gamma (a + (σ + y * I))‖ ≤ C₁ * Real.exp (-((π / 2 - ε) * |y|)) := by
      simpa only [add_assoc] using h₁ y
    have hb2 : ‖Gamma (b + (σ + y * I))‖ ≤ C₂ * Real.exp (-((π / 2 - ε) * |y|)) := by
      simpa only [add_assoc] using h₂ y
    have hb3 : ‖Gamma (-(σ + y * I))‖ ≤ C₃ * Real.exp (-((π / 2 - ε) * |y|)) := by
      have heq : -((σ : ℂ) + y * I) = -(σ : ℂ) - y * I := by ring
      simpa only [heq] using h₃ y
    have hb4 : ‖deriv (fun w : ℂ ↦ (Gamma (w + (σ + y * I)))⁻¹) c‖ ≤
        C₄ * Real.exp ((π / 2 + ε) * |y|) := by
      have hc' : c + (σ : ℂ) ∈ Metric.closedBall (c₀ + σ) 1 := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using (Metric.mem_ball.mp hc).le
      have hd_eq : deriv (fun w : ℂ ↦ (Gamma (w + (σ + y * I)))⁻¹) c =
          deriv (fun w : ℂ ↦ (Gamma (w + y * I))⁻¹) (c + σ) := by
        have hcomp : HasDerivAt (fun w : ℂ ↦ (Gamma ((w + σ) + y * I))⁻¹)
            (deriv (fun w : ℂ ↦ (Gamma (w + y * I))⁻¹) (c + σ)) c := by
          have hd := (differentiable_one_div_Gamma.comp
            (differentiable_id.add (differentiable_const ((y : ℂ) * I))) (c + σ)).hasDerivAt
          simpa [Function.comp_def] using hd.comp c ((hasDerivAt_id c).add_const (σ : ℂ))
        simpa only [add_assoc] using hcomp.deriv
      rw [hd_eq]
      exact h₄ (c + σ) hc' y
    have hb5 : ‖(-z) ^ ((σ : ℂ) + y * I)‖ ≤ ‖-z‖ ^ σ * Real.exp (|arg (-z)| * |y|) :=
      norm_cpow_vertical_le (-z) σ y
    simp only [F', g, norm_mul]
    calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ * ‖Gamma (-(σ + y * I))‖ *
          ‖(-z) ^ ((σ : ℂ) + y * I)‖ * ‖deriv (fun w : ℂ ↦ (Gamma (w + (σ + y * I)))⁻¹) c‖
        ≤ (C₁ * Real.exp (-((π / 2 - ε) * |y|))) * (C₂ * Real.exp (-((π / 2 - ε) * |y|))) *
            (C₃ * Real.exp (-((π / 2 - ε) * |y|))) *
            (‖-z‖ ^ σ * Real.exp (|arg (-z)| * |y|)) *
            (C₄ * Real.exp ((π / 2 + ε) * |y|)) := by gcongr
      _ = K * (Real.exp (-((π / 2 - ε) * |y|)) * Real.exp (-((π / 2 - ε) * |y|)) *
            Real.exp (-((π / 2 - ε) * |y|)) * Real.exp (|arg (-z)| * |y|) *
            Real.exp ((π / 2 + ε) * |y|)) := by simp only [K]; ring
      _ = K * Real.exp (-(ε * |y|)) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          congr 2
          dsimp [ε]
          ring
  have h_diff : ∀ᵐ y ∂volume, ∀ c ∈ Metric.ball c₀ 1, HasDerivAt (F · y) (F' c y) c := by
    refine .of_forall fun y c _ ↦ ?_
    have hd : HasDerivAt (fun w : ℂ ↦ (Gamma (w + (σ + y * I)))⁻¹)
        (deriv (fun w : ℂ ↦ (Gamma (w + (σ + y * I)))⁻¹) c) c :=
      (differentiable_one_div_Gamma.comp
        (differentiable_id.add (differentiable_const _)) c).hasDerivAt
    have hmul := hd.const_mul (g y)
    have hfun : (fun w : ℂ ↦ g y * (Gamma (w + (σ + y * I)))⁻¹) = (F · y) := by
      ext w
      simp only [F, g]
      ring
    rwa [hfun] at hmul
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds c₀ one_pos) hF_meas
    hF_int hF'_meas h_bound ((TauCeti.integrable_exp_neg_mul_abs hε).const_mul K)
    h_diff).2.differentiableAt

/-- Joint integrability on `(0, 1) × ℝ` of the Fubini kernel bridging Euler's integral and
DLMF 15.6.6 on the negative real axis. -/
private lemma integrable_eulerMellinKernel {a b c : ℂ} (hbc : b.re < c.re) {x : ℝ} (hx : 0 < x)
    {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    Integrable
      (Function.uncurry fun (t y : ℝ) ↦
        (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (((x : ℂ) ^ ((σ : ℂ) + y * I) * (t : ℂ) ^ ((σ : ℂ) + y * I)) *
            (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I)))))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hbσ_pos : 0 < (b + σ).re := by simp; linarith
  have hprod_eq : (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume : Measure ℝ) =
      ((volume : Measure ℝ).prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hG_cont : ContinuousOn
      (Function.uncurry fun (t y : ℝ) ↦
        (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (((x : ℂ) ^ ((σ : ℂ) + y * I) * (t : ℂ) ^ ((σ : ℂ) + y * I)) *
            (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I)))))
      (Ioo (0 : ℝ) 1 ×ˢ Set.univ) := by
    refine continuousOn_of_forall_continuousAt fun p hp ↦ ?_
    have ht0 : 0 < p.1 := hp.1.1
    have ht1 : 0 < 1 - p.1 := sub_pos.mpr hp.1.2
    have h1 : ContinuousAt (fun q : ℝ × ℝ ↦ (q.1 : ℂ) ^ (b - 1)) p :=
      ContinuousAt.cpow (by fun_prop) continuousAt_const (ofReal_mem_slitPlane.mpr ht0)
    have h2 : ContinuousAt (fun q : ℝ × ℝ ↦ (1 - (q.1 : ℂ)) ^ (c - b - 1)) p :=
      ContinuousAt.cpow (by fun_prop) continuousAt_const <| by
        rw [← ofReal_one, ← ofReal_sub]
        exact ofReal_mem_slitPlane.mpr ht1
    have h3 : ContinuousAt (fun q : ℝ × ℝ ↦ (x : ℂ) ^ ((σ : ℂ) + (q.2 : ℂ) * I)) p :=
      ContinuousAt.cpow continuousAt_const (by fun_prop) (ofReal_mem_slitPlane.mpr hx)
    have h4 : ContinuousAt (fun q : ℝ × ℝ ↦ (q.1 : ℂ) ^ ((σ : ℂ) + (q.2 : ℂ) * I)) p :=
      ContinuousAt.cpow (by fun_prop) (by fun_prop) (ofReal_mem_slitPlane.mpr ht0)
    have h5 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (-((σ : ℂ) + (q.2 : ℂ) * I))) p := by
      have hc : Continuous fun y : ℝ ↦ Gamma (-((σ : ℂ) + y * I)) := by
        simpa only [neg_add, ← sub_eq_add_neg] using continuous_Gamma_sub_mul_I (a := -(σ : ℂ))
          (fun n h ↦ by simp at h; linarith [n.cast_nonneg' (α := ℝ)])
      exact (hc.comp continuous_snd).continuousAt
    have h6 : ContinuousAt (fun q : ℝ × ℝ ↦ Gamma (a + ((σ : ℂ) + (q.2 : ℂ) * I))) p := by
      have hc : Continuous fun y : ℝ ↦ Gamma (a + ((σ : ℂ) + y * I)) := by
        simpa only [add_assoc] using continuous_Gamma_add_mul_I (a := a + σ)
          (fun n h ↦ by simp at h; linarith [n.cast_nonneg' (α := ℝ)])
      exact (hc.comp continuous_snd).continuousAt
    exact (h1.mul h2).mul ((h3.mul h4).mul (h5.mul h6))
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (t y : ℝ) ↦
        (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (((x : ℂ) ^ ((σ : ℂ) + y * I) * (t : ℂ) ^ ((σ : ℂ) + y * I)) *
            (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I)))))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
    rw [hprod_eq]
    exact hG_cont.aestronglyMeasurable (measurableSet_Ioo.prod MeasurableSet.univ)
  have ht_int : Integrable
      (fun t : ℝ ↦ x ^ σ * ‖(t : ℂ) ^ (b + σ - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have hbeta := (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (betaIntegral_convergent hbσ_pos hcb)
    exact (hbeta.mono_set Ioo_subset_Ioc_self).norm.const_mul (x ^ σ)
  have hy_int : Integrable
      (fun y : ℝ ↦ ‖Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I))‖) volume := by
    have hv := (verticalIntegrable_Gamma_mul_Gamma_sub (a := a) (σ := -σ)
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])).comp_neg
    refine hv.norm.congr (.of_forall fun y ↦ ?_)
    dsimp only [Function.comp_def]
    congr 2
    · congr 1; push_cast; ring
    · congr 1; push_cast; ring
  refine (ht_int.mul_prod hy_int).mono' hmeas ?_
  rw [hprod_eq]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with p hp
  have ht0 : 0 < p.1 := hp.1.1
  simp only [Function.uncurry, norm_mul]
  have hx_norm : ‖(x : ℂ) ^ ((σ : ℂ) + (p.2 : ℂ) * I)‖ = x ^ σ := by
    rw [norm_cpow_eq_rpow_re_of_pos hx]; simp
  have ht_norm : ‖(p.1 : ℂ) ^ (b - 1)‖ * ‖(p.1 : ℂ) ^ ((σ : ℂ) + (p.2 : ℂ) * I)‖ =
      ‖(p.1 : ℂ) ^ (b + σ - 1)‖ := by
    rw [norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos ht0,
      norm_cpow_eq_rpow_re_of_pos ht0, ← Real.rpow_add ht0]
    congr 1; simp; ring
  rw [hx_norm]
  exact le_of_eq <| by
    calc ‖(p.1 : ℂ) ^ (b - 1)‖ * ‖(1 - (p.1 : ℂ)) ^ (c - b - 1)‖ *
          (x ^ σ * ‖(p.1 : ℂ) ^ ((σ : ℂ) + (p.2 : ℂ) * I)‖ *
            (‖Gamma (-((σ : ℂ) + (p.2 : ℂ) * I))‖ *
              ‖Gamma (a + ((σ : ℂ) + (p.2 : ℂ) * I))‖))
        = x ^ σ * ((‖(p.1 : ℂ) ^ (b - 1)‖ * ‖(p.1 : ℂ) ^ ((σ : ℂ) + (p.2 : ℂ) * I)‖) *
            ‖(1 - (p.1 : ℂ)) ^ (c - b - 1)‖) *
            (‖Gamma (-((σ : ℂ) + (p.2 : ℂ) * I))‖ *
              ‖Gamma (a + ((σ : ℂ) + (p.2 : ℂ) * I))‖) := by ring
      _ = _ := by rw [ht_norm]

/-- DLMF 15.6.6 for `Complex.eulerIntegral` on the negative real axis `z = -x < 0`, by substituting
the Mellin–Barnes integral of `(1 + x t)^{-a}` into Euler's integral and swapping integrals. -/
private lemma eulerIntegral_neg_ofReal_eq_mellinBarnes {a b c : ℂ} (hbc : b.re < c.re)
    {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    eulerIntegral a b c (-(x : ℂ)) = (2 * π * Gamma a * Gamma b)⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I) := by
  have ha : 0 < a.re := by linarith
  have hb : 0 < b.re := by linarith
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hσ_pos : 0 < -σ := by linarith
  have hσa : -σ < a.re := by linarith
  have h2π : (2 * π : ℂ) ≠ 0 := mul_ne_zero two_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  let G : ℝ → ℝ → ℂ := fun t y ↦
    (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
      (((x : ℂ) ^ ((σ : ℂ) + y * I) * (t : ℂ) ^ ((σ : ℂ) + y * I)) *
        (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I))))
  have hG_int : Integrable (Function.uncurry G)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) :=
    integrable_eulerMellinKernel hbc hx hσ haσ hbσ
  -- Integrating in `y` first recovers Euler's integral.
  have h_ty : ∫ t in Ioo (0 : ℝ) 1, ∫ y : ℝ, G t y =
      2 * π * Gamma a * Gamma b * Gamma (c - b) * eulerIntegral a b c (-(x : ℂ)) := by
    have hinner : ∀ t ∈ Ioo (0 : ℝ) 1, ∫ y : ℝ, G t y =
        (2 * π * Gamma a) * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (1 - (-(x : ℂ)) * (t : ℂ)) ^ (-a)) := by
      intro t ht
      have hmb := integral_cpow_neg_mul_Gamma_mul_Gamma_sub hσ_pos hσa (mul_pos hx ht.1)
      rw [← integral_neg_eq_self] at hmb
      have hmb' : ∫ y : ℝ, ((x : ℂ) ^ ((σ : ℂ) + y * I) * (t : ℂ) ^ ((σ : ℂ) + y * I)) *
            (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I))) =
          2 * π * (Gamma a * (1 - (-(x : ℂ)) * (t : ℂ)) ^ (-a)) := by
        calc ∫ y : ℝ, ((x : ℂ) ^ ((σ : ℂ) + y * I) * (t : ℂ) ^ ((σ : ℂ) + y * I)) *
                (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I)))
            = ∫ y : ℝ, ((x * t : ℝ) : ℂ) ^ (-(((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I)) *
                (Gamma (((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I) *
                  Gamma (a - (((-σ : ℝ) : ℂ) + ((-y : ℝ) : ℂ) * I))) := by
              refine integral_congr_ae (.of_forall fun y ↦ ?_)
              dsimp only
              rw [← mul_cpow_ofReal_nonneg hx.le ht.1.le, ← ofReal_mul]
              congr 1
              · congr 1; push_cast; ring
              · congr 1 <;> (congr 1; push_cast; ring)
          _ = 2 * π * (Gamma a * (1 + ((x * t : ℝ) : ℂ)) ^ (-a)) := hmb
          _ = 2 * π * (Gamma a * (1 - (-(x : ℂ)) * (t : ℂ)) ^ (-a)) := by
              congr 3; push_cast; ring
      simp only [G, integral_const_mul, hmb']
      ring
    rw [setIntegral_congr_fun measurableSet_Ioo hinner, integral_const_mul,
      setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      eulerIntegral_def, ← mul_assoc]
    congr 1
    field_simp [hΓb, hΓcb]
  -- Integrating in `t` first evaluates the Beta integral for each `y`.
  have h_yt : ∫ y : ℝ, ∫ t in Ioo (0 : ℝ) 1, G t y =
      Gamma (c - b) * ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
          (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I) := by
    have hinner (y : ℝ) : ∫ t in Ioo (0 : ℝ) 1, G t y =
        Gamma (c - b) * (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I)) := by
      have hrew : ∀ t ∈ Ioo (0 : ℝ) 1, G t y =
          ((t : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
            ((x : ℂ) ^ ((σ : ℂ) + y * I) *
              (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I)))) := by
        intro t ht
        have ht0 : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.1.ne'
        have hcpow : (t : ℂ) ^ (b - 1) * (t : ℂ) ^ ((σ : ℂ) + y * I) =
            (t : ℂ) ^ (b + (σ + y * I) - 1) := by
          rw [← cpow_add _ _ ht0]; congr 1; ring
        simp only [G]
        calc (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
              ((x : ℂ) ^ ((σ : ℂ) + y * I) * (t : ℂ) ^ ((σ : ℂ) + y * I) *
                (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I))))
            = ((t : ℂ) ^ (b - 1) * (t : ℂ) ^ ((σ : ℂ) + y * I)) *
                (1 - (t : ℂ)) ^ (c - b - 1) *
                ((x : ℂ) ^ ((σ : ℂ) + y * I) *
                  (Gamma (-((σ : ℂ) + y * I)) * Gamma (a + ((σ : ℂ) + y * I)))) := by ring
          _ = _ := by rw [hcpow]
      have hsum : b + (σ + y * I) + (c - b) = c + (σ + y * I) := by ring
      rw [setIntegral_congr_fun measurableSet_Ioo hrew, integral_mul_const,
        setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
        ← betaIntegral, betaIntegral_eq_Gamma_mul_div (b + (σ + y * I)) (c - b)
          (by simp; linarith) hcb, hsum]
      ring
    simp_rw [hinner, integral_const_mul]
  -- Equate the two iterated integrals by Fubini's theorem.
  have heq : 2 * π * Gamma a * Gamma b * Gamma (c - b) * eulerIntegral a b c (-(x : ℂ)) =
      Gamma (c - b) * ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
          (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I) := by
    rw [← h_ty, ← h_yt]
    exact integral_integral_swap hG_int
  have hdenom : 2 * π * Gamma a * Gamma b * Gamma (c - b) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero h2π hΓa) hΓb) hΓcb
  have hmul := congrArg (fun w : ℂ ↦ (2 * π * Gamma a * Gamma b * Gamma (c - b))⁻¹ * w) heq
  have hcancel : (2 * π * Gamma a * Gamma b * Gamma (c - b))⁻¹ * Gamma (c - b) =
      (2 * π * Gamma a * Gamma b)⁻¹ := by
    field_simp [h2π, hΓa, hΓb, hΓcb]
  calc eulerIntegral a b c (-(x : ℂ))
      = (2 * π * Gamma a * Gamma b * Gamma (c - b))⁻¹ *
          (2 * π * Gamma a * Gamma b * Gamma (c - b) * eulerIntegral a b c (-(x : ℂ))) := by
        rw [← mul_assoc, inv_mul_cancel₀ hdenom, one_mul]
    _ = (2 * π * Gamma a * Gamma b * Gamma (c - b))⁻¹ *
          (Gamma (c - b) * ∫ y : ℝ,
            Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
              (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I)) := hmul
    _ = (2 * π * Gamma a * Gamma b)⁻¹ *
          ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
            (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ (σ + y * I) := by
        rw [← mul_assoc, hcancel]

/-- **Mellin–Barnes representation of Euler's integral**
([DLMF 15.6.6](https://dlmf.nist.gov/15.6#E6)): for `Re b < Re c`, `-z ∈ Complex.slitPlane`,
and `-min(Re a, Re b) < σ < 0`,
`eulerIntegral a b c z = (2π Γ(a) Γ(b))⁻¹ ∫ Γ(a + σ + i y) Γ(b + σ + i y) Γ(-σ - i y)`
`  (Γ(c + σ + i y))⁻¹ (-z)^{σ + i y} dy`. -/
theorem eulerIntegral_eq_mellinBarnes {a b c z : ℂ} (hbc : b.re < c.re) (hz : -z ∈ slitPlane)
    {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    eulerIntegral a b c z = (2 * π * Gamma a * Gamma b)⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  have hb : 0 < b.re := by linarith
  have hf : AnalyticOnNhd ℂ (fun w : ℂ ↦ eulerIntegral a b c (-w)) slitPlane := by
    intro w hw
    have h1w : 1 - (-w) ∈ slitPlane := by
      simpa [sub_neg_eq_add] using TauCeti.ofReal_add_mem_slitPlane hw zero_le_one
    exact (analyticOnNhd_eulerIntegral hb hbc (a, -w) h1w).comp₂
      analyticAt_const analyticAt_id.neg
  have hg : AnalyticOnNhd ℂ (fun w : ℂ ↦ (2 * π * Gamma a * Gamma b)⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * w ^ (σ + y * I)) slitPlane :=
    ((differentiableOn_integral_mul_cpow_vertical le_rfl
      (continuous_mellinBarnes_neg_kernel a b c
        (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
        (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
        (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]))
      (fun _ hε ↦ exists_norm_mellinBarnes_neg_kernel_le a b c
        (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
        (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
        (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]) hε) σ).const_mul _).analyticOnNhd
      isOpen_slitPlane
  have heq := hf.eqOn_slitPlane_of_ofReal_pos_eq hg
    (fun x hx ↦ eulerIntegral_neg_ofReal_eq_mellinBarnes hbc hx hσ haσ hbσ) hz
  simpa only [neg_neg] using heq

/-! ### DLMF 15.6.7: convergence, holomorphy, and evaluation via Barnes's first lemma -/

private lemma continuous_mellinBarnes_one_sub_kernel (a b c : ℂ) {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hcσ : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) := by
  have hG1 : Continuous fun y : ℝ ↦ Gamma (a + (σ + y * I)) := by
    simpa only [add_assoc] using continuous_Gamma_add_mul_I (a := a + σ) (by simpa using haσ)
  have hG2 : Continuous fun y : ℝ ↦ Gamma (b + (σ + y * I)) := by
    simpa only [add_assoc] using continuous_Gamma_add_mul_I (a := b + σ) (by simpa using hbσ)
  have hG3 : Continuous fun y : ℝ ↦ Gamma (c - a - b - (σ + y * I)) := by
    simpa only [sub_add_eq_sub_sub] using
      continuous_Gamma_sub_mul_I (a := c - a - b - σ) (by simpa using hcσ)
  have hG4 : Continuous fun y : ℝ ↦ Gamma (-(σ + y * I)) := by
    simpa only [neg_add, ← sub_eq_add_neg] using
      continuous_Gamma_sub_mul_I (a := -(σ : ℂ)) (by simpa using hσ)
  exact ((hG1.mul hG2).mul hG3).mul hG4

private lemma exists_norm_mellinBarnes_one_sub_kernel_le (a b c : ℂ) {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hcσ : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
        C * Real.exp (-((2 * π - ε) * |y|)) := by
  have hε4 : 0 < ε / 4 := by positivity
  obtain ⟨C₁, hC₁, h₁⟩ :=
    TauCeti.exists_norm_Gamma_add_mul_I_le_exp_neg (a + σ) (by simpa using haσ) hε4
  obtain ⟨C₂, hC₂, h₂⟩ :=
    TauCeti.exists_norm_Gamma_add_mul_I_le_exp_neg (b + σ) (by simpa using hbσ) hε4
  obtain ⟨C₃, hC₃, h₃⟩ :=
    TauCeti.exists_norm_Gamma_sub_mul_I_le_exp_neg (c - a - b - σ) (by simpa using hcσ) hε4
  obtain ⟨C₄, _, h₄⟩ :=
    TauCeti.exists_norm_Gamma_sub_mul_I_le_exp_neg (-(σ : ℂ)) (by simpa using hσ) hε4
  refine ⟨C₁ * C₂ * C₃ * C₄, fun y ↦ ?_⟩
  have hb1 : ‖Gamma (a + (σ + y * I))‖ ≤ C₁ * Real.exp (-((π / 2 - ε / 4) * |y|)) := by
    simpa only [add_assoc] using h₁ y
  have hb2 : ‖Gamma (b + (σ + y * I))‖ ≤ C₂ * Real.exp (-((π / 2 - ε / 4) * |y|)) := by
    simpa only [add_assoc] using h₂ y
  have hb3 : ‖Gamma (c - a - b - (σ + y * I))‖ ≤ C₃ * Real.exp (-((π / 2 - ε / 4) * |y|)) := by
    simpa only [sub_add_eq_sub_sub] using h₃ y
  have hb4 : ‖Gamma (-(σ + y * I))‖ ≤ C₄ * Real.exp (-((π / 2 - ε / 4) * |y|)) := by
    have heq : -((σ : ℂ) + y * I) = -(σ : ℂ) - y * I := by ring
    simpa only [heq] using h₄ y
  simp only [norm_mul]
  calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ *
        ‖Gamma (c - a - b - (σ + y * I))‖ * ‖Gamma (-(σ + y * I))‖
      ≤ (C₁ * Real.exp (-((π / 2 - ε / 4) * |y|))) *
          (C₂ * Real.exp (-((π / 2 - ε / 4) * |y|))) *
          (C₃ * Real.exp (-((π / 2 - ε / 4) * |y|))) *
          (C₄ * Real.exp (-((π / 2 - ε / 4) * |y|))) := by gcongr
    _ = C₁ * C₂ * C₃ * C₄ *
          (Real.exp (-((π / 2 - ε / 4) * |y|)) * Real.exp (-((π / 2 - ε / 4) * |y|)) *
          Real.exp (-((π / 2 - ε / 4) * |y|)) * Real.exp (-((π / 2 - ε / 4) * |y|))) := by ring
    _ = C₁ * C₂ * C₃ * C₄ * Real.exp (-((2 * π - ε) * |y|)) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-- Integrability of the DLMF 15.6.7 Mellin–Barnes integrand on every pole-avoiding vertical line
`Re s = σ` for `1 - z ∈ Complex.slitPlane`. -/
theorem integrable_mellinBarnes_one_sub (a b c : ℂ) {z : ℂ} (hz : 1 - z ∈ slitPlane) {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hcσ : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) :=
  integrable_mul_cpow_vertical (by linarith [Real.pi_pos])
    (continuous_mellinBarnes_one_sub_kernel a b c haσ hbσ hcσ hσ)
    (fun _ hε ↦ exists_norm_mellinBarnes_one_sub_kernel_le a b c haσ hbσ hcσ hσ hε) hz σ

/-- Holomorphy of the DLMF 15.6.7 Mellin–Barnes integral in `z` on the cut plane
`{z | 1 - z ∈ Complex.slitPlane}`. -/
theorem differentiableOn_mellinBarnes_one_sub (a b c : ℂ) {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hcσ : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) :
    DifferentiableOn ℂ (fun z : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I))
      {z : ℂ | 1 - z ∈ slitPlane} :=
  (differentiableOn_integral_mul_cpow_vertical (by linarith [Real.pi_pos])
    (continuous_mellinBarnes_one_sub_kernel a b c haσ hbσ hcσ hσ)
    (fun _ hε ↦ exists_norm_mellinBarnes_one_sub_kernel_le a b c haσ hbσ hcσ hσ hε) σ).comp
    ((differentiable_const 1).sub differentiable_id).differentiableOn (fun _ hz ↦ hz)

/-- Termwise evaluation of the `n`-th binomial coefficient against the DLMF 15.6.7 kernel via
Barnes's first lemma. -/
private lemma integral_mellinBarnes_one_sub_term {a b c : ℂ} {σ : ℝ} (hσ : σ < 0)
    (hσc : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) (z : ℂ) (n : ℕ) :
    (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))) *
          (Ring.multichoose (-((σ : ℂ) + y * I)) n * z ^ n) =
      (regularizedGaussHGFunSeries a b c).coeff n * z ^ n := by
  have ha : 0 < a.re := by linarith
  have hb : 0 < b.re := by linarith
  have hca : 0 < (c - a).re := by
    have : (c - a).re = (c - a - b).re + b.re := by simp
    linarith
  have hcb : 0 < (c - b).re := by
    have : (c - b).re = (c - a - b).re + a.re := by simp; ring
    linarith
  have ha_ne : ∀ k : ℕ, a ≠ -k := fun k hk ↦ by
    have := congrArg re hk; simp at this; linarith [k.cast_nonneg' (α := ℝ)]
  have hb_ne : ∀ k : ℕ, b ≠ -k := fun k hk ↦ by
    have := congrArg re hk; simp at this; linarith [k.cast_nonneg' (α := ℝ)]
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hΓca : Gamma (c - a) ≠ 0 := Gamma_ne_zero_of_re_pos hca
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hFn (y : ℝ) :
      (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))) *
        (Ring.multichoose (-((σ : ℂ) + y * I)) n * z ^ n) =
      (z ^ n / (n ! : ℂ)) *
        (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma ((n : ℂ) - (σ + y * I))) := by
    have hmc : Ring.multichoose (-((σ : ℂ) + y * I)) n =
        (ascPochhammer ℂ n).eval (-((σ : ℂ) + y * I)) / (n ! : ℂ) := by
      rw [eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), mul_comm, ← nsmul_eq_mul,
        Ring.factorial_nsmul_multichoose_eq_ascPochhammer, Polynomial.ascPochhammer_smeval_eq_eval]
    rw [hmc]
    have ht_ne : ∀ k : ℕ, -((σ : ℂ) + y * I) ≠ -k := fun k hk ↦ by
      have hre := congrArg re hk; simp at hre; linarith [k.cast_nonneg' (α := ℝ)]
    have hΓt : Gamma (-((σ : ℂ) + y * I)) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
    have hmul : Gamma (-((σ : ℂ) + y * I)) * (ascPochhammer ℂ n).eval (-((σ : ℂ) + y * I)) =
        Gamma ((n : ℂ) - (σ + y * I)) := by
      rw [← Gamma_add_nat_div_Gamma_eq (n := n) (-((σ : ℂ) + y * I)) ht_ne,
        mul_div_cancel₀ _ hΓt]
      congr 1; ring
    calc Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-((σ : ℂ) + y * I)) *
          ((ascPochhammer ℂ n).eval (-((σ : ℂ) + y * I)) / (n ! : ℂ) * z ^ n)
        = (z ^ n / (n ! : ℂ)) * (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
            Gamma (c - a - b - (σ + y * I)) *
            (Gamma (-((σ : ℂ) + y * I)) * (ascPochhammer ℂ n).eval (-((σ : ℂ) + y * I)))) := by
          ring
      _ = _ := by rw [hmul]
  simp_rw [hFn, integral_const_mul]
  have hbarnes := integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub
    (a := a) (b := b) (c := c - a - b) (d := (n : ℂ))
    haσ hbσ hσc (by simp; linarith [n.cast_nonneg' (α := ℝ)])
  have h1 : a + (c - a - b) = c - b := by ring
  have h2 : b + (c - a - b) = c - a := by ring
  have h3 : a + b + (c - a - b) + (n : ℂ) = c + n := by ring
  rw [h1, h2, h3] at hbarnes
  have hpull : (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ((z ^ n / (n ! : ℂ)) * ∫ y : ℝ,
          Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
            Gamma (c - a - b - (σ + y * I)) * Gamma ((n : ℂ) - (σ + y * I))) =
      (Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ * (z ^ n / (n ! : ℂ)) *
        ((2 * π : ℂ)⁻¹ * ∫ y : ℝ,
          Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
            Gamma (c - a - b - (σ + y * I)) * Gamma ((n : ℂ) - (σ + y * I))) := by
    simp only [mul_inv_rev]; ring
  rw [hpull, hbarnes, coeff_regularizedGaussHGFunSeries,
    ← Gamma_add_nat_div_Gamma_eq a ha_ne, ← Gamma_add_nat_div_Gamma_eq b hb_ne]
  field_simp [hΓa, hΓb, hΓca, hΓcb]

/-- DLMF 15.6.7 on the disk `‖z‖ < 1 / 2`, proved by termwise integration of the binomial
series of `(1 - z)^{σ + i y}` via dominated convergence and Barnes's first lemma. -/
private lemma regularizedGaussHGFun_eq_mellinBarnes_one_sub_of_norm_lt_half {a b c z : ℂ}
    (hz : ‖z‖ < 1 / 2) {σ : ℝ} (hσ : σ < 0) (hσc : σ < (c - a - b).re) (haσ : -a.re < σ)
    (hbσ : -b.re < σ) :
    regularizedGaussHGFun a b c z =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) := by
  have hz1 : ‖z‖ < 1 := by linarith
  have haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hbσ_ne : ∀ n : ℕ, b.re + σ ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hcσ_ne : ∀ n : ℕ, (c - a - b).re - σ ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hσ_ne : ∀ n : ℕ, -σ ≠ -n := fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hmcC (t : ℂ) (n : ℕ) : Ring.multichoose t n = (ascPochhammer ℂ n).eval t / (n ! : ℂ) := by
    rw [eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), mul_comm, ← nsmul_eq_mul,
      Ring.factorial_nsmul_multichoose_eq_ascPochhammer, Polynomial.ascPochhammer_smeval_eq_eval]
  have hmcR (x : ℝ) (n : ℕ) : Ring.multichoose x n = (ascPochhammer ℝ n).eval x / (n ! : ℝ) := by
    rw [eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), mul_comm, ← nsmul_eq_mul,
      Ring.factorial_nsmul_multichoose_eq_ascPochhammer, Polynomial.ascPochhammer_smeval_eq_eval]
  let g : ℝ → ℂ := fun y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))
  let F : ℕ → ℝ → ℂ := fun n y ↦ g y * (Ring.multichoose (-((σ : ℂ) + y * I)) n * z ^ n)
  let bound : ℕ → ℝ → ℝ := fun n y ↦ ‖g y‖ * (Ring.multichoose ‖(σ : ℂ) + y * I‖ n * ‖z‖ ^ n)
  have hg_cont : Continuous g :=
    continuous_mellinBarnes_one_sub_kernel a b c haσ_ne hbσ_ne hcσ_ne hσ_ne
  have hF_meas : ∀ n : ℕ, AEStronglyMeasurable (F n) volume := by
    intro n
    have hcoeff : Continuous fun y : ℝ ↦ Ring.multichoose (-((σ : ℂ) + y * I)) n := by
      simp_rw [hmcC]
      exact ((Polynomial.continuous (ascPochhammer ℂ n)).comp (by fun_prop)).div_const _
    exact (hg_cont.mul (hcoeff.mul continuous_const)).aestronglyMeasurable
  -- Majorize each binomial term by replacing `-((σ : ℂ) + y * I)` with its norm.
  have h_bound : ∀ n : ℕ, ∀ᵐ y ∂volume, ‖F n y‖ ≤ bound n y := by
    have hpoch (t : ℂ) (n : ℕ) : ‖(ascPochhammer ℂ n).eval t‖ ≤ (ascPochhammer ℝ n).eval ‖t‖ := by
      induction n with
      | zero => simp
      | succ n ih =>
        simp only [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_natCast, norm_mul]
        have hfac : ‖t + (n : ℂ)‖ ≤ ‖t‖ + (n : ℝ) := by
          calc ‖t + (n : ℂ)‖ ≤ ‖t‖ + ‖(n : ℂ)‖ := norm_add_le _ _
            _ = ‖t‖ + (n : ℝ) := by simp
        exact mul_le_mul ih hfac (norm_nonneg _) ((norm_nonneg _).trans ih)
    intro n
    refine .of_forall fun y ↦ ?_
    simp only [F, bound, norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by positivity)) (norm_nonneg _)
    rw [hmcC, hmcR, norm_div, Complex.norm_natCast]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    simpa only [norm_neg] using hpoch (-((σ : ℂ) + y * I)) n
  have hreal_hasSum (y : ℝ) :
      HasSum (fun n : ℕ ↦ Ring.multichoose ‖(σ : ℂ) + y * I‖ n * ‖z‖ ^ n)
        (1 / (1 - ‖z‖) ^ ‖(σ : ℂ) + y * I‖) :=
    TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (by simpa using hz1)
  have hbound_sum : ∀ᵐ y ∂volume, Summable fun n : ℕ ↦ bound n y :=
    .of_forall fun y ↦ (hreal_hasSum y).summable.mul_left ‖g y‖
  -- Integrability of the majorant `‖g y‖ * (1 - ‖z‖)^{-‖σ + i y‖}` for `‖z‖ < 1 / 2`.
  have hbound_int : Integrable (fun y : ℝ ↦ ∑' n : ℕ, bound n y) volume := by
    have hsum_eq (y : ℝ) : ∑' n : ℕ, bound n y = ‖g y‖ * (1 / (1 - ‖z‖) ^ ‖(σ : ℂ) + y * I‖) := by
      simp only [bound, tsum_mul_left, (hreal_hasSum y).tsum_eq]
    simp_rw [hsum_eq]
    have h1z_pos : 0 < 1 - ‖z‖ := by linarith
    have h1z_half : (1 / 2 : ℝ) < 1 - ‖z‖ := by linarith
    obtain ⟨C, hgb⟩ := exists_norm_mellinBarnes_one_sub_kernel_le a b c haσ_ne hbσ_ne hcσ_ne
      hσ_ne (ε := 2) (by norm_num)
    have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hgb 0)
    have hrate : 0 < 2 * π - 3 := by linarith [Real.pi_gt_three]
    set K : ℝ := C * Real.exp |σ|
    have hcont_b : Continuous fun y : ℝ ↦ ‖g y‖ * (1 / (1 - ‖z‖) ^ ‖(σ : ℂ) + y * I‖) := by
      refine hg_cont.norm.mul (continuous_const.div ?_ fun y ↦ (Real.rpow_pos_of_pos h1z_pos _).ne')
      exact continuous_const.rpow (by fun_prop) fun _ ↦ Or.inl h1z_pos.ne'
    refine ((TauCeti.integrable_exp_neg_mul_abs hrate).const_mul K).mono'
      hcont_b.aestronglyMeasurable (.of_forall fun y ↦ ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity))]
    have hpow_b : 1 / (1 - ‖z‖) ^ ‖(σ : ℂ) + y * I‖ ≤ Real.exp |σ| * Real.exp |y| := by
      rw [one_div, ← Real.rpow_neg h1z_pos.le, Real.rpow_def_of_pos h1z_pos, ← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have hlog : -Real.log (1 - ‖z‖) ≤ 1 := by
        have hlt : Real.log (1 / 2) < Real.log (1 - ‖z‖) :=
          Real.log_lt_log (by norm_num) h1z_half
        rw [one_div, Real.log_inv] at hlt
        have hlog2 : Real.log 2 < 1 := by
          rw [Real.log_lt_iff_lt_exp (by norm_num)]
          linarith [Real.exp_one_gt_d9]
        linarith
      have hnorm : ‖(σ : ℂ) + y * I‖ ≤ |σ| + |y| := by
        calc ‖(σ : ℂ) + y * I‖ ≤ ‖(σ : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
          _ = |σ| + |y| := by simp
      nlinarith [norm_nonneg ((σ : ℂ) + y * I)]
    calc ‖g y‖ * (1 / (1 - ‖z‖) ^ ‖(σ : ℂ) + y * I‖)
        ≤ (C * Real.exp (-((2 * π - 2) * |y|))) * (Real.exp |σ| * Real.exp |y|) := by
          gcongr; exact hgb y
      _ = K * (Real.exp (-((2 * π - 2) * |y|)) * Real.exp |y|) := by simp only [K]; ring
      _ = K * Real.exp (-((2 * π - 3) * |y|)) := by
          rw [← Real.exp_add]; congr 2; ring
  have h_lim : ∀ᵐ y ∂volume, HasSum (fun n : ℕ ↦ F n y) (g y * (1 - z) ^ ((σ : ℂ) + y * I)) := by
    refine .of_forall fun y ↦ ?_
    have h := TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one
      (r := -((σ : ℂ) + y * I)) hz1
    rw [one_div, cpow_neg, inv_inv] at h
    exact h.mul_left (g y)
  have hdom := hasSum_integral_of_dominated_convergence bound hF_meas h_bound hbound_sum hbound_int
    h_lim
  have hsum_mb : HasSum (fun n ↦ (regularizedGaussHGFunSeries a b c).coeff n * z ^ n)
      ((2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, g y * (1 - z) ^ ((σ : ℂ) + y * I)) := by
    simpa only [F, g, integral_mellinBarnes_one_sub_term hσ hσc haσ hbσ z] using hdom.mul_left
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹
  have hsum_hg : HasSum (fun n ↦ (regularizedGaussHGFunSeries a b c).coeff n * z ^ n)
      (regularizedGaussHGFun a b c z) := by
    have hr : z ∈ Metric.eball 0 (regularizedGaussHGFunSeries a b c).radius := by
      rw [Metric.mem_eball, edist_zero_right]
      exact lt_of_lt_of_le (by rw [← ofReal_norm, ENNReal.ofReal_lt_one]; exact hz1)
        (radius_regularizedGaussHGFunSeries_ge_one a b c)
    simpa [regularizedGaussHGFun, regularizedGaussHGFunSeries, regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
      (regularizedGaussHGFunSeries a b c).hasSum hr
  exact hsum_hg.unique hsum_mb

/-- **Mellin–Barnes representation in `1 - z`**
([DLMF 15.6.7](https://dlmf.nist.gov/15.6#E7)) on the open unit disk `‖z‖ < 1`: whenever
`-min(Re a, Re b) < σ < min(0, Re (c - a - b))`,
`regularizedGaussHGFun a b c z = (2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫ Γ(a + σ + i y)`
`  Γ(b + σ + i y) Γ(c - a - b - σ - i y) Γ(-σ - i y) (1 - z)^{σ + i y} dy`. -/
theorem regularizedGaussHGFun_eq_mellinBarnes_one_sub {a b c z : ℂ} (hz : ‖z‖ < 1)
    {σ : ℝ} (hσ : σ < 0) (hσc : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    regularizedGaussHGFun a b c z =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) := by
  have hball_sub : Metric.ball (0 : ℂ) 1 ⊆ {w : ℂ | 1 - w ∈ slitPlane} := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    simpa [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one (z := -w) (by simpa using hw)
  have hf : AnalyticOnNhd ℂ (regularizedGaussHGFun a b c) (Metric.ball (0 : ℂ) 1) := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact analyticAt_regularizedHGFun_of_card_eq_add_one (a := {a, b}) (b := {c}) rfl hw
  have hg : AnalyticOnNhd ℂ (fun w : ℂ ↦
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - w) ^ (σ + y * I))
      (Metric.ball (0 : ℂ) 1) := by
    have hopen : IsOpen {w : ℂ | 1 - w ∈ slitPlane} :=
      isOpen_slitPlane.preimage (continuous_const.sub continuous_id)
    have hdiff := (differentiableOn_mellinBarnes_one_sub a b c (σ := σ)
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])
      (fun n h ↦ by linarith [n.cast_nonneg' (α := ℝ)])).const_mul
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹
    exact (hdiff.analyticOnNhd hopen).mono hball_sub
  have hev : regularizedGaussHGFun a b c =ᶠ[𝓝 (0 : ℂ)] fun w : ℂ ↦
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - w) ^ (σ + y * I) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact regularizedGaussHGFun_eq_mellinBarnes_one_sub_of_norm_lt_half hw hσ hσc haσ hbσ
  exact hf.eqOn_of_preconnected_of_eventuallyEq hg (convex_ball (0 : ℂ) 1).isPreconnected
    (Metric.mem_ball_self one_pos) hev (by simpa [Metric.mem_ball] using hz)

end Complex
