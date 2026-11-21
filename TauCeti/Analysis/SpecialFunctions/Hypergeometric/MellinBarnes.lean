/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.RingTheory.Binomial

/-!
# Mellin–Barnes integrals for the Gauss hypergeometric function (DLMF 15.6.7)

This file formalizes the Mellin–Barnes vertical-line integral representation **DLMF 15.6.7** in
powers of `1 - z` for the Gauss hypergeometric family:
`(2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫ Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s) (1 - z)^s dy`,
where `s = σ + i y` and `max (-Re a, -Re b) < σ < min (0, Re (c - a - b))`.
(For DLMF 15.6.6 in powers of `-z` and its separating-contour continuation, see
`TauCeti.Analysis.SpecialFunctions.Hypergeometric.SeparatingContour.Continuation`.)

On any pole-free line `Re s = σ`, Stirling's vertical-strip bounds give
`O((1 + |y|)^K exp (-2π |y|))` decay for the four-Gamma product in 15.6.7 at fixed `(a, b, c)`.
Combined with `|arg (1 - z)| ≤ π` (and `|arg (1 - z)| < π` on `{z | 1 - z ∈ Complex.slitPlane}`),
this yields integrability for every `z : ℂ` and holomorphy on `{z | 1 - z ∈ Complex.slitPlane}`.

Expanding `(1 - z)^s` in its binomial series on `‖z‖ < 1 / 2` (where the summed series majorant
grows at exponential rate `log 2 < 2π`, so its product with `exp (-2π |y|)` decays at rate
`2π - log 2 > 0`) and integrating term by term via Barnes's first lemma
(`Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`) recovers
`Complex.regularizedGaussHGFun`; analyticity on the open unit disk extends the identity to all
`‖z‖ < 1`.

## Main results

* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow`,
  `Complex.analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow`:
  convergence (for all `z : ℂ`) and `z`-holomorphy (on `{z | 1 - z ∈ slitPlane}`) of the
  Mellin–Barnes integral 15.6.7.
* `Complex.regularizedGaussHGFun_eq_mellinBarnes_one_sub`,
  `Complex.ordinaryHypergeometric_eq_mellinBarnes_one_sub`: equality of the regularized and
  ordinary Gauss series with the Mellin–Barnes integral 15.6.7 on the open unit disk `‖z‖ < 1`.

## References

* NIST Digital Library of Mathematical Functions, §15.6, equation
  [15.6.7](https://dlmf.nist.gov/15.6.E7).
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §§14.5–14.51.
* G. E. Andrews, R. Askey, and R. Roy, *Special Functions*, §2.4.
-/

public section

noncomputable section

open Complex Filter MeasureTheory Metric Real Set
open scoped Nat Topology

namespace Complex

/-! ### DLMF 15.6.6: Mellin–Barnes representation in powers of `-z` -/

/-- Three-Gamma decay estimate for the fixed factors of 15.6.6: on any pole-free vertical line
`Re s = σ`, `‖Γ(a + s) Γ(b + s) Γ(-s)‖ ≤ C (1 + |y|) ^ K exp (-3π |y| / 2)`. -/
private theorem exists_norm_three_Gamma_le {a b : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    ∃ C > 0, ∃ K : ℝ, ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(3 * π * |y| / 2)) := by
  obtain ⟨Ca, hCa, hba⟩ := TauCeti.exists_norm_Gamma_add_I_le (w := a + σ) (by simpa using ha)
  obtain ⟨Cb, hCb, hbb⟩ := TauCeti.exists_norm_Gamma_add_I_le (w := b + σ) (by simpa using hb)
  obtain ⟨Cs, hCs, hbs⟩ := TauCeti.exists_norm_Gamma_sub_I_le (w := -σ)
    (fun n hn ↦ hσ n (by simp at hn; linarith))
  set Ka : ℝ := (a + σ).re - 1 / 2
  set Kb : ℝ := (b + σ).re - 1 / 2
  set Ks : ℝ := (-σ : ℂ).re - 1 / 2
  refine ⟨Ca * Cb * Cs, by positivity, Ka + Kb + Ks, fun y ↦ ?_⟩
  have h1 : ‖Gamma (a + (σ + y * I))‖ ≤
      Ca * (1 + |y|) ^ Ka * Real.exp (-(π * |y| / 2)) := by
    simpa only [← add_assoc] using hba y
  have h2 : ‖Gamma (b + (σ + y * I))‖ ≤
      Cb * (1 + |y|) ^ Kb * Real.exp (-(π * |y| / 2)) := by
    simpa only [← add_assoc] using hbb y
  have h3 : ‖Gamma (-((σ : ℂ) + y * I))‖ ≤
      Cs * (1 + |y|) ^ Ks * Real.exp (-(π * |y| / 2)) := by
    rw [neg_add']
    exact hbs y
  rw [norm_mul, norm_mul]
  calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ * ‖Gamma (-((σ : ℂ) + y * I))‖
      ≤ (Ca * (1 + |y|) ^ Ka * Real.exp (-(π * |y| / 2))) *
          (Cb * (1 + |y|) ^ Kb * Real.exp (-(π * |y| / 2))) *
          (Cs * (1 + |y|) ^ Ks * Real.exp (-(π * |y| / 2))) :=
        mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h3
          (norm_nonneg _) (by positivity)
    _ = Ca * Cb * Cs * ((1 + |y|) ^ Ka * (1 + |y|) ^ Kb * (1 + |y|) ^ Ks) *
          (Real.exp (-(π * |y| / 2)) * Real.exp (-(π * |y| / 2)) *
            Real.exp (-(π * |y| / 2))) := by ring
    _ = Ca * Cb * Cs * (1 + |y|) ^ (Ka + Kb + Ks) * Real.exp (-(3 * π * |y| / 2)) := by
        rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity),
          ← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-- Continuity in `y` of the three-Gamma factor `Γ(a + s) Γ(b + s) Γ(-s)` in DLMF 15.6.6. -/
private theorem continuous_three_Gamma {a b : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) := by
  have hGa : Continuous fun y : ℝ ↦ Gamma (a + (σ + y * I)) := by
    simpa only [← add_assoc] using continuous_Gamma_add_mul_I (w := a + σ) (by simpa using ha)
  have hGb : Continuous fun y : ℝ ↦ Gamma (b + (σ + y * I)) := by
    simpa only [← add_assoc] using continuous_Gamma_add_mul_I (w := b + σ) (by simpa using hb)
  have hGs : Continuous fun y : ℝ ↦ Gamma (-(σ + y * I)) := by
    convert continuous_Gamma_sub_mul_I (w := -σ) (fun n hn ↦ hσ n (by simp at hn; linarith))
      using 3 with y
    ring
  exact (hGa.mul hGb).mul hGs

/-! ### DLMF 15.6.7: Mellin–Barnes representation in powers of `1 - z` -/

/-- Four-Gamma decay estimate for the fixed factors of 15.6.7: on any pole-free vertical line
`Re s = σ`, `‖Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s)‖ ≤ C (1 + |y|) ^ K exp (-2π |y|)`. -/
private theorem exists_norm_four_Gamma_le {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    ∃ C > 0, ∃ K : ℝ, ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(2 * π * |y|)) := by
  obtain ⟨C₃, hC₃, K₃, hb₃⟩ := exists_norm_three_Gamma_le ha hb hσ
  obtain ⟨Cc, hCc, hbc⟩ :=
    TauCeti.exists_norm_Gamma_sub_I_le (w := c - a - b - σ) (by simpa using hc)
  set Kc : ℝ := (c - a - b - σ).re - 1 / 2
  refine ⟨C₃ * Cc, by positivity, K₃ + Kc, fun y ↦ ?_⟩
  have h1 := hb₃ y
  have h2 : ‖Gamma (c - a - b - (σ + y * I))‖ ≤
      Cc * (1 + |y|) ^ Kc * Real.exp (-(π * |y| / 2)) := by
    simpa only [sub_add_eq_sub_sub] using hbc y
  have hrew : ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ =
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
        ‖Gamma (c - a - b - (σ + y * I))‖ := by
    simp only [norm_mul]; ring
  rw [hrew]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          ‖Gamma (c - a - b - (σ + y * I))‖
      ≤ (C₃ * (1 + |y|) ^ K₃ * Real.exp (-(3 * π * |y| / 2))) *
          (Cc * (1 + |y|) ^ Kc * Real.exp (-(π * |y| / 2))) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = C₃ * Cc * ((1 + |y|) ^ K₃ * (1 + |y|) ^ Kc) *
          (Real.exp (-(3 * π * |y| / 2)) * Real.exp (-(π * |y| / 2))) := by ring
    _ = C₃ * Cc * (1 + |y|) ^ (K₃ + Kc) * Real.exp (-(2 * π * |y|)) := by
        rw [← Real.rpow_add (by positivity), ← Real.exp_add]
        congr 2; ring

/-- Continuity in `y` of the four-Gamma factor in DLMF 15.6.7. -/
private theorem continuous_four_Gamma {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) := by
  have hGc : Continuous fun y : ℝ ↦ Gamma (c - a - b - (σ + y * I)) := by
    simpa only [sub_add_eq_sub_sub] using
      continuous_Gamma_sub_mul_I (w := c - a - b - σ) (by simpa using hc)
  have heq : (fun y : ℝ ↦ Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))) =
      fun y : ℝ ↦ (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))) *
        Gamma (c - a - b - (σ + y * I)) :=
    funext fun _ ↦ by ring
  exact heq ▸ (continuous_three_Gamma ha hb hσ).mul hGc

/-- On every vertical line `Re s = σ` avoiding the poles of all four Gamma factors, the
Mellin–Barnes integrand of DLMF 15.6.7 is integrable on `ℝ` for every `z : ℂ` (since
`|arg (1 - z)| ≤ π` leaves at least `exp (-π |y|)` decay against the four-Gamma `exp (-2π |y|)`
factor). -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow {a b c : ℂ} (z : ℂ)
    {σ : ℝ} (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
        (1 - z) ^ ((σ : ℂ) + y * I) := by
  obtain ⟨Cg, hCg, Kg, hbg⟩ := exists_norm_four_Gamma_le ha hb hc hσ
  have hpow_cont : Continuous fun y : ℝ ↦ (1 - z) ^ ((σ : ℂ) + y * I) :=
    Continuous.const_cpow (by fun_prop) <| Or.inr fun y h0 ↦
      hσ 0 (by simpa using congrArg re h0)
  refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs Kg Real.pi_pos).const_mul
    (Cg * ‖1 - z‖ ^ σ)).mono'
    ((continuous_four_Gamma ha hb hc hσ).mul hpow_cont).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  have hpow : ‖(1 - z) ^ ((σ : ℂ) + y * I)‖ ≤ ‖1 - z‖ ^ σ * Real.exp (π * |y|) := by
    calc ‖(1 - z) ^ ((σ : ℂ) + y * I)‖
        ≤ ‖1 - z‖ ^ ((σ : ℂ) + y * I).re *
            (Real.exp ((1 - z).arg * ((σ : ℂ) + y * I).im))⁻¹ := by
          simpa only [div_eq_mul_inv] using norm_cpow_le (1 - z) ((σ : ℂ) + y * I)
      _ ≤ ‖1 - z‖ ^ σ * Real.exp (π * |y|) := by
          simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, add_im,
            mul_I_im, zero_add]
          exact mul_le_mul_of_nonneg_left (inv_exp_arg_mul_le_exp_pi_mul_abs (1 - z) y)
            (Real.rpow_nonneg (norm_nonneg _) σ)
  rw [norm_mul]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          ‖(1 - z) ^ ((σ : ℂ) + y * I)‖
      ≤ (Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|))) *
          (‖1 - z‖ ^ σ * Real.exp (π * |y|)) :=
        mul_le_mul (hbg y) hpow (norm_nonneg _) (by positivity)
    _ = Cg * ‖1 - z‖ ^ σ * ((1 + |y|) ^ Kg *
          (Real.exp (-(2 * π * |y|)) * Real.exp (π * |y|))) := by ring
    _ = Cg * ‖1 - z‖ ^ σ * ((1 + |y|) ^ Kg * Real.exp (-(π * |y|))) := by
        rw [← Real.exp_add]; ring_nf

/-- On every vertical line `Re s = σ` avoiding the poles of all four Gamma factors, the
Mellin–Barnes integral of DLMF 15.6.7 is holomorphic on `{z | 1 - z ∈ slitPlane}`. -/
theorem analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow {a b c : ℂ}
    {σ : ℝ} (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    AnalyticOnNhd ℂ
      (fun z : ℂ ↦ ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - z) ^ ((σ : ℂ) + y * I))
      {z | 1 - z ∈ slitPlane} := by
  have hopen : IsOpen {z : ℂ | 1 - z ∈ slitPlane} :=
    isOpen_slitPlane.preimage (continuous_const.sub continuous_id)
  refine DifferentiableOn.analyticOnNhd (fun z₀ hz₀ ↦ ?_) hopen
  let G : ℝ → ℂ := fun y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))
  let F : ℂ → ℝ → ℂ := fun z y ↦ G y * (1 - z) ^ ((σ : ℂ) + y * I)
  let F' : ℂ → ℝ → ℂ := fun z y ↦
    -(G y * (((σ : ℂ) + y * I) * (1 - z) ^ ((σ : ℂ) + y * I - 1)))
  -- Preimage ball around `z₀` inside `{z | 1 - z ∈ slitPlane}`.
  obtain ⟨Cg, hCg, Kg, hbg⟩ := exists_norm_four_Gamma_le ha hb hc hσ
  obtain ⟨ε, hε, θ, hθ, M, _hM, hball⟩ := TauCeti.exists_ball_slitPlane_cpow_le hz₀ σ
  let U : Set ℂ := (fun z : ℂ ↦ 1 - z) ⁻¹' ball (1 - z₀) ε
  have hU_nhds : U ∈ 𝓝 z₀ :=
    (continuous_const.sub continuous_id).continuousAt.eventually (ball_mem_nhds (1 - z₀) hε)
  -- Dominated differentiation under the integral sign.
  have hF_meas : ∀ᶠ z in 𝓝 z₀, AEStronglyMeasurable (F z) volume := by
    filter_upwards [hU_nhds] with z hz
    exact ((continuous_four_Gamma ha hb hc hσ).mul
      (continuous_const.cpow (by fun_prop) (fun _ ↦ (hball _ hz).1))).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' z₀) volume := by
    refine Continuous.aestronglyMeasurable ?_
    exact ((continuous_four_Gamma ha hb hc hσ).mul
      ((by fun_prop : Continuous fun y : ℝ ↦ (σ : ℂ) + y * I).mul
        (continuous_const.cpow (by fun_prop) (fun _ ↦ hz₀)))).neg
  have h_diff : ∀ᵐ y : ℝ, ∀ z ∈ U, HasDerivAt (F · y) (F' z y) z := by
    refine Eventually.of_forall fun y z hz ↦ ?_
    exact ((((hasDerivAt_id' z).const_sub 1).cpow_const (c := (σ : ℂ) + y * I)
      (hball (1 - z) hz).1).const_mul (G y)).congr_deriv (by dsimp [F']; ring)
  have h2pi_sub : 0 < 2 * π - θ := by linarith [Real.pi_pos]
  have h_bound : ∀ᵐ y : ℝ, ∀ z ∈ U,
      ‖F' z y‖ ≤ Cg * M * ((1 + |y|) ^ (Kg + 1) * Real.exp (-((2 * π - θ) * |y|))) := by
    refine Eventually.of_forall fun y z hz ↦ ?_
    obtain ⟨-, -, hpow1⟩ := hball (1 - z) hz
    rw [norm_neg, norm_mul]
    calc ‖G y‖ * ‖((σ : ℂ) + y * I) * (1 - z) ^ ((σ : ℂ) + y * I - 1)‖
        ≤ (Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|))) *
            (M * (1 + |y|) * Real.exp (θ * |y|)) :=
          mul_le_mul (hbg y) (hpow1 y) (norm_nonneg _) (by positivity)
      _ = Cg * M * ((1 + |y|) ^ Kg * (1 + |y|) ^ (1 : ℝ)) *
            (Real.exp (-(2 * π * |y|)) * Real.exp (θ * |y|)) := by
          rw [Real.rpow_one]; ring
      _ = Cg * M * ((1 + |y|) ^ (Kg + 1) * Real.exp (-((2 * π - θ) * |y|))) := by
          rw [← Real.rpow_add (by positivity), ← Real.exp_add]; ring_nf
  have h_dom_int := (TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (Kg + 1)
    h2pi_sub).const_mul (Cg * M)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le hU_nhds hF_meas
    (integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow z₀ ha hb hc hσ)
    hF'_meas h_bound h_dom_int h_diff).2.differentiableAt.differentiableWithinAt

/-- Single-term Barnes evaluation: integrating `Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s)` against
`multichoose (-s) n * z ^ n` along `Re s = σ` recovers the `n`-th term of the regularized Gauss
power series. -/
private theorem integral_four_Gamma_mul_multichoose (a b c z : ℂ) {σ : ℝ} (hσ : σ < 0)
    (hσc : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) (n : ℕ) :
    (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
      (∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Ring.multichoose (-((σ : ℂ) + y * I)) n * z ^ n)) =
      (regularizedGaussHGFunSeries a b c).coeff n * z ^ n := by
  have ha_pos : 0 < a.re := by linarith
  have hb_pos : 0 < b.re := by linarith
  have hca_pos : 0 < (c - a).re := by simp at hσc ⊢; linarith
  have hcb_pos : 0 < (c - b).re := by simp at hσc ⊢; linarith
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha_pos
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb_pos
  have hΓca : Gamma (c - a) ≠ 0 := Gamma_ne_zero_of_re_pos hca_pos
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb_pos
  have h2pi : (2 * π : ℂ) ≠ 0 := by norm_num [Real.pi_ne_zero]
  have hfac : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  -- Absorb `multichoose (-s) n` into `Γ(-s)` to form `Γ(n - s) / n!`.
  have hFn (y : ℝ) :
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (Ring.multichoose (-((σ : ℂ) + y * I)) n * z ^ n) =
        (z ^ n / (n ! : ℂ)) *
          (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
            Gamma (c - a - b - (σ + y * I)) * Gamma ((n : ℂ) - (σ + y * I))) := by
    set s : ℂ := (σ : ℂ) + y * I
    have hs_ne : ∀ k : ℕ, -s ≠ -k := fun k hk ↦ by
      have hre := congrArg re hk; simp [s] at hre; linarith [k.cast_nonneg' (α := ℝ)]
    have hGs : Gamma (-s) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [s]; linarith)
    have hmc : Gamma (-s) * Ring.multichoose (-s) n = Gamma ((n : ℂ) - s) / (n ! : ℂ) := by
      rw [TauCeti.Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer,
        ← Gamma_add_nat_div_Gamma_eq (-s) hs_ne, neg_add_eq_sub]
      field_simp [hGs, hfac]
    calc Gamma (a + s) * Gamma (b + s) * Gamma (c - a - b - s) * Gamma (-s) *
            (Ring.multichoose (-s) n * z ^ n)
        = (Gamma (a + s) * Gamma (b + s) * Gamma (c - a - b - s)) *
            (Gamma (-s) * Ring.multichoose (-s) n) * z ^ n := by ring
      _ = (z ^ n / (n ! : ℂ)) *
            (Gamma (a + s) * Gamma (b + s) * Gamma (c - a - b - s) * Gamma ((n : ℂ) - s)) := by
            rw [hmc]; ring
  simp_rw [hFn]
  rw [integral_const_mul]
  -- Evaluate the shifted four-Gamma integral by Barnes's first lemma.
  have hbarnes := integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub (a := a) (b := b)
    (c := c - a - b) (d := (n : ℂ)) haσ hbσ hσc (by simp; linarith [n.cast_nonneg' (α := ℝ)])
  have hb' := congrArg ((2 * π : ℂ) * ·) hbarnes
  simp only [← mul_assoc, mul_inv_cancel₀ h2pi, one_mul] at hb'
  have hac : a + (c - a - b) = c - b := by ring
  have hbc : b + (c - a - b) = c - a := by ring
  have habc : a + b + (c - a - b) + (n : ℂ) = c + n := by ring
  rw [hac, hbc, habc] at hb'
  rw [hb', coeff_regularizedGaussHGFunSeries,
    ← Gamma_add_nat_div_Gamma_eq a (fun k hk ↦ by
      have hre := congrArg re hk; simp at hre; linarith [k.cast_nonneg' (α := ℝ)]),
    ← Gamma_add_nat_div_Gamma_eq b (fun k hk ↦ by
      have hre := congrArg re hk; simp at hre; linarith [k.cast_nonneg' (α := ℝ)])]
  field_simp [h2pi, hΓa, hΓb, hΓca, hΓcb, hfac]

/-- Integrability on `ℝ` of the summed binomial-series majorant on `‖z‖ < 1 / 2`, where
`(1 - ‖z‖)^{-(|σ| + |y|)} ≤ 2 ^ |σ| exp ((log 2) |y|)` grows at exponential rate `log 2 < 2π`, so
its product with `exp (-2π |y|)` decays at rate `2π - log 2 > 0`. -/
private theorem integrable_tsum_multichoose_bound {Cg : ℝ} (hCg : 0 < Cg) (Kg σ : ℝ) {z : ℂ}
    (hz : ‖z‖ < 1 / 2) :
    Integrable fun y : ℝ ↦ ∑' n : ℕ,
      Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|)) *
        (Ring.multichoose (|σ| + |y|) n * ‖z‖ ^ n) := by
  -- Sum the positive geometric-multichoose series in closed form.
  have hz1 : |‖z‖| < 1 := by rw [abs_norm]; linarith
  have h_sum (y : ℝ) :
      HasSum (fun n : ℕ ↦ Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|)) *
          (Ring.multichoose (|σ| + |y|) n * ‖z‖ ^ n))
        (Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|)) *
          (1 / (1 - ‖z‖) ^ (|σ| + |y|))) :=
    (TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (r := |σ| + |y|) hz1).mul_left _
  have hrate : 0 < 2 * π - Real.log 2 := by
    have hlog2 : Real.log 2 ≤ 1 := by linarith [Real.log_le_sub_one_of_pos zero_lt_two]
    linarith [Real.two_le_pi]
  -- Bound `(1 - ‖z‖)^{-(|σ| + |y|)}` by `2^{|σ|} exp ((log 2) |y|)` on `‖z‖ < 1 / 2`.
  refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs Kg hrate).const_mul
    (Cg * 2 ^ |σ|)).mono' ?_ (Eventually.of_forall fun y ↦ ?_)
  · have htsum (y : ℝ) := (h_sum y).tsum_eq
    simp_rw [htsum]
    refine Continuous.aestronglyMeasurable ?_
    have hc1 : Continuous fun y : ℝ ↦ Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|)) :=
      (continuous_const.mul ((continuous_const.add continuous_abs).rpow_const fun y ↦
        Or.inl (add_pos_of_pos_of_nonneg one_pos (abs_nonneg y)).ne')).mul (by fun_prop)
    have hc2 : Continuous fun y : ℝ ↦ 1 / (1 - ‖z‖) ^ (|σ| + |y|) :=
      continuous_const.div (continuous_const.rpow (continuous_const.add continuous_abs)
        fun _ ↦ Or.inl (by linarith)) fun _ ↦ (Real.rpow_pos_of_pos (by linarith) _).ne'
    exact hc1.mul hc2
  · rw [(h_sum y).tsum_eq]
    have hnonneg : 0 ≤ Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|)) *
        (1 / (1 - ‖z‖) ^ (|σ| + |y|)) := by
      have : 0 < (1 - ‖z‖) ^ (|σ| + |y|) := Real.rpow_pos_of_pos (by linarith) _
      positivity
    rw [Real.norm_of_nonneg hnonneg]
    have hpow_le : 1 / (1 - ‖z‖) ^ (|σ| + |y|) ≤ 2 ^ |σ| * Real.exp (Real.log 2 * |y|) := by
      have h12 : (2 : ℝ)⁻¹ ≤ 1 - ‖z‖ := by linarith
      have hrp : ((2 : ℝ)⁻¹) ^ (|σ| + |y|) ≤ (1 - ‖z‖) ^ (|σ| + |y|) :=
        Real.rpow_le_rpow (by positivity) h12 (by positivity)
      calc 1 / (1 - ‖z‖) ^ (|σ| + |y|)
          ≤ 1 / ((2 : ℝ)⁻¹) ^ (|σ| + |y|) := one_div_le_one_div_of_le (by positivity) hrp
        _ = 2 ^ (|σ| + |y|) := by rw [Real.inv_rpow zero_le_two, one_div, inv_inv]
        _ = 2 ^ |σ| * Real.exp (Real.log 2 * |y|) := by
            rw [Real.rpow_add zero_lt_two, Real.rpow_def_of_pos zero_lt_two |y|]
    calc Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|)) * (1 / (1 - ‖z‖) ^ (|σ| + |y|))
        ≤ Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|)) *
            (2 ^ |σ| * Real.exp (Real.log 2 * |y|)) :=
          mul_le_mul_of_nonneg_left hpow_le (by positivity)
      _ = Cg * 2 ^ |σ| * ((1 + |y|) ^ Kg *
            (Real.exp (-(2 * π * |y|)) * Real.exp (Real.log 2 * |y|))) := by ring
      _ = Cg * 2 ^ |σ| * ((1 + |y|) ^ Kg * Real.exp (-((2 * π - Real.log 2) * |y|))) := by
          rw [← Real.exp_add]; ring_nf

/-- On the open disk `‖z‖ < 1 / 2`, `regularizedGaussHGFun a b c z` equals the Mellin–Barnes
integral 15.6.7 along any separating vertical line `Re s = σ`. -/
private theorem regularizedGaussHGFun_eq_mellinBarnes_one_sub_of_norm_lt_half (a b c : ℂ) {z : ℂ}
    (hz : ‖z‖ < 1 / 2) {σ : ℝ} (hσ : σ < 0) (hσc : σ < (c - a - b).re) (haσ : -a.re < σ)
    (hbσ : -b.re < σ) :
    regularizedGaussHGFun a b c z =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - z) ^ ((σ : ℂ) + y * I) := by
  have hz1 : ‖z‖ < 1 := by linarith
  have ha' : ∀ n : ℕ, a.re + σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hb' : ∀ n : ℕ, b.re + σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hc' : ∀ n : ℕ, (c - a - b).re - σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  have hσ' : ∀ n : ℕ, σ ≠ n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
  let G : ℝ → ℂ := fun y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))
  obtain ⟨Cg, hCg, Kg, hbg⟩ := exists_norm_four_Gamma_le ha' hb' hc' hσ'
  let F : ℕ → ℝ → ℂ := fun n y ↦ G y * (Ring.multichoose (-((σ : ℂ) + y * I)) n * z ^ n)
  let bound : ℕ → ℝ → ℝ := fun n y ↦
    Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|)) *
      (Ring.multichoose (|σ| + |y|) n * ‖z‖ ^ n)
  -- Measurability and dominated-convergence bounds for the binomial-series terms.
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) volume := by
    refine Continuous.aestronglyMeasurable <| (continuous_four_Gamma ha' hb' hc' hσ').mul ?_
    simp_rw [TauCeti.Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer]
    exact (continuous_const.mul ((ascPochhammer ℂ n).continuous.comp (by fun_prop))).mul
      continuous_const
  have h_bound (n : ℕ) : ∀ᵐ y : ℝ, ‖F n y‖ ≤ bound n y := by
    refine Eventually.of_forall fun y ↦ ?_
    have hnorm_le : ‖-((σ : ℂ) + y * I)‖ ≤ |σ| + |y| := by
      rw [norm_neg]; simpa using norm_le_abs_re_add_abs_im ((σ : ℂ) + y * I)
    have hmc := TauCeti.norm_multichoose_le_of_norm_le hnorm_le n
    calc ‖F n y‖
        = ‖G y‖ * (‖Ring.multichoose (-((σ : ℂ) + y * I)) n‖ * ‖z‖ ^ n) := by
            dsimp [F]; rw [norm_mul, norm_mul (Ring.multichoose _ _) (z ^ n), norm_pow]
      _ ≤ bound n y :=
          mul_le_mul (hbg y) (mul_le_mul_of_nonneg_right hmc (by positivity))
            (by positivity) (by positivity)
  have h_bound_summable : ∀ᵐ y : ℝ, Summable fun n ↦ bound n y :=
    Eventually.of_forall fun y ↦
      ((TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (r := |σ| + |y|)
        (x := ‖z‖) (by rwa [abs_norm])).mul_left _).summable
  have h_lim : ∀ᵐ y : ℝ, HasSum (fun n : ℕ ↦ F n y) (G y * (1 - z) ^ ((σ : ℂ) + y * I)) := by
    refine Eventually.of_forall fun y ↦ ?_
    simpa only [F, one_div, cpow_neg, inv_inv] using
      (TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one
        (r := -((σ : ℂ) + y * I)) hz1).mul_left (G y)
  -- Integrate term by term and match the power-series sum of `regularizedGaussHGFun`.
  have h_hasSum_int := hasSum_integral_of_dominated_convergence bound hF_meas h_bound
    h_bound_summable (integrable_tsum_multichoose_bound hCg Kg σ hz) h_lim
  have h_rhs_sum : HasSum (fun n : ℕ ↦ (regularizedGaussHGFunSeries a b c).coeff n * z ^ n)
      ((2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, G y * (1 - z) ^ ((σ : ℂ) + y * I)) := by
    simpa only [F, G, integral_four_Gamma_mul_multichoose a b c z hσ hσc haσ hbσ] using
      h_hasSum_int.mul_left (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹
  simpa only [G, mul_assoc] using (hasSum_regularizedGaussHGFun a b c hz1).unique h_rhs_sum

/-- **Mellin–Barnes integral for the regularized Gauss hypergeometric series**
([DLMF 15.6.7](https://dlmf.nist.gov/15.6.E7)) on the open unit disk `‖z‖ < 1`: on any vertical
line `Re s = σ` with `max (-Re a, -Re b) < σ < min (0, Re (c - a - b))`,
`regularizedGaussHGFun a b c z =
  (2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫ Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s) (1 - z)^s dy`. -/
theorem regularizedGaussHGFun_eq_mellinBarnes_one_sub (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    {σ : ℝ} (hσ : σ < 0) (hσc : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    regularizedGaussHGFun a b c z =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - z) ^ ((σ : ℂ) + y * I) := by
  have h_lhs : AnalyticOnNhd ℂ (regularizedGaussHGFun a b c) (ball 0 1) := by
    intro w hw
    exact analyticAt_regularizedHGFun_of_card_eq_add_one rfl (by simpa using hw)
  have h_rhs : AnalyticOnNhd ℂ
      (fun w : ℂ ↦ (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - w) ^ ((σ : ℂ) + y * I)) (ball 0 1) := by
    have ha' : ∀ n : ℕ, a.re + σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
    have hb' : ∀ n : ℕ, b.re + σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
    have hc' : ∀ n : ℕ, (c - a - b).re - σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
    have hσ' : ∀ n : ℕ, σ ≠ n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
    intro w hw
    have h1w : 1 - w ∈ slitPlane := by
      simpa [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one (z := -w) (by simpa using hw)
    exact analyticAt_const.mul
      (analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow
        ha' hb' hc' hσ' w h1w)
  have hev : regularizedGaussHGFun a b c =ᶠ[𝓝 (0 : ℂ)] fun w : ℂ ↦
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - w) ^ ((σ : ℂ) + y * I) := by
    filter_upwards [ball_mem_nhds (0 : ℂ) (by positivity : (0 : ℝ) < 1 / 2)] with w hw
    exact regularizedGaussHGFun_eq_mellinBarnes_one_sub_of_norm_lt_half a b c
      (by simpa using hw) hσ hσc haσ hbσ
  exact h_lhs.eqOn_of_preconnected_of_eventuallyEq h_rhs (convex_ball 0 1).isPreconnected
    (mem_ball_self zero_lt_one) hev (by simpa using hz)

/-- **Mellin–Barnes integral for the ordinary Gauss hypergeometric series** on `‖z‖ < 1`. Since the
separating-line hypotheses imply `0 < Re a` and `0 < Re (c - a)`, hence `0 < Re c`, no separate
non-pole condition on `c` is required. -/
theorem ordinaryHypergeometric_eq_mellinBarnes_one_sub (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1)
    {σ : ℝ} (hσ : σ < 0) (hσc : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    ordinaryHypergeometric a b c z =
      Gamma c * (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - z) ^ ((σ : ℂ) + y * I) := by
  have hc_pos : 0 < c.re := by simp at hσc; linarith
  have hc_ne : ∀ k : ℕ, c ≠ -k := fun k hk ↦ by
    have hre := congrArg re hk; simp at hre; linarith [k.cast_nonneg' (α := ℝ)]
  have hΓc : Gamma c ≠ 0 := Gamma_ne_zero_of_re_pos hc_pos
  have hdiv := ordinaryHypergeometric_div_Gamma_eq (a := a) (b := b) (z := z) hc_ne
  rw [(div_eq_iff hΓc).mp hdiv,
    regularizedGaussHGFun_eq_mellinBarnes_one_sub a b c hz hσ hσc haσ hbσ]
  ring

end Complex
