/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.MellinInversion
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Mellin–Barnes integrals for the Gauss hypergeometric function

The Gauss hypergeometric function admits two classical Mellin–Barnes contour representations along
vertical lines `s = σ + i y` separating left-opening and right-opening Gamma pole sequences
([DLMF 15.6.6](https://dlmf.nist.gov/15.6.E6) and [DLMF 15.6.7](https://dlmf.nist.gov/15.6.E7)):

* In powers of `-z` on `{z : ℂ | -z ∈ Complex.slitPlane}` (`ℂ \ [0, ∞)`), with `-Re a < σ < 0` and
  `-Re b < σ`, the integrand
  `Γ(a + s) Γ(b + s) Γ(-s) (Γ(c + s))⁻¹ (-z) ^ s`
  combines three decaying Gamma factors (`e^{-3π |y| / 2}`) with one entire reciprocal Gamma factor
  (`e^{π |y| / 2}`), giving net vertical decay `O((1 + |y|) ^ R e^{-π |y|})`. Its integral defines
  a function holomorphic in `z` on `{z | -z ∈ Complex.slitPlane}` and entire in `c` on `ℂ`, and
  equals `Complex.eulerIntegral a b c z` whenever `Re b < Re c`.
* In powers of `1 - z` on `{z : ℂ | 1 - z ∈ Complex.slitPlane}` (`ℂ \ [1, ∞)`), with
  `-Re a < σ < 0`, `-Re b < σ`, and `σ < Re(c - a - b)`, the four-Gamma integrand
  `Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s) (1 - z) ^ s`
  decays like `O((1 + |y|) ^ R e^{-2π |y|})`. Its normalized integral is holomorphic on the entire
  cut plane `{z | 1 - z ∈ Complex.slitPlane}`, equals `Complex.eulerIntegral a b c z` throughout
  that cut plane, and equals Mathlib's `Complex.regularizedGaussHGFun a b c z` (hence also
  `(Γ c)⁻¹ ₂F₁(a, b; c; z)` when `c ∉ -ℕ`) on the open unit disk `‖z‖ < 1`.

On the cut plane, both representations of `Complex.eulerIntegral` follow by inserting the
slit-plane Mellin–Barnes integral of `(1 + w) ^ (-a)` into Euler's integral (directly with
`w = t (-z)` for DLMF 15.6.6, and after factoring `1 - z t = (1 - t) (1 + t (1 - t)⁻¹ (1 - z))`
for DLMF 15.6.7) and exchanging the `0..1` and `ℝ` integrals via Fubini's theorem. On the unit
disk, `Complex.regularizedGaussHGFun_eq_mellinBarnes_one_sub` expands `(1 - w) ^ s` on
`‖w‖ < 1 / 2` in its multichoose binomial series, interchanges summation and integration using the
`e^{-2π |y|}` decay against `2 ^ ‖s‖ ≤ 2 ^ |σ| e^{(log 2) |y|}`, evaluates each term by Barnes's
first lemma (`Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`), and extends
from `‖w‖ < 1 / 2` to `‖w‖ < 1` by analytic continuation.

## Main results

* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow`,
  `Complex.differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow`,
  `Complex.analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow`,
  `Complex.differentiable_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow`:
  integrability, holomorphy in `z` on `{z | -z ∈ Complex.slitPlane}`, and entirety in `c : ℂ` of
  the Mellin–Barnes integral in `-z`.
* `Complex.eulerIntegral_eq_mellinBarnes`: DLMF 15.6.6 for `Complex.eulerIntegral` on
  `{z | -z ∈ Complex.slitPlane}` when `Re b < Re c` and `-min(Re a, Re b) < σ < 0`.
* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow`,
  `Complex.differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow`,
  `Complex.analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow`:
  integrability and holomorphy in `z` on `{z | 1 - z ∈ Complex.slitPlane}` of the Mellin–Barnes
  integral in `1 - z`.
* `Complex.eulerIntegral_eq_mellinBarnes_one_sub`: DLMF 15.6.7 for `Complex.eulerIntegral` on the
  entire cut plane `{z | 1 - z ∈ Complex.slitPlane}`.
* `Complex.regularizedGaussHGFun_eq_mellinBarnes_one_sub`,
  `Complex.ordinaryHypergeometric_eq_mellinBarnes_one_sub`: DLMF 15.6.7 on the open unit disk
  `‖z‖ < 1` for `Complex.regularizedGaussHGFun` and `Complex.ordinaryHypergeometric`.

## References

* [NIST Digital Library of Mathematical Functions, §15.6(ii)](https://dlmf.nist.gov/15.6.ii),
  equations 15.6.6 and 15.6.7.
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.5–14.52.
-/

public section

noncomputable section

open Complex Filter Function MeasureTheory Set
open scoped Nat Real Topology

namespace Complex

/-! ### Mellin–Barnes integral in `-z` (DLMF 15.6.6) -/

/-- Continuity and `O((1 + |y|) ^ (Re a + Re b - Re c - 1) e^{-π |y|})` vertical bound for the
Gamma kernel `y ↦ Γ(a + s) Γ(b + s) Γ(-s) (Γ(c + s))⁻¹` on `s = σ + i y`. -/
private theorem continuous_and_norm_mellinBarnesNegKernel_le (c : ℂ) {a b : ℂ} {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Continuous (fun y : ℝ ↦
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹) ∧
      ∃ C > 0, ∀ y : ℝ,
        ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
            Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹‖ ≤
          C * (1 + |y|) ^ (a.re + b.re - c.re - 1) * Real.exp (-π * |y|) := by
  have ha' : ∀ n : ℕ, (a + σ).re ≠ -n := by simpa [add_re] using haσ
  have hb' : ∀ n : ℕ, (b + σ).re ≠ -n := by simpa [add_re] using hbσ
  have hσ' : ∀ n : ℕ, ((-σ : ℝ) : ℂ).re ≠ -n := by simpa using hσ
  obtain ⟨C₁, hC₁, h₁⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le ha'
  obtain ⟨C₂, hC₂, h₂⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le hb'
  obtain ⟨C₃, hC₃, h₃⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hσ'
  obtain ⟨C₄, hC₄, h₄⟩ := TauCeti.exists_norm_inv_Gamma_add_mul_I_le (c + σ)
  have hcont : Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ := by
    have hinv_cont : Continuous fun w : ℂ ↦ (Gamma w)⁻¹ := by
      simpa only [one_div] using differentiable_one_div_Gamma.continuous
    refine (((Continuous.mul ?_ ?_).mul ?_).mul (hinv_cont.comp (by fun_prop)))
    · exact continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          haσ m (by simpa [add_re] using congrArg re hm)).continuousAt.comp (by fun_prop)
    · exact continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          hbσ m (by simpa [add_re] using congrArg re hm)).continuousAt.comp (by fun_prop)
    · exact continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          hσ m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
  refine ⟨hcont, C₁ * C₂ * C₃ * C₄, by positivity, fun y ↦ ?_⟩
  have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
  have e1 : a + ((σ : ℂ) + y * I) = (a + σ) + y * I := by ring
  have e2 : b + ((σ : ℂ) + y * I) = (b + σ) + y * I := by ring
  have e3 : -((σ : ℂ) + y * I) = ((-σ : ℝ) : ℂ) - y * I := by push_cast; ring
  have e4 : c + ((σ : ℂ) + y * I) = (c + σ) + y * I := by ring
  have b1 : ‖Gamma (a + (σ + y * I))‖ ≤
      C₁ * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    simpa [e1, add_re] using h₁ y
  have b2 : ‖Gamma (b + (σ + y * I))‖ ≤
      C₂ * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    simpa [e2, add_re] using h₂ y
  have b3 : ‖Gamma (-(σ + y * I))‖ ≤
      C₃ * (1 + |y|) ^ (-σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    simpa [e3] using h₃ y
  have b4 : ‖(Gamma (c + (σ + y * I)))⁻¹‖ ≤
      C₄ * (1 + |y|) ^ (1 / 2 - (c.re + σ)) * Real.exp (π * |y| / 2) := by
    simpa [e4, add_re] using h₄ y
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ *
        ‖Gamma (-(σ + y * I))‖ * ‖(Gamma (c + (σ + y * I)))⁻¹‖
      ≤ (C₁ * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₂ * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₃ * (1 + |y|) ^ (-σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₄ * (1 + |y|) ^ (1 / 2 - (c.re + σ)) * Real.exp (π * |y| / 2)) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) (by positivity))
          b3 (norm_nonneg _) (by positivity)) b4 (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * C₃ * C₄ *
          ((1 + |y|) ^ (a.re + σ - 1 / 2) * (1 + |y|) ^ (b.re + σ - 1 / 2) *
            (1 + |y|) ^ (-σ - 1 / 2) * (1 + |y|) ^ (1 / 2 - (c.re + σ))) *
          (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2) *
            Real.exp (-π * |y| / 2) * Real.exp (π * |y| / 2)) := by ring
    _ = C₁ * C₂ * C₃ * C₄ * (1 + |y|) ^ (a.re + b.re - c.re - 1) * Real.exp (-π * |y|) := by
        rw [← Real.rpow_add h1y, ← Real.rpow_add h1y, ← Real.rpow_add h1y,
          ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        ring_nf

/-- For `-z ∈ Complex.slitPlane`, arbitrary `c : ℂ`, and any vertical line `Re s = σ` avoiding the
poles of `Γ(a + s)`, `Γ(b + s)`, and `Γ(-s)`, the Mellin–Barnes integrand of DLMF 15.6.6 is
integrable on `ℝ`. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow
    (c : ℂ) {a b z : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) (hz : -z ∈ slitPlane) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  obtain ⟨hcont, C, _, hbound⟩ := continuous_and_norm_mellinBarnesNegKernel_le c haσ hbσ hσ
  have h := TauCeti.integrable_cpow_smul_of_norm_le_exp_neg_pi_mul_abs
    hcont.aestronglyMeasurable ⟨C, a.re + b.re - c.re - 1, hbound⟩ σ hz
  exact h.congr (Eventually.of_forall fun y ↦ by simp [smul_eq_mul, mul_comm])

/-- The Mellin–Barnes integral in `-z` (DLMF 15.6.6) is complex differentiable in `z` on the cut
plane `{z : ℂ | -z ∈ Complex.slitPlane}` (`ℂ \ [0, ∞)`). -/
theorem differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow
    (c : ℂ) {a b : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) :
    DifferentiableOn ℂ (fun z : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I))
      {z : ℂ | -z ∈ slitPlane} := by
  obtain ⟨hcont, C, _, hbound⟩ := continuous_and_norm_mellinBarnesNegKernel_le c haσ hbσ hσ
  have hH := TauCeti.differentiableOn_integral_cpow_smul_slitPlane
    hcont.aestronglyMeasurable ⟨C, a.re + b.re - c.re - 1, hbound⟩ σ
  refine (hH.comp differentiableOn_id.neg fun _ hz ↦ hz).congr fun z _ ↦ ?_
  exact integral_congr_ae (Eventually.of_forall fun y ↦ by simp [smul_eq_mul, mul_comm])

/-- The Mellin–Barnes integral in `-z` (DLMF 15.6.6) is holomorphic in `z` on the cut plane
`{z : ℂ | -z ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow
    (c : ℂ) {a b : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I))
      {z : ℂ | -z ∈ slitPlane} :=
  (differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow
    c haσ hbσ hσ).analyticOnNhd (isOpen_slitPlane.preimage continuous_neg)

/-- For fixed `a, b, z` with `-z ∈ Complex.slitPlane` and pole-free `σ`, the Mellin–Barnes
integral of DLMF 15.6.6 is an entire function of the denominator parameter `c : ℂ`. -/
theorem differentiable_integral_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow
    {a b z : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) (hz : -z ∈ slitPlane) :
    Differentiable ℂ fun c : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  intro c₀
  have ha' : ∀ n : ℕ, (a + σ).re ≠ -n := by simpa [add_re] using haσ
  have hb' : ∀ n : ℕ, (b + σ).re ≠ -n := by simpa [add_re] using hbσ
  have hσ' : ∀ n : ℕ, ((-σ : ℝ) : ℂ).re ≠ -n := by simpa using hσ
  obtain ⟨C₁, hC₁, h₁⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le ha'
  obtain ⟨C₂, hC₂, h₂⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le hb'
  obtain ⟨C₃, hC₃, h₃⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hσ'
  obtain ⟨C₄, hC₄, h₄⟩ :=
    TauCeti.exists_norm_deriv_inv_Gamma_vertical_strip_le (c₀.re + σ - 1) (c₀.re + σ + 1)
  have hinvG : Differentiable ℂ fun w : ℂ ↦ (Gamma w)⁻¹ := by
    simpa only [one_div] using differentiable_one_div_Gamma
  let h : ℝ → ℂ := fun y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (-(σ + y * I)) * (-z) ^ ((σ : ℂ) + y * I)
  have hh_cont : Continuous h := by
    refine ((Continuous.mul ?_ ?_).mul ?_).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (slitPlane_ne_zero hz)))
    · exact continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          haσ m (by simpa [add_re] using congrArg re hm)).continuousAt.comp (by fun_prop)
    · exact continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          hbσ m (by simpa [add_re] using congrArg re hm)).continuousAt.comp (by fun_prop)
    · exact continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          hσ m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
  set δ : ℝ := π - |(-z).arg|
  have hδ : 0 < δ := sub_pos.2 (abs_arg_lt_pi_of_mem_slitPlane hz)
  set r : ℝ := 3 / 2 - (c₀.re + σ - 1)
  set r' : ℝ := max r 0
  set K : ℝ := C₁ * C₂ * C₃ * ‖-z‖ ^ σ * C₄ * (2 + |c₀.im|) ^ r' *
    Real.exp (π * (1 + |c₀.im|) / 2)
  set R : ℝ := a.re + b.re + σ - 3 / 2 + r'
  have hF_meas : ∀ᶠ c in 𝓝 c₀, AEStronglyMeasurable (fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I)) :=
    Eventually.of_forall fun c ↦
      (continuous_and_norm_mellinBarnesNegKernel_le c haσ hbσ hσ).1.mul
        (Continuous.const_cpow (by fun_prop) (Or.inl (slitPlane_ne_zero hz)))
          |>.aestronglyMeasurable
  have hF'_cont : Continuous fun y : ℝ ↦
      h y * deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (c₀ + ((σ : ℂ) + y * I)) :=
    hh_cont.mul ((hinvG.contDiff.continuous_deriv le_rfl).comp (by fun_prop))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (c : ℂ) (y : ℝ) ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I))
    (F' := fun (c : ℂ) (y : ℝ) ↦
      h y * deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (c + ((σ : ℂ) + y * I)))
    (bound := fun y : ℝ ↦ K * ((1 + |y|) ^ R * Real.exp (-δ * |y|)))
    (Metric.ball_mem_nhds c₀ one_pos) hF_meas
    (integrable_Gamma_mul_Gamma_mul_Gamma_neg_mul_inv_Gamma_mul_neg_cpow c₀ haσ hbσ hσ hz)
    hF'_cont.aestronglyMeasurable ?_
    ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs hδ R).const_mul K) ?_).2
      |>.differentiableAt
  · refine Eventually.of_forall fun y c hc ↦ ?_
    rw [Metric.mem_ball, dist_eq_norm] at hc
    have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
    have e1 : a + ((σ : ℂ) + y * I) = (a + σ) + y * I := by ring
    have e2 : b + ((σ : ℂ) + y * I) = (b + σ) + y * I := by ring
    have e3 : -((σ : ℂ) + y * I) = ((-σ : ℝ) : ℂ) - y * I := by push_cast; ring
    have b1 : ‖Gamma (a + (σ + y * I))‖ ≤
        C₁ * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
      simpa [e1, add_re] using h₁ y
    have b2 : ‖Gamma (b + (σ + y * I))‖ ≤
        C₂ * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
      simpa [e2, add_re] using h₂ y
    have b3 : ‖Gamma (-(σ + y * I))‖ ≤
        C₃ * (1 + |y|) ^ (-σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
      simpa [e3] using h₃ y
    have bpow : ‖(-z) ^ ((σ : ℂ) + y * I)‖ ≤ ‖-z‖ ^ σ * Real.exp ((π - δ) * |y|) := by
      have hre : ((σ : ℂ) + y * I).re = σ := by simp
      have him : ((σ : ℂ) + y * I).im = y := by simp
      have hang : (Real.exp ((-z).arg * y))⁻¹ ≤ Real.exp ((π - δ) * |y|) := by
        rw [← Real.exp_neg]
        refine Real.exp_le_exp.2 ?_
        calc -((-z).arg * y) ≤ |(-z).arg * y| := neg_le_abs _
          _ = |(-z).arg| * |y| := abs_mul _ _
          _ = (π - δ) * |y| := by dsimp [δ]; ring
      calc ‖(-z) ^ ((σ : ℂ) + y * I)‖
          ≤ ‖-z‖ ^ ((σ : ℂ) + y * I).re / Real.exp ((-z).arg * ((σ : ℂ) + y * I).im) :=
            norm_cpow_le _ _
        _ = ‖-z‖ ^ σ * (Real.exp ((-z).arg * y))⁻¹ := by rw [hre, him, div_eq_mul_inv]
        _ ≤ ‖-z‖ ^ σ * Real.exp ((π - δ) * |y|) :=
            mul_le_mul_of_nonneg_left hang (Real.rpow_nonneg (norm_nonneg _) _)
    set w : ℂ := c + ((σ : ℂ) + y * I)
    have hw_re : w.re ∈ Icc (c₀.re + σ - 1) (c₀.re + σ + 1) := by
      have hcre : |c.re - c₀.re| < 1 := (abs_re_le_norm (c - c₀)).trans_lt hc
      obtain ⟨hl, hu⟩ := abs_lt.1 hcre
      simp only [w, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
        sub_self, add_zero, mem_Icc]
      exact ⟨by linarith, by linarith⟩
    have hw_im_le : |w.im| ≤ 1 + |c₀.im| + |y| := by
      have hcim : |c.im - c₀.im| < 1 := (abs_im_le_norm (c - c₀)).trans_lt hc
      have hwim : w.im = (c.im - c₀.im) + c₀.im + y := by simp [w]
      have ht1 := abs_add_le ((c.im - c₀.im) + c₀.im) y
      have ht2 := abs_add_le (c.im - c₀.im) c₀.im
      rw [← hwim] at ht1
      linarith
    have b4 : ‖deriv (fun u : ℂ ↦ (Gamma u)⁻¹) w‖ ≤
        C₄ * (2 + |c₀.im|) ^ r' * Real.exp (π * (1 + |c₀.im|) / 2) *
          (1 + |y|) ^ r' * Real.exp (π * |y| / 2) := by
      have hd := h₄ w hw_re
      have hr_le : (1 + |w.im|) ^ r ≤ (2 + |c₀.im|) ^ r' * (1 + |y|) ^ r' := by
        have h1w : 1 ≤ 1 + |w.im| := by linarith [abs_nonneg w.im]
        have hprod : 1 + |w.im| ≤ (2 + |c₀.im|) * (1 + |y|) := by
          nlinarith [abs_nonneg c₀.im, abs_nonneg y]
        calc (1 + |w.im|) ^ r
            ≤ (1 + |w.im|) ^ r' := Real.rpow_le_rpow_of_exponent_le h1w (le_max_left r 0)
          _ ≤ ((2 + |c₀.im|) * (1 + |y|)) ^ r' :=
              Real.rpow_le_rpow (by positivity) hprod (le_max_right r 0)
          _ = (2 + |c₀.im|) ^ r' * (1 + |y|) ^ r' :=
              Real.mul_rpow (by linarith [abs_nonneg c₀.im]) h1y.le
      have hexp : Real.exp (π * |w.im| / 2) ≤
          Real.exp (π * (1 + |c₀.im|) / 2) * Real.exp (π * |y| / 2) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
      calc ‖deriv (fun u : ℂ ↦ (Gamma u)⁻¹) w‖
          ≤ C₄ * (1 + |w.im|) ^ r * Real.exp (π * |w.im| / 2) := hd
        _ ≤ C₄ * ((2 + |c₀.im|) ^ r' * (1 + |y|) ^ r') *
              (Real.exp (π * (1 + |c₀.im|) / 2) * Real.exp (π * |y| / 2)) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hr_le hC₄.le) hexp
              (by positivity) (by positivity)
        _ = C₄ * (2 + |c₀.im|) ^ r' * Real.exp (π * (1 + |c₀.im|) / 2) *
              (1 + |y|) ^ r' * Real.exp (π * |y| / 2) := by ring
    have hz_pos : 0 < ‖-z‖ := norm_pos_iff.2 (slitPlane_ne_zero hz)
    dsimp [h]
    rw [norm_mul, norm_mul, norm_mul, norm_mul]
    calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ *
          ‖Gamma (-(σ + y * I))‖ * ‖(-z) ^ ((σ : ℂ) + y * I)‖ *
          ‖deriv (fun u : ℂ ↦ (Gamma u)⁻¹) w‖
        ≤ (C₁ * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
            (C₂ * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
            (C₃ * (1 + |y|) ^ (-σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
            (‖-z‖ ^ σ * Real.exp ((π - δ) * |y|)) *
            (C₄ * (2 + |c₀.im|) ^ r' * Real.exp (π * (1 + |c₀.im|) / 2) *
              (1 + |y|) ^ r' * Real.exp (π * |y| / 2)) := by
          refine mul_le_mul (mul_le_mul (mul_le_mul (mul_le_mul b1 b2
            (norm_nonneg _) (by positivity)) b3 (norm_nonneg _) (by positivity))
            bpow (norm_nonneg _) (by positivity)) b4 (norm_nonneg _) (by positivity)
      _ = K * ((1 + |y|) ^ (a.re + σ - 1 / 2) * (1 + |y|) ^ (b.re + σ - 1 / 2) *
            (1 + |y|) ^ (-σ - 1 / 2) * (1 + |y|) ^ r') *
            (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2) *
              Real.exp (-π * |y| / 2) * Real.exp ((π - δ) * |y|) *
              Real.exp (π * |y| / 2)) := by dsimp [K]; ring
      _ = K * ((1 + |y|) ^ R * Real.exp (-δ * |y|)) := by
          rw [← Real.rpow_add h1y, ← Real.rpow_add h1y, ← Real.rpow_add h1y,
            ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
          dsimp [R]
          ring_nf
  · refine Eventually.of_forall fun y c _ ↦ ?_
    have hd : HasDerivAt (fun u : ℂ ↦ (Gamma (u + ((σ : ℂ) + y * I)))⁻¹)
        (deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (c + ((σ : ℂ) + y * I))) c := by
      simpa [Function.comp_def] using
        (hinvG.differentiableAt.hasDerivAt).comp c ((hasDerivAt_id' c).add_const _)
    exact (hd.const_mul (h y)).congr_of_eventuallyEq
      (Eventually.of_forall fun u ↦ by dsimp [h]; ring)

/-- **Mellin–Barnes integral for Euler's hypergeometric integral in `-z` (DLMF 15.6.6).**
For `Re b < Re c`, `-z ∈ Complex.slitPlane`, and `-min(Re a, Re b) < σ < 0`,
`Complex.eulerIntegral a b c z = (2π Γ(a) Γ(b))⁻¹ ∫_ℝ Γ(a + s) Γ(b + s) Γ(-s) (Γ(c + s))⁻¹ (-z)^s`
along `s = σ + i y`. -/
theorem eulerIntegral_eq_mellinBarnes {a b c z : ℂ} {σ : ℝ}
    (hbc : b.re < c.re) (hz : -z ∈ slitPlane)
    (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    eulerIntegral a b c z =
      (2 * π * Gamma a * Gamma b)⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I) := by
  have ha : 0 < a.re := by linarith
  have hb : 0 < b.re := by linarith
  have hcb : 0 < (c - b).re := by simp only [sub_re]; linarith
  have hbσ_pos : 0 < b.re + σ := by linarith
  have hσ_ne : ∀ n : ℕ, -σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  let s : ℝ → ℂ := fun y ↦ (σ : ℂ) + y * I
  let F : ℝ → ℝ → ℂ := fun t y ↦
    (t : ℂ) ^ (b + s y - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
      (Gamma (a + s y) * Gamma (-s y) * (-z) ^ s y)
  -- Express `Γ(a)` times Euler's integrand on `(0, 1]` via the Mellin–Barnes integral of
  -- `(1 + t (-z)) ^ (-a)`.
  have hpoint : ∫ t : ℝ in 0..1,
        Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      (2 * π : ℂ)⁻¹ * ∫ t : ℝ in 0..1, ∫ y : ℝ, F t y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
    rw [uIoc_of_le zero_le_one] at ht
    have ht_pos : 0 < t := ht.1
    have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht_pos.ne'
    have htz : (t : ℂ) * (-z) ∈ slitPlane := TauCeti.ofReal_mul_mem_slitPlane ht_pos hz
    have hmb := integral_Gamma_add_mul_Gamma_neg_mul_cpow hσ haσ htz
    have h1zt : 1 - z * (t : ℂ) = 1 + (t : ℂ) * (-z) := by ring
    rw [h1zt, mul_left_comm (Gamma a), ← hmb]
    have hpull : ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
        ((2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + s y) * Gamma (-s y) * ((t : ℂ) * (-z)) ^ s y) =
        (2 * π : ℂ)⁻¹ * ∫ y : ℝ, F t y := by
      rw [← mul_left_comm ((2 * π : ℂ)⁻¹), ← integral_const_mul]
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
      dsimp [F, s]
      rw [TauCeti.ofReal_mul_cpow ht_pos.le]
      have hpow : (t : ℂ) ^ (b - 1) * (t : ℂ) ^ ((σ : ℂ) + y * I) =
          (t : ℂ) ^ (b + ((σ : ℂ) + y * I) - 1) := by
        rw [← cpow_add _ _ ht_ne]
        congr 1
        ring
      rw [← hpow]
      ring
    exact hpull
  -- Check product integrability of `F` on `(0, 1] × ℝ` to swap the integrals.
  have hF_int : Integrable (uncurry F) ((volume.restrict (uIoc 0 1)).prod volume) := by
    have hmeas_oo : (volume.restrict (uIoc (0 : ℝ) 1)).prod (volume : Measure ℝ) =
        ((volume : Measure ℝ).prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ univ) := by
      rw [uIoc_of_le zero_le_one, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      simpa only [Measure.restrict_univ] using
        Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (Ioo (0 : ℝ) 1) univ
    have hφ : Integrable (fun t : ℝ ↦
        ‖(t : ℂ) ^ (((b.re + σ : ℝ) : ℂ) - 1) *
          (1 - (t : ℂ)) ^ (((c - b).re : ℂ) - 1)‖) (volume.restrict (uIoc 0 1)) := by
      have hbeta := betaIntegral_convergent
        (u := ((b.re + σ : ℝ) : ℂ)) (v := ((c - b).re : ℂ))
        (by simpa using hbσ_pos) (by simpa using hcb)
      exact (intervalIntegrable_iff.1 hbeta).norm
    have hψ : Integrable (fun y : ℝ ↦ ‖Gamma (a + s y) * Gamma (-s y) * (-z) ^ s y‖) volume :=
      (integrable_Gamma_add_mul_Gamma_neg_mul_cpow hσ_ne haσ_ne hz).norm
    have hF_meas : AEStronglyMeasurable (uncurry F)
        ((volume.restrict (uIoc 0 1)).prod volume) := by
      rw [hmeas_oo]
      refine ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ).prod volume) ?_
        (measurableSet_Ioo.prod MeasurableSet.univ)
      rintro ⟨t, y⟩ ⟨⟨ht0, ht1⟩, -⟩
      have ht_slit : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 ht0
      have h1t_slit : 1 - (t : ℂ) ∈ slitPlane := by
        rw [← ofReal_one, ← ofReal_sub]
        exact ofReal_mem_slitPlane.2 (sub_pos.2 ht1)
      refine ContinuousAt.continuousWithinAt ?_
      refine ((ContinuousAt.mul ?_ ?_).mul ((ContinuousAt.mul ?_ ?_).mul ?_))
      · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) ht_slit
      · exact ContinuousAt.cpow (by fun_prop) continuousAt_const h1t_slit
      · exact (differentiableAt_Gamma _ fun m hm ↦
          haσ_ne m (by simpa [s, add_re] using congrArg re hm)).continuousAt.comp (by fun_prop)
      · exact (differentiableAt_Gamma _ fun m hm ↦
          hσ_ne m (by simpa [s] using congrArg re hm)).continuousAt.comp (by fun_prop)
      · exact ContinuousAt.cpow continuousAt_const (by fun_prop) hz
    refine (hφ.mul_prod hψ).mono' hF_meas ?_
    rw [hmeas_oo]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with
      ⟨t, y⟩ ⟨⟨ht0, ht1⟩, _⟩
    have ht0' : 0 < t := ht0
    have h1t : 0 < 1 - t := sub_pos.2 ht1
    dsimp [uncurry, F, s]
    rw [← ofReal_one, ← ofReal_sub]
    simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0', norm_cpow_eq_rpow_re_of_pos h1t,
      sub_re, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    exact le_rfl
  -- Swap `∫_0^1` and `∫_ℝ`, then evaluate the inner Beta integral.
  have hinner (y : ℝ) : ∫ t : ℝ in 0..1, F t y =
      Gamma (c - b) * (Gamma (a + s y) * Gamma (b + s y) * Gamma (-s y) *
        (Gamma (c + s y))⁻¹ * (-z) ^ s y) := by
    dsimp [F]
    rw [intervalIntegral.integral_mul_const, ← betaIntegral,
      betaIntegral_eq_Gamma_mul_div (b + s y) (c - b) (by simpa [s, add_re] using hbσ_pos) hcb,
      show b + s y + (c - b) = c + s y by ring, div_eq_mul_inv]
    ring
  rw [intervalIntegral.integral_const_mul, intervalIntegral_integral_swap hF_int] at hpoint
  simp_rw [hinner, integral_const_mul] at hpoint
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hI : (∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * t) ^ (-a)) =
      (Gamma a)⁻¹ * ((2 * π : ℂ)⁻¹ * (Gamma (c - b) *
        ∫ y : ℝ, Gamma (a + s y) * Gamma (b + s y) * Gamma (-s y) *
          (Gamma (c + s y))⁻¹ * (-z) ^ s y)) := by
    rw [← hpoint, inv_mul_cancel_left₀ hΓa]
  rw [eulerIntegral_def, hI]
  dsimp only [s]
  generalize (∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
    Gamma (-(σ + y * I)) * (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ (σ + y * I)) = J
  field_simp [hΓa, hΓb, hΓcb, hpi]

/-! ### Mellin–Barnes integral in `1 - z` (DLMF 15.6.7) -/

/-- Continuity and `O((1 + |y|) ^ (Re c - 2) e^{-2π |y|})` vertical decay for the four-Gamma
kernel `y ↦ Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s)` on `s = σ + i y`. -/
private theorem continuous_and_norm_mellinBarnesOneSubKernel_le {a b c : ℂ} {σ : ℝ}
    (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hbσ : ∀ n : ℕ, b.re + σ ≠ -n)
    (hcab : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, -σ ≠ -n) :
    Continuous (fun y : ℝ ↦
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))) ∧
      ∃ C > 0, ∀ y : ℝ,
        ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
            Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
          C * (1 + |y|) ^ (c.re - 2) * Real.exp (-2 * π * |y|) := by
  have ha' : ∀ n : ℕ, (a + σ).re ≠ -n := by simpa [add_re] using haσ
  have hb' : ∀ n : ℕ, (b + σ).re ≠ -n := by simpa [add_re] using hbσ
  have hcab' : ∀ n : ℕ, (c - a - b - σ).re ≠ -n := by simpa [sub_re] using hcab
  have hσ' : ∀ n : ℕ, ((-σ : ℝ) : ℂ).re ≠ -n := by simpa using hσ
  obtain ⟨C₁, hC₁, h₁⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le ha'
  obtain ⟨C₂, hC₂, h₂⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le hb'
  obtain ⟨C₃, hC₃, h₃⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hcab'
  obtain ⟨C₄, hC₄, h₄⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hσ'
  have hcont : Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) := by
    refine (((Continuous.mul ?_ ?_).mul ?_).mul ?_)
    · exact continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          haσ m (by simpa [add_re] using congrArg re hm)).continuousAt.comp (by fun_prop)
    · exact continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          hbσ m (by simpa [add_re] using congrArg re hm)).continuousAt.comp (by fun_prop)
    · exact continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          hcab m (by simpa [sub_re] using congrArg re hm)).continuousAt.comp (by fun_prop)
    · exact continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          hσ m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
  refine ⟨hcont, C₁ * C₂ * C₃ * C₄, by positivity, fun y ↦ ?_⟩
  have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
  have e1 : a + ((σ : ℂ) + y * I) = (a + σ) + y * I := by ring
  have e2 : b + ((σ : ℂ) + y * I) = (b + σ) + y * I := by ring
  have e3 : c - a - b - ((σ : ℂ) + y * I) = (c - a - b - σ) - y * I := by ring
  have e4 : -((σ : ℂ) + y * I) = ((-σ : ℝ) : ℂ) - y * I := by push_cast; ring
  have b1 : ‖Gamma (a + (σ + y * I))‖ ≤
      C₁ * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    simpa [e1, add_re] using h₁ y
  have b2 : ‖Gamma (b + (σ + y * I))‖ ≤
      C₂ * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    simpa [e2, add_re] using h₂ y
  have b3 : ‖Gamma (c - a - b - (σ + y * I))‖ ≤
      C₃ * (1 + |y|) ^ (c.re - a.re - b.re - σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    simpa [e3, sub_re] using h₃ y
  have b4 : ‖Gamma (-(σ + y * I))‖ ≤
      C₄ * (1 + |y|) ^ (-σ - 1 / 2) * Real.exp (-π * |y| / 2) := by
    simpa [e4] using h₄ y
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖Gamma (a + (σ + y * I))‖ * ‖Gamma (b + (σ + y * I))‖ *
        ‖Gamma (c - a - b - (σ + y * I))‖ * ‖Gamma (-(σ + y * I))‖
      ≤ (C₁ * (1 + |y|) ^ (a.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₂ * (1 + |y|) ^ (b.re + σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₃ * (1 + |y|) ^ (c.re - a.re - b.re - σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₄ * (1 + |y|) ^ (-σ - 1 / 2) * Real.exp (-π * |y| / 2)) := by
        refine mul_le_mul (mul_le_mul (mul_le_mul b1 b2 (norm_nonneg _) (by positivity))
          b3 (norm_nonneg _) (by positivity)) b4 (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * C₃ * C₄ *
          ((1 + |y|) ^ (a.re + σ - 1 / 2) * (1 + |y|) ^ (b.re + σ - 1 / 2) *
            (1 + |y|) ^ (c.re - a.re - b.re - σ - 1 / 2) * (1 + |y|) ^ (-σ - 1 / 2)) *
          (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2) *
            Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2)) := by ring
    _ = C₁ * C₂ * C₃ * C₄ * (1 + |y|) ^ (c.re - 2) * Real.exp (-2 * π * |y|) := by
        rw [← Real.rpow_add h1y, ← Real.rpow_add h1y, ← Real.rpow_add h1y,
          ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        ring_nf

/-- For `1 - z ∈ Complex.slitPlane` and any vertical line `Re s = σ` avoiding the poles of
`Γ(a + s)`, `Γ(b + s)`, `Γ(c - a - b - s)`, and `Γ(-s)`, the Mellin–Barnes integrand of
DLMF 15.6.7 is integrable on `ℝ`. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow
    {a b c z : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hcab : ∀ n : ℕ, (c - a - b).re - σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) (hz : 1 - z ∈ slitPlane) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I) := by
  obtain ⟨hcont, C, hC, hbound⟩ :=
    continuous_and_norm_mellinBarnesOneSubKernel_le haσ hbσ hcab hσ
  have hbound' : ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
        C * (1 + |y|) ^ (c.re - 2) * Real.exp (-π * |y|) := fun y ↦
    (hbound y).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, abs_nonneg y])) (by positivity))
  have h := TauCeti.integrable_cpow_smul_of_norm_le_exp_neg_pi_mul_abs
    hcont.aestronglyMeasurable ⟨C, c.re - 2, hbound'⟩ σ hz
  exact h.congr (Eventually.of_forall fun y ↦ by simp [smul_eq_mul, mul_comm])

/-- The Mellin–Barnes integral in `1 - z` (DLMF 15.6.7) is complex differentiable in `z` on the
entire cut plane `{z : ℂ | 1 - z ∈ Complex.slitPlane}` (`ℂ \ [1, ∞)`). -/
theorem differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow
    {a b c : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hcab : ∀ n : ℕ, (c - a - b).re - σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    DifferentiableOn ℂ (fun z : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I))
      {z : ℂ | 1 - z ∈ slitPlane} := by
  obtain ⟨hcont, C, hC, hbound⟩ :=
    continuous_and_norm_mellinBarnesOneSubKernel_le haσ hbσ hcab hσ
  have hbound' : ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
        C * (1 + |y|) ^ (c.re - 2) * Real.exp (-π * |y|) := fun y ↦
    (hbound y).trans (mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (by nlinarith [Real.pi_pos, abs_nonneg y])) (by positivity))
  have hH := TauCeti.differentiableOn_integral_cpow_smul_slitPlane
    hcont.aestronglyMeasurable ⟨C, c.re - 2, hbound'⟩ σ
  refine (hH.comp (differentiableOn_const (1 : ℂ) |>.sub differentiableOn_id)
    fun _ hz ↦ hz).congr fun z _ ↦ ?_
  exact integral_congr_ae (Eventually.of_forall fun y ↦ by simp [smul_eq_mul, mul_comm])

/-- The Mellin–Barnes integral in `1 - z` (DLMF 15.6.7) is holomorphic in `z` on the entire cut
plane `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow
    {a b c : ℂ} {σ : ℝ} (haσ : ∀ n : ℕ, a.re + σ ≠ -n)
    (hbσ : ∀ n : ℕ, b.re + σ ≠ -n) (hcab : ∀ n : ℕ, (c - a - b).re - σ ≠ -n)
    (hσ : ∀ n : ℕ, -σ ≠ -n) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I))
      {z : ℂ | 1 - z ∈ slitPlane} :=
  (differentiableOn_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow
    haσ hbσ hcab hσ).analyticOnNhd
      (isOpen_slitPlane.preimage (continuous_const.sub continuous_id))

/-- **Mellin–Barnes integral for Euler's hypergeometric integral in `1 - z` (DLMF 15.6.7).**
On the entire cut plane `1 - z ∈ Complex.slitPlane`, for any vertical line `Re s = σ` separating
the left-opening poles of `Γ(a + s) Γ(b + s)` from the right-opening poles of
`Γ(c - a - b - s) Γ(-s)` (`-min(Re a, Re b) < σ < min(0, Re(c - a - b))`),
`Complex.eulerIntegral a b c z = (2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫_ℝ Γ(a + s) Γ(b + s)
  Γ(c - a - b - s) Γ(-s) (1 - z)^s`. -/
theorem eulerIntegral_eq_mellinBarnes_one_sub {a b c z : ℂ} {σ : ℝ}
    (hz : 1 - z ∈ slitPlane) (hσ : σ < 0) (hcab : σ < (c - a - b).re)
    (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    eulerIntegral a b c z =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - z) ^ (σ + y * I) := by
  have ha : 0 < a.re := by linarith
  have hb : 0 < b.re := by linarith
  have hcb : 0 < (c - b).re := by simp only [sub_re] at hcab ⊢; linarith
  have hca : 0 < (c - a).re := by simp only [sub_re] at hcab ⊢; linarith
  have hbσ_pos : 0 < b.re + σ := by linarith
  have hcab_pos : 0 < (c - a - b).re - σ := by linarith
  have hσ_ne : ∀ n : ℕ, -σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  let s : ℝ → ℂ := fun y ↦ (σ : ℂ) + y * I
  let F : ℝ → ℝ → ℂ := fun t y ↦
    (t : ℂ) ^ (b + s y - 1) * (1 - (t : ℂ)) ^ (c - a - b - s y - 1) *
      (Gamma (a + s y) * Gamma (-s y) * (1 - z) ^ s y)
  -- Factor `1 - z t = (1 - t) (1 + (t / (1 - t)) (1 - z))` for `t ∈ (0, 1)` and apply the
  -- slit-plane Mellin–Barnes integral of `(1 + w) ^ (-a)`.
  have hpoint : ∫ t : ℝ in 0..1,
        Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      (2 * π : ℂ)⁻¹ * ∫ t : ℝ in 0..1, ∫ y : ℝ, F t y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Ioo_ae_eq_Ioc] with t ht ht_mem
    rw [uIoc_of_le zero_le_one] at ht_mem
    obtain ⟨ht0, ht1⟩ := ht.2 ht_mem
    have h1t : 0 < 1 - t := sub_pos.2 ht1
    have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
    have h1t_ne : (1 - (t : ℂ)) ≠ 0 := by
      rw [← ofReal_one, ← ofReal_sub]
      exact ofReal_ne_zero.2 h1t.ne'
    set q : ℝ := t / (1 - t)
    have hq : 0 < q := div_pos ht0 h1t
    have hqz : (q : ℂ) * (1 - z) ∈ slitPlane := TauCeti.ofReal_mul_mem_slitPlane hq hz
    have hfact : 1 - z * (t : ℂ) = ((1 - t : ℝ) : ℂ) * (1 + (q : ℂ) * (1 - z)) := by
      have h1t_ne' : ((1 - t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 h1t.ne'
      dsimp [q]
      push_cast
      field_simp [h1t_ne']
      ring
    have hcpow_fact : (1 - z * (t : ℂ)) ^ (-a) =
        (1 - (t : ℂ)) ^ (-a) * (1 + (q : ℂ) * (1 - z)) ^ (-a) := by
      rw [hfact, TauCeti.ofReal_mul_cpow h1t.le]
      push_cast
      rfl
    have hmb := integral_Gamma_add_mul_Gamma_neg_mul_cpow hσ haσ hqz
    rw [hcpow_fact]
    have hpull : Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          ((1 - (t : ℂ)) ^ (-a) * (1 + (q : ℂ) * (1 - z)) ^ (-a))) =
        ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - (t : ℂ)) ^ (-a)) *
          (Gamma a * (1 + (q : ℂ) * (1 - z)) ^ (-a)) := by ring
    rw [hpull, ← hmb, ← mul_left_comm ((2 * π : ℂ)⁻¹), ← integral_const_mul]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp [F, s]
    have hq_pow : (q : ℂ) ^ ((σ : ℂ) + y * I) =
        (t : ℂ) ^ ((σ : ℂ) + y * I) * (1 - (t : ℂ)) ^ (-((σ : ℂ) + y * I)) := by
      set u : ℂ := ((1 - t : ℝ) : ℂ) ^ ((σ : ℂ) + y * I)
      set v : ℂ := (((1 - t)⁻¹ : ℝ) : ℂ) ^ ((σ : ℂ) + y * I)
      set w : ℂ := (1 - (t : ℂ)) ^ (-((σ : ℂ) + y * I))
      have huv : u * v = 1 := by
        dsimp [u, v]
        rw [← TauCeti.ofReal_mul_cpow h1t.le, ← ofReal_mul, mul_inv_cancel₀ h1t.ne',
          ofReal_one, one_cpow]
      have huw : u * w = 1 := by
        dsimp [u, w]
        rw [ofReal_sub, ofReal_one, ← cpow_add _ _ h1t_ne, add_neg_cancel, cpow_zero]
      have hvw : v = w :=
        calc v = v * (u * w) := by rw [huw, mul_one]
          _ = (u * v) * w := by ring
          _ = w := by rw [huv, one_mul]
      have hq_eq : (q : ℂ) = (t : ℂ) * (((1 - t)⁻¹ : ℝ) : ℂ) := by
        dsimp [q]
        rw [div_eq_mul_inv, ofReal_mul]
      rw [hq_eq, TauCeti.ofReal_mul_cpow ht0.le]
      exact congrArg ((t : ℂ) ^ ((σ : ℂ) + y * I) * ·) hvw
    rw [TauCeti.ofReal_mul_cpow hq.le, hq_pow]
    have hpow_t : (t : ℂ) ^ (b - 1) * (t : ℂ) ^ ((σ : ℂ) + y * I) =
        (t : ℂ) ^ (b + ((σ : ℂ) + y * I) - 1) := by
      rw [← cpow_add _ _ ht_ne]
      congr 1
      ring
    have hpow_1t : (1 - (t : ℂ)) ^ (c - b - 1) * (1 - (t : ℂ)) ^ (-a) *
        (1 - (t : ℂ)) ^ (-((σ : ℂ) + y * I)) =
        (1 - (t : ℂ)) ^ (c - a - b - ((σ : ℂ) + y * I) - 1) := by
      rw [← cpow_add _ _ h1t_ne, ← cpow_add _ _ h1t_ne]
      congr 1
      ring
    linear_combination
      ((1 - (t : ℂ)) ^ (c - a - b - ((σ : ℂ) + y * I) - 1) *
        (Gamma (a + ((σ : ℂ) + y * I)) * Gamma (-((σ : ℂ) + y * I)) *
          (1 - z) ^ ((σ : ℂ) + y * I))) * hpow_t +
      ((t : ℂ) ^ (b - 1) * (t : ℂ) ^ ((σ : ℂ) + y * I) *
        (Gamma (a + ((σ : ℂ) + y * I)) * Gamma (-((σ : ℂ) + y * I)) *
          (1 - z) ^ ((σ : ℂ) + y * I))) * hpow_1t
  -- Check product integrability of `F` on `(0, 1] × ℝ` to swap the integrals.
  have hF_int : Integrable (uncurry F) ((volume.restrict (uIoc 0 1)).prod volume) := by
    have hmeas_oo : (volume.restrict (uIoc (0 : ℝ) 1)).prod (volume : Measure ℝ) =
        ((volume : Measure ℝ).prod volume).restrict (Ioo (0 : ℝ) 1 ×ˢ univ) := by
      rw [uIoc_of_le zero_le_one, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
      simpa only [Measure.restrict_univ] using
        Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (Ioo (0 : ℝ) 1) univ
    have hφ : Integrable (fun t : ℝ ↦
        ‖(t : ℂ) ^ (((b.re + σ : ℝ) : ℂ) - 1) *
          (1 - (t : ℂ)) ^ ((((c - a - b).re - σ : ℝ) : ℂ) - 1)‖)
        (volume.restrict (uIoc 0 1)) := by
      have hbeta := betaIntegral_convergent
        (u := ((b.re + σ : ℝ) : ℂ)) (v := (((c - a - b).re - σ : ℝ) : ℂ))
        (by simpa using hbσ_pos) (by simpa using hcab_pos)
      exact (intervalIntegrable_iff.1 hbeta).norm
    have hψ : Integrable (fun y : ℝ ↦ ‖Gamma (a + s y) * Gamma (-s y) * (1 - z) ^ s y‖) volume :=
      (integrable_Gamma_add_mul_Gamma_neg_mul_cpow hσ_ne haσ_ne hz).norm
    have hF_meas : AEStronglyMeasurable (uncurry F)
        ((volume.restrict (uIoc 0 1)).prod volume) := by
      rw [hmeas_oo]
      refine ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ).prod volume) ?_
        (measurableSet_Ioo.prod MeasurableSet.univ)
      rintro ⟨t, y⟩ ⟨⟨ht0, ht1⟩, -⟩
      have ht_slit : (t : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 ht0
      have h1t_slit : 1 - (t : ℂ) ∈ slitPlane := by
        rw [← ofReal_one, ← ofReal_sub]
        exact ofReal_mem_slitPlane.2 (sub_pos.2 ht1)
      refine ContinuousAt.continuousWithinAt ?_
      refine ((ContinuousAt.mul ?_ ?_).mul ((ContinuousAt.mul ?_ ?_).mul ?_))
      · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) ht_slit
      · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) h1t_slit
      · exact (differentiableAt_Gamma _ fun m hm ↦
          haσ_ne m (by simpa [s, add_re] using congrArg re hm)).continuousAt.comp (by fun_prop)
      · exact (differentiableAt_Gamma _ fun m hm ↦
          hσ_ne m (by simpa [s] using congrArg re hm)).continuousAt.comp (by fun_prop)
      · exact ContinuousAt.cpow continuousAt_const (by fun_prop) hz
    refine (hφ.mul_prod hψ).mono' hF_meas ?_
    rw [hmeas_oo]
    filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with
      ⟨t, y⟩ ⟨⟨ht0, ht1⟩, _⟩
    have ht0' : 0 < t := ht0
    have h1t : 0 < 1 - t := sub_pos.2 ht1
    dsimp [uncurry, F, s]
    rw [← ofReal_one, ← ofReal_sub]
    simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0', norm_cpow_eq_rpow_re_of_pos h1t,
      sub_re, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero]
    exact le_rfl
  -- Swap `∫_0^1` and `∫_ℝ` and evaluate the inner Beta integral.
  have hinner (y : ℝ) : ∫ t : ℝ in 0..1, F t y =
      (Gamma (a + s y) * Gamma (b + s y) * Gamma (c - a - b - s y) *
        Gamma (-s y) * (1 - z) ^ s y) / Gamma (c - a) := by
    dsimp [F]
    rw [intervalIntegral.integral_mul_const, ← betaIntegral,
      betaIntegral_eq_Gamma_mul_div (b + s y) (c - a - b - s y)
        (by simpa [s, add_re] using hbσ_pos) (by simpa [s, sub_re] using hcab_pos),
      show b + s y + (c - a - b - s y) = c - a by ring]
    ring
  rw [intervalIntegral.integral_const_mul, intervalIntegral_integral_swap hF_int] at hpoint
  simp_rw [hinner, integral_div] at hpoint
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hΓca : Gamma (c - a) ≠ 0 := Gamma_ne_zero_of_re_pos hca
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hI : (∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * t) ^ (-a)) =
      (Gamma a)⁻¹ * ((2 * π : ℂ)⁻¹ *
        ((∫ y : ℝ, Gamma (a + s y) * Gamma (b + s y) *
          Gamma (c - a - b - s y) * Gamma (-s y) * (1 - z) ^ s y) / Gamma (c - a))) := by
    rw [← hpoint, inv_mul_cancel_left₀ hΓa]
  rw [eulerIntegral_def, hI]
  dsimp only [s]
  generalize (∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
    Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I)) = J
  field_simp [hΓa, hΓb, hΓca, hΓcb, hpi]

/-- **Mellin–Barnes integral for `Complex.regularizedGaussHGFun` in `1 - z` (DLMF 15.6.7).**
On the open unit disk `‖z‖ < 1`, for `-min(Re a, Re b) < σ < min(0, Re(c - a - b))`,
`Complex.regularizedGaussHGFun a b c z = (2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫_ℝ Γ(a + s) Γ(b + s)
  Γ(c - a - b - s) Γ(-s) (1 - z)^s`, proved by expanding `(1 - w)^s` on `‖w‖ < 1 / 2` in its
multichoose binomial series, integrating termwise via Barnes's first lemma, and continuing
analytically across `‖z‖ < 1`. -/
theorem regularizedGaussHGFun_eq_mellinBarnes_one_sub {a b c z : ℂ} {σ : ℝ}
    (hz : ‖z‖ < 1) (hσ : σ < 0) (hcab : σ < (c - a - b).re)
    (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    regularizedGaussHGFun a b c z =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - z) ^ (σ + y * I) := by
  have ha : 0 < a.re := by linarith
  have hb : 0 < b.re := by linarith
  have hcb : 0 < (c - b).re := by simp only [sub_re] at hcab ⊢; linarith
  have hca : 0 < (c - a).re := by simp only [sub_re] at hcab ⊢; linarith
  have haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hbσ_ne : ∀ n : ℕ, b.re + σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hcab_ne : ∀ n : ℕ, (c - a - b).re - σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hσ_ne : ∀ n : ℕ, -σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  let s : ℝ → ℂ := fun y ↦ (σ : ℂ) + y * I
  let g : ℝ → ℂ := fun y ↦
    Gamma (a + s y) * Gamma (b + s y) * Gamma (c - a - b - s y) * Gamma (-s y)
  let M : ℂ := (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹
  let RHS : ℂ → ℂ := fun w ↦ M * ∫ y : ℝ, g y * (1 - w) ^ s y
  have hball_slit : Metric.ball (0 : ℂ) 1 ⊆ {w : ℂ | 1 - w ∈ slitPlane} := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    refine mem_slitPlane_iff.2 (Or.inl ?_)
    have := re_le_norm w
    simp only [sub_re, one_re]
    linarith
  have hanL : AnalyticOnNhd ℂ (regularizedGaussHGFun a b c) (Metric.ball 0 1) := fun w hw ↦
    analyticAt_regularizedHGFun_of_card_eq_add_one rfl (by simpa using hw)
  have hanR : AnalyticOnNhd ℂ RHS (Metric.ball 0 1) :=
    analyticOnNhd_const.mul
      ((analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_sub_mul_Gamma_neg_mul_one_sub_cpow
        haσ_ne hbσ_ne hcab_ne hσ_ne).mono hball_slit)
  -- Evaluate `RHS w` on the half-radius disk `‖w‖ < 1 / 2` by expanding `(1 - w) ^ s y` in its
  -- binomial series and applying Barnes's first lemma term by term.
  have hhalf : ∀ w ∈ Metric.ball (0 : ℂ) (1 / 2), regularizedGaussHGFun a b c w = RHS w := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hw1 : ‖w‖ < 1 := hw.trans (by norm_num)
    obtain ⟨hg_cont, C, hC, hg_bound⟩ :=
      continuous_and_norm_mellinBarnesOneSubKernel_le haσ_ne hbσ_ne hcab_ne hσ_ne
    let bound : ℕ → ℝ → ℝ := fun n y ↦ ‖g y‖ * (Ring.multichoose ‖s y‖ n * (1 / 2 : ℝ) ^ n)
    have hpoch_cont (n : ℕ) : Continuous fun z : ℂ ↦ (ascPochhammer ℂ n).eval z := by
      induction n with
      | zero =>
        simp only [ascPochhammer_zero, Polynomial.eval_one]
        exact continuous_const
      | succ n ih =>
        simp only [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_natCast]
        exact ih.mul (by fun_prop)
    have hmc_cont (n : ℕ) : Continuous fun y : ℝ ↦ Ring.multichoose (-s y) n := by
      have hfn : (fun y : ℝ ↦ Ring.multichoose (-s y) n) =
          fun y : ℝ ↦ (ascPochhammer ℂ n).eval (-s y) / (n ! : ℂ) := by
        ext y
        have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (-s y) n
        rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
        have hfac : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
        rw [eq_div_iff hfac, mul_comm, h]
      rw [hfn]
      exact ((hpoch_cont n).comp (by fun_prop)).div_const _
    have hF_meas (n : ℕ) :
        AEStronglyMeasurable (fun y : ℝ ↦ g y * (Ring.multichoose (-s y) n * w ^ n)) volume :=
      (hg_cont.mul ((hmc_cont n).mul continuous_const)).aestronglyMeasurable
    have h_bound (n : ℕ) : ∀ᵐ y : ℝ ∂volume,
        ‖g y * (Ring.multichoose (-s y) n * w ^ n)‖ ≤ bound n y := by
      refine Eventually.of_forall fun y ↦ ?_
      dsimp only [bound]
      rw [norm_mul (g y), norm_mul (Ring.multichoose (-s y) n), norm_pow]
      have hmc : ‖Ring.multichoose (-s y) n‖ ≤ Ring.multichoose ‖s y‖ n := by
        simpa only [norm_neg] using TauCeti.norm_multichoose_le (-s y) n
      have hmc_nn : 0 ≤ Ring.multichoose ‖s y‖ n := (norm_nonneg _).trans hmc
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hmc (pow_le_pow_left₀ (norm_nonneg w) hw.le n)
          (pow_nonneg (norm_nonneg w) n) hmc_nn)
        (norm_nonneg _)
    have h_mc_sum (y : ℝ) : HasSum (fun n : ℕ ↦ Ring.multichoose ‖s y‖ n * (1 / 2 : ℝ) ^ n)
        (1 / (1 - (1 / 2 : ℝ)) ^ ‖s y‖) :=
      TauCeti.hasSum_multichoose_mul_geometric_of_abs_lt_one (by norm_num)
    have bound_summable : ∀ᵐ y : ℝ ∂volume, Summable fun n : ℕ ↦ bound n y :=
      Eventually.of_forall fun y ↦ (h_mc_sum y).summable.mul_left ‖g y‖
    have bound_integrable : Integrable (fun y : ℝ ↦ ∑' n : ℕ, bound n y) volume := by
      set α : ℝ := 2 * π - Real.log 2
      have hα : 0 < α := by
        have hlog2 : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
        have hpi : (2 : ℝ) ≤ π := Real.two_le_pi
        dsimp [α]
        linarith
      have htsum_cont : Continuous fun y : ℝ ↦ ∑' n : ℕ, bound n y := by
        have hfn : (fun y : ℝ ↦ ∑' n : ℕ, bound n y) =
            fun y : ℝ ↦ ‖g y‖ * (1 / (1 - (1 / 2 : ℝ)) ^ ‖s y‖) := by
          ext y
          dsimp [bound]
          rw [tsum_mul_left, (h_mc_sum y).tsum_eq]
        rw [hfn]
        refine hg_cont.norm.mul (continuous_const.div ?_ fun y ↦ by positivity)
        exact continuous_const.rpow (by fun_prop) fun _ ↦ Or.inl (by norm_num)
      refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs hα
        (c.re - 2)).const_mul (C * 2 ^ |σ|)).mono' htsum_cont.aestronglyMeasurable
        (Eventually.of_forall fun y ↦ ?_)
      have htsum_eq : (∑' n : ℕ, bound n y) = ‖g y‖ * 2 ^ ‖s y‖ := by
        dsimp [bound]
        rw [tsum_mul_left, (h_mc_sum y).tsum_eq, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num,
          one_div, ← Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 1 / 2),
          show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
      have h2pow : (2 : ℝ) ^ ‖s y‖ ≤ 2 ^ |σ| * Real.exp (Real.log 2 * |y|) := by
        have hsy : ‖s y‖ ≤ |σ| + |y| := by
          dsimp [s]
          exact (norm_add_le _ _).trans_eq (by simp)
        calc (2 : ℝ) ^ ‖s y‖
            ≤ 2 ^ (|σ| + |y|) := Real.rpow_le_rpow_of_exponent_le one_le_two hsy
          _ = 2 ^ |σ| * 2 ^ |y| := Real.rpow_add two_pos _ _
          _ = 2 ^ |σ| * Real.exp (Real.log 2 * |y|) := by
              nth_rw 2 [Real.rpow_def_of_pos two_pos]
      have hnonneg : 0 ≤ ∑' n : ℕ, bound n y := by
        rw [htsum_eq]
        positivity
      rw [Real.norm_of_nonneg hnonneg, htsum_eq]
      calc ‖g y‖ * 2 ^ ‖s y‖
          ≤ (C * (1 + |y|) ^ (c.re - 2) * Real.exp (-2 * π * |y|)) *
              (2 ^ |σ| * Real.exp (Real.log 2 * |y|)) :=
            mul_le_mul (hg_bound y) h2pow (by positivity) (by positivity)
        _ = C * 2 ^ |σ| * (1 + |y|) ^ (c.re - 2) *
              (Real.exp (-2 * π * |y|) * Real.exp (Real.log 2 * |y|)) := by ring
        _ = C * 2 ^ |σ| * ((1 + |y|) ^ (c.re - 2) * Real.exp (-α * |y|)) := by
            rw [← Real.exp_add]
            dsimp [α]
            ring_nf
    have h_lim : ∀ᵐ y : ℝ ∂volume,
        HasSum (fun n : ℕ ↦ g y * (Ring.multichoose (-s y) n * w ^ n))
          (g y * (1 - w) ^ s y) := by
      refine Eventually.of_forall fun y ↦ ?_
      have hbin := TauCeti.hasSum_multichoose_mul_geometric_complex_of_norm_lt_one
        (r := -s y) hw1
      rw [one_div, cpow_neg, inv_inv] at hbin
      exact hbin.mul_left (g y)
    have hswap := hasSum_integral_of_dominated_convergence bound hF_meas h_bound
      bound_summable bound_integrable h_lim
    -- Evaluate the `n`-th integral by Barnes's first lemma.
    have hterm (n : ℕ) : M * ∫ y : ℝ, g y * (Ring.multichoose (-s y) n * w ^ n) =
        ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b) /
          (n ! * Gamma (c + n)) * w ^ n := by
      have hbarnes := integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub
        (a := a) (b := b) (c := c - a - b) (d := (n : ℂ)) (σ := σ)
        haσ hbσ hcab (by simp; linarith [n.cast_nonneg (α := ℝ)])
      have hint_eq : (∫ y : ℝ, g y * (Ring.multichoose (-s y) n * w ^ n)) =
          (w ^ n / (n ! : ℂ)) * ∫ y : ℝ,
            Gamma (a + s y) * Gamma (b + s y) *
              Gamma (c - a - b - s y) * Gamma ((n : ℂ) - s y) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
        have hns : ∀ k : ℕ, -s y ≠ -k :=
          ne_neg_natCast_of_re_pos (by simp [s]; linarith)
        have hmc := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (-s y) n
        rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval,
          ← Gamma_add_nat_div_Gamma_eq (-s y) hns] at hmc
        have hfac : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
        have hΓns : Gamma (-s y) ≠ 0 := Gamma_ne_zero hns
        have hmc' : Gamma (-s y) * Ring.multichoose (-s y) n =
            Gamma ((n : ℂ) - s y) / (n ! : ℂ) := by
          rw [show (n : ℂ) - s y = -s y + n by ring]
          rw [eq_div_iff hfac]
          calc Gamma (-s y) * Ring.multichoose (-s y) n * (n ! : ℂ)
              = Gamma (-s y) * ((n ! : ℂ) * Ring.multichoose (-s y) n) := by ring
            _ = Gamma (-s y) * (Gamma (-s y + n) / Gamma (-s y)) := by rw [hmc]
            _ = Gamma (-s y + n) := mul_div_cancel₀ _ hΓns
        dsimp [g]
        calc Gamma (a + s y) * Gamma (b + s y) * Gamma (c - a - b - s y) * Gamma (-s y) *
              (Ring.multichoose (-s y) n * w ^ n)
            = Gamma (a + s y) * Gamma (b + s y) * Gamma (c - a - b - s y) *
                (Gamma (-s y) * Ring.multichoose (-s y) n) * w ^ n := by ring
          _ = Gamma (a + s y) * Gamma (b + s y) * Gamma (c - a - b - s y) *
                (Gamma ((n : ℂ) - s y) / (n ! : ℂ)) * w ^ n := by rw [hmc']
          _ = w ^ n / (n ! : ℂ) * (Gamma (a + s y) * Gamma (b + s y) *
                Gamma (c - a - b - s y) * Gamma ((n : ℂ) - s y)) := by ring
      have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
      have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
      have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
      have hΓca : Gamma (c - a) ≠ 0 := Gamma_ne_zero_of_re_pos hca
      have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
      have hbarnes' : (∫ y : ℝ, Gamma (a + s y) * Gamma (b + s y) *
            Gamma (c - a - b - s y) * Gamma ((n : ℂ) - s y)) =
          (2 * π : ℂ) * (Gamma (c - b) * Gamma (a + n) * Gamma (c - a) *
            Gamma (b + n) / Gamma (c + n)) := by
        have e1 : a + (c - a - b) = c - b := by ring
        have e2 : b + (c - a - b) = c - a := by ring
        have e3 : a + b + (c - a - b) + (n : ℂ) = c + n := by ring
        rw [e1, e2, e3] at hbarnes
        dsimp [s]
        rw [← hbarnes, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]
      have hpa := Gamma_add_nat_div_Gamma_eq (n := n) a (ne_neg_natCast_of_re_pos ha)
      have hpb := Gamma_add_nat_div_Gamma_eq (n := n) b (ne_neg_natCast_of_re_pos hb)
      rw [hint_eq, hbarnes']
      dsimp [M]
      rw [← hpa, ← hpb]
      field_simp [hpi, hΓa, hΓb, hΓca, hΓcb]
    have hRHS_sum : HasSum (fun n : ℕ ↦
        ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b) /
          (n ! * Gamma (c + n)) * w ^ n) (RHS w) := by
      have hm := hswap.mul_left M
      convert hm using 1
      ext n
      exact (hterm n).symm
    have hLHS_sum : HasSum (fun n : ℕ ↦
        ((ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b) /
          (n ! * Gamma (c + n)) * w ^ n) (regularizedGaussHGFun a b c w) := by
      have hmem : w ∈ Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries a b c).radius :=
        Metric.eball_subset_eball (radius_regularizedGaussHGFunSeries_ge_one a b c)
          (by rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one])
      rw [regularizedGaussHGFun]
      convert (regularizedGaussHGFunSeries a b c).hasSum hmem using 1
      ext n
      have hcoeff := coeff_regularizedGaussHGFunSeries (a := a) (b := b) (c := c) (n := n)
      rw [regularizedGaussHGFunSeries, regularizedHGFunSeries,
        FormalMultilinearSeries.ofScalars_apply_eq]
      rw [regularizedGaussHGFunSeries, regularizedHGFunSeries,
        FormalMultilinearSeries.coeff_ofScalars] at hcoeff
      rw [smul_eq_mul, hcoeff]
    exact hLHS_sum.unique hRHS_sum
  have heq : EqOn (regularizedGaussHGFun a b c) RHS (Metric.ball 0 1) :=
    hanL.eqOn_of_preconnected_of_eventuallyEq hanR (convex_ball (0 : ℂ) 1).isPreconnected
      (Metric.mem_ball_self one_pos)
      (Filter.eventually_of_mem (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 1 / 2)) hhalf)
  exact heq (by simpa using hz)

/-- **Mellin–Barnes integral for `₂F₁` in `1 - z` on the open unit disk (DLMF 15.6.7).** -/
theorem ordinaryHypergeometric_eq_mellinBarnes_one_sub {a b c z : ℂ} {σ : ℝ}
    (hc : ∀ k : ℕ, c ≠ -k) (hz : ‖z‖ < 1) (hσ : σ < 0)
    (hcab : σ < (c - a - b).re) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    ordinaryHypergeometric a b c z =
      Gamma c * (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - z) ^ (σ + y * I) := by
  have hΓc : Gamma c ≠ 0 := Gamma_ne_zero hc
  have hreg := regularizedGaussHGFun_eq_mellinBarnes_one_sub
    (a := a) (b := b) (c := c) hz hσ hcab haσ hbσ
  rw [← ordinaryHypergeometric_div_Gamma_eq hc, div_eq_iff hΓc] at hreg
  linear_combination hreg

end Complex

end
