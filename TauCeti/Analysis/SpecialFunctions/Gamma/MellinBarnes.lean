/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import TauCeti.Analysis.MellinInversion
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.MellinTransform.Convolution
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical

/-!
# Mellin–Barnes integral of `(1 + z)^{-a}` and Barnes's first lemma

For complex parameters `0 < Re s < Re a`, the half-line Euler beta integral
[DLMF 5.12.3](https://dlmf.nist.gov/5.12.E3) expresses the Mellin transform of `t ↦ (1 + t)^{-a}` on
`(0, ∞)` as `Γ(s) Γ(a - s) / Γ(a)`: writing `Γ(a) (1 + x)^{-a} = ∫₀^∞ t^{a-1} e^{-t} e^{-xt} dt`
reduces the transform to the multiplicative convolution identity
`TauCeti.hasMellin_integral_mul_comp_mul`.

Along any vertical line `Re s = σ` avoiding the poles of `Γ(s)` and `Γ(a - s)`, Stirling's vertical
estimates (`TauCeti.exists_norm_Gamma_vertical_line_le` and
`TauCeti.exists_norm_Gamma_sub_mul_I_le`) give `‖Γ(σ + i y) Γ(a - σ - i y)‖ =
O((1 + |y|)^{Re a - 1} e^{-π |y|})`. Mellin inversion recovers `Γ(a) (1 + x)^{-a}` for `x > 0` when
`0 < σ < Re a`, and the slit-plane holomorphy of the Mellin–Barnes kernel
(`TauCeti.analyticOnNhd_integral_cpow_neg_smul_slitPlane`) together with the positive-axis identity
principle `AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq` continues the identity to the whole cut
plane `z ∈ Complex.slitPlane`:

`(2π)⁻¹ ∫_ℝ Γ(σ + i y) Γ(a - σ - i y) z^{-(σ + i y)} dy = Γ(a) (1 + z)^{-a}`.

Inserting this representation of `Γ(b + d) (1 + u)^{-(b + d)}` (translated along the vertical line
to `s = d - i y`) against `u^{a + d - 1} (1 + u)^{-(a + c)}` on `(0, ∞)` and exchanging the order of
integration by Fubini's theorem yields Barnes's first lemma
([DLMF 5.13.3](https://dlmf.nist.gov/5.13.E3)): for `a, b, c, d : ℂ` in the open right half-plane,

`(2π)⁻¹ ∫_ℝ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`.

## Main results

* `Complex.hasMellin_one_add_cpow_neg`, `Complex.integrableOn_cpow_mul_one_add_cpow_Ioi`,
  `Complex.integral_cpow_mul_one_add_cpow_Ioi`: the Mellin transform of `(1 + t)^{-a}` on `(0, ∞)`
  (DLMF 5.12.3).
* `Complex.verticalIntegrable_Gamma_mul_Gamma_sub`,
  `Complex.integrable_Gamma_mul_Gamma_sub_mul_cpow_neg`,
  `Complex.integrable_Gamma_add_mul_Gamma_neg_mul_cpow`: vertical integrability of
  `Γ(s) Γ(a - s)` and its slit-plane Mellin–Barnes integrands.
* `Complex.mellinInv_Gamma_mul_Gamma_sub`, `Complex.integral_Gamma_mul_Gamma_sub_mul_cpow_neg`,
  `Complex.integral_Gamma_add_mul_Gamma_neg_mul_cpow`: the Mellin–Barnes integral representation of
  `Γ(a) (1 + z)^{-a}` on `Complex.slitPlane`, in both sign conventions.
* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`,
  `Complex.integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma`,
  `Complex.integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub`: Barnes's first lemma
  (DLMF 5.13.3) and its shifted-contour corollary.

## References

* [NIST Digital Library of Mathematical Functions, §5.12.3 and §5.13.3](https://dlmf.nist.gov/5.13).
* E. T. Whittaker and G. N. Watson, *A Course of Modern Analysis*, §14.51–14.52.
-/

public section

open Real Set MeasureTheory Filter Topology Function
open Complex hiding exp continuous_exp

namespace Complex

/-! ### Mellin transform of `(1 + t)^{-a}` (DLMF 5.12.3) -/

/-- **DLMF 5.12.3** as a Mellin transform: for `0 < Re s < Re a`, the function
`t ↦ (1 + (t : ℂ)) ^ (-a)` on `(0, ∞)` has Mellin transform `Γ(s) Γ(a - s) / Γ(a)`. -/
theorem hasMellin_one_add_cpow_neg {a s : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re) :
    HasMellin (fun t : ℝ ↦ (1 + (t : ℂ)) ^ (-a)) s (Gamma s * Gamma (a - s) / Gamma a) := by
  have ha : 0 < a.re := hs.trans hsa
  have has_pos : 0 < (a - s).re := by simp [sub_re, hsa]
  let h : ℝ → ℂ := fun t ↦ (Real.exp (-t) : ℂ)
  let f : ℝ → ℂ := fun t ↦ (t : ℂ) ^ (a - 1) • h t
  have hh_conv {w : ℂ} (hw : 0 < w.re) : MellinConvergent h w := by
    refine (GammaIntegral_convergent hw).congr_fun (fun u _ ↦ ?_) measurableSet_Ioi
    simp [h, smul_eq_mul, mul_comm]
  have hh_mel {w : ℂ} (hw : 0 < w.re) : mellin h w = Gamma w := by
    rw [Gamma_eq_integral hw, GammaIntegral_eq_mellin]
  have hf_conv : MellinConvergent f (1 - s) := by
    rw [MellinConvergent.cpow_smul, show 1 - s + (a - 1) = a - s by ring]
    exact hh_conv has_pos
  have hf_mel : mellin f (1 - s) = Gamma (a - s) := by
    rw [mellin_cpow_smul, show 1 - s + (a - 1) = a - s by ring, hh_mel has_pos]
  have hconv := TauCeti.hasMellin_integral_mul_comp_mul (f := f) (h := h) (z := s)
    hf_conv (hh_conv hs)
  rw [hf_mel, hh_mel hs] at hconv
  have hlaplace (x : ℝ) (hx : 0 < x) :
      (∫ t in Ioi 0, f t * h (x * t)) = Gamma a * (1 + (x : ℂ)) ^ (-a) := by
    have h1x : 0 < 1 + x := by linarith
    have heq : EqOn (fun t : ℝ ↦ f t * h (x * t))
        (fun t : ℝ ↦ (t : ℂ) ^ (a - 1) * Complex.exp (-(((1 + x : ℝ) : ℂ) * t))) (Ioi 0) := by
      intro t _
      dsimp [f, h]
      rw [mul_assoc, ← ofReal_mul, ← Real.exp_add, ofReal_exp]
      congr 2
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi heq, integral_cpow_mul_exp_neg_mul_Ioi ha h1x]
    have harg : arg ((1 + x : ℝ) : ℂ) ≠ Real.pi := by
      rw [arg_ofReal_of_nonneg h1x.le]
      exact Real.pi_pos.ne
    rw [one_div, inv_cpow _ _ harg, ← cpow_neg, ofReal_add, ofReal_one, mul_comm]
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hscaled : HasMellin (fun x : ℝ ↦ Gamma a * (1 + (x : ℂ)) ^ (-a)) s
      (Gamma (a - s) * Gamma s) := by
    refine ⟨hconv.1.congr_fun (fun x hx ↦ ?_) measurableSet_Ioi, ?_⟩
    · dsimp only [smul_eq_mul]
      rw [hlaplace x hx]
    · rw [← hconv.2]
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
      dsimp only [smul_eq_mul]
      rw [hlaplace x hx]
  have hdiv := hasMellin_const_smul hscaled.1 (Gamma a)⁻¹
  rw [hscaled.2] at hdiv
  refine ⟨hdiv.1.congr_fun (fun x _ ↦ ?_) measurableSet_Ioi, ?_⟩
  · simp [smul_eq_mul, inv_mul_cancel_left₀ hΓa]
  · calc mellin (fun t : ℝ ↦ (1 + (t : ℂ)) ^ (-a)) s
        = mellin (fun t : ℝ ↦ (Gamma a)⁻¹ • (Gamma a * (1 + (t : ℂ)) ^ (-a))) s := by
          refine setIntegral_congr_fun measurableSet_Ioi fun x _ ↦ ?_
          simp [smul_eq_mul, inv_mul_cancel_left₀ hΓa]
      _ = (Gamma a)⁻¹ • (Gamma (a - s) * Gamma s) := hdiv.2
      _ = Gamma s * Gamma (a - s) / Gamma a := by
          rw [smul_eq_mul]
          ring

/-- For `0 < Re s < Re a`, the complex Euler beta integrand `t^{s-1} (1 + t)^{-a}` is integrable on
`(0, ∞)`. -/
theorem integrableOn_cpow_mul_one_add_cpow_Ioi {a s : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re) :
    IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ (s - 1) * (1 + (t : ℂ)) ^ (-a)) (Ioi 0) := by
  simpa only [MellinConvergent, smul_eq_mul] using (hasMellin_one_add_cpow_neg hs hsa).1

/-- **Complex Euler second beta integral (DLMF 5.12.3)**: for `0 < Re s < Re a`,
`∫₀^∞ t^{s-1} (1 + t)^{-a} dt = Γ(s) Γ(a - s) / Γ(a)`. -/
theorem integral_cpow_mul_one_add_cpow_Ioi {a s : ℂ} (hs : 0 < s.re) (hsa : s.re < a.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) * (1 + (t : ℂ)) ^ (-a) =
      Gamma s * Gamma (a - s) / Gamma a := by
  simpa only [mellin, smul_eq_mul] using (hasMellin_one_add_cpow_neg hs hsa).2

/-! ### Mellin–Barnes integral of `(1 + z)^{-a}` on the slit plane -/

/-- Continuity and `O((1 + |y|)^{Re a - 1} e^{-π |y|})` decay of `y ↦ Γ(σ + i y) Γ(a - σ - i y)`
along any vertical line `Re s = σ` avoiding the poles of both Gamma factors. -/
private theorem continuous_and_norm_Gamma_mul_Gamma_sub_le {a : ℂ} {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ -n) (haσ : ∀ n : ℕ, a.re - σ ≠ -n) :
    Continuous (fun y : ℝ ↦ Gamma (σ + y * I) * Gamma (a - (σ + y * I))) ∧
      ∃ C > 0, ∀ y : ℝ, ‖Gamma (σ + y * I) * Gamma (a - (σ + y * I))‖ ≤
        C * (1 + |y|) ^ (a.re - 1) * Real.exp (-π * |y|) := by
  have hcont : Continuous fun y : ℝ ↦ Gamma (σ + y * I) * Gamma (a - (σ + y * I)) := by
    refine Continuous.mul (continuous_iff_continuousAt.2 fun y ↦ ?_)
      (continuous_iff_continuousAt.2 fun y ↦ ?_)
    · exact (differentiableAt_Gamma _ fun m hm ↦
        hσ m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
    · exact (differentiableAt_Gamma _ fun m hm ↦
        haσ m (by simpa [sub_re] using congrArg re hm)).continuousAt.comp (by fun_prop)
  obtain ⟨C₁, hC₁, h₁⟩ := TauCeti.exists_norm_Gamma_vertical_line_le hσ
  obtain ⟨C₂, hC₂, h₂⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le (z := a - σ)
    (by simpa [sub_re] using haσ)
  refine ⟨hcont, C₁ * C₂, mul_pos hC₁ hC₂, fun y ↦ ?_⟩
  have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
  have hsub : a - ((σ : ℂ) + y * I) = a - σ - y * I := by ring
  have h2y := h₂ y
  simp only [sub_re, ofReal_re] at h2y
  rw [hsub, norm_mul]
  calc ‖Gamma (σ + y * I)‖ * ‖Gamma (a - σ - y * I)‖
      ≤ (C₁ * (1 + |y|) ^ (σ - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₂ * (1 + |y|) ^ (a.re - σ - 1 / 2) * Real.exp (-π * |y| / 2)) :=
        mul_le_mul (h₁ y) h2y (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * ((1 + |y|) ^ (σ - 1 / 2) * (1 + |y|) ^ (a.re - σ - 1 / 2)) *
          (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2)) := by ring
    _ = C₁ * C₂ * (1 + |y|) ^ (a.re - 1) * Real.exp (-π * |y|) := by
        rw [← Real.rpow_add h1y, ← Real.exp_add]
        have hr : σ - 1 / 2 + (a.re - σ - 1 / 2) = a.re - 1 := by ring
        have he : -π * |y| / 2 + -π * |y| / 2 = -π * |y| := by ring
        rw [hr, he]

/-- Along any vertical line `Re s = σ` avoiding the poles of `Γ(s)` and `Γ(a - s)`, the product
`s ↦ Γ(s) Γ(a - s)` is vertically integrable. -/
theorem verticalIntegrable_Gamma_mul_Gamma_sub {a : ℂ} {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ -n) (haσ : ∀ n : ℕ, a.re - σ ≠ -n) :
    VerticalIntegrable (fun s : ℂ ↦ Gamma s * Gamma (a - s)) σ := by
  obtain ⟨hcont, C, _, hbound⟩ := continuous_and_norm_Gamma_mul_Gamma_sub_le hσ haσ
  refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs Real.pi_pos
    (a.re - 1)).const_mul C).mono' hcont.aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  exact (hbound y).trans_eq (by ring)

/-- For `z ∈ Complex.slitPlane` and `σ : ℝ` avoiding the poles of `Γ(s)` and `Γ(a - s)`, the
Mellin–Barnes integrand `y ↦ Γ(σ + i y) Γ(a - (σ + i y)) z^{-(σ + i y)}` is integrable on `ℝ`. -/
theorem integrable_Gamma_mul_Gamma_sub_mul_cpow_neg {a z : ℂ} {σ : ℝ}
    (hσ : ∀ n : ℕ, σ ≠ -n) (haσ : ∀ n : ℕ, a.re - σ ≠ -n) (hz : z ∈ slitPlane) :
    Integrable fun y : ℝ ↦ Gamma (σ + y * I) * Gamma (a - (σ + y * I)) * z ^ (-(σ + y * I)) := by
  obtain ⟨hcont, C, _, hbound⟩ := continuous_and_norm_Gamma_mul_Gamma_sub_le hσ haσ
  have h := TauCeti.integrable_cpow_neg_smul_of_norm_le_exp_neg_pi_mul_abs
    hcont.aestronglyMeasurable ⟨C, a.re - 1, hbound⟩ σ hz
  exact h.congr (Eventually.of_forall fun y ↦ by simp [smul_eq_mul, mul_comm, mul_assoc])

/-- Mellin inversion of `s ↦ Γ(s) Γ(a - s)` on `Re s = σ` (`0 < σ < Re a`) recovers
`Γ(a) (1 + x)^{-a}` for `x > 0`. -/
theorem mellinInv_Gamma_mul_Gamma_sub {a : ℂ} {σ x : ℝ} (hσ : 0 < σ) (hσa : σ < a.re)
    (hx : 0 < x) :
    mellinInv σ (fun s : ℂ ↦ Gamma s * Gamma (a - s)) x = Gamma a * (1 + (x : ℂ)) ^ (-a) := by
  have ha : 0 < a.re := hσ.trans hσa
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  let φ : ℝ → ℂ := fun t ↦ (1 + (t : ℂ)) ^ (-a)
  have hline (y : ℝ) : mellin φ (σ + y * I) =
      (Gamma (σ + y * I) * Gamma (a - (σ + y * I))) / Gamma a :=
    (hasMellin_one_add_cpow_neg (by simpa using hσ) (by simpa using hσa)).2
  have hσ_ne : ∀ n : ℕ, σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have haσ_ne : ∀ n : ℕ, a.re - σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hV : VerticalIntegrable (mellin φ) σ := by
    unfold VerticalIntegrable
    simp_rw [hline]
    exact (verticalIntegrable_Gamma_mul_Gamma_sub hσ_ne haσ_ne).div_const (Gamma a)
  have hφ_cont : ContinuousAt φ x := by
    refine ContinuousAt.cpow (by fun_prop) continuousAt_const ?_
    exact TauCeti.ofReal_add_mem_slitPlane_of_mem_union (Or.inl (ofReal_mem_slitPlane.2 hx))
      zero_lt_one
  have hinv := mellinInv_mellin_eq σ φ hx
    (hasMellin_one_add_cpow_neg (by simpa using hσ) (by simpa using hσa)).1 hV hφ_cont
  have hpull : mellinInv σ (mellin φ) x =
      (Gamma a)⁻¹ * mellinInv σ (fun s ↦ Gamma s * Gamma (a - s)) x := by
    unfold mellinInv
    simp_rw [hline, smul_eq_mul, ← mul_div_assoc, integral_div]
    rw [real_smul, real_smul]
    ring
  rw [hpull] at hinv
  exact (inv_mul_eq_iff_eq_mul₀ hΓa).1 hinv

/-- **Mellin–Barnes integral representation of `(1 + z)^{-a}`** on the slit plane: for
`0 < σ < Re a` and `z ∈ Complex.slitPlane`,
`(2π)⁻¹ ∫_ℝ Γ(σ + i y) Γ(a - (σ + i y)) z^{-(σ + i y)} dy = Γ(a) (1 + z)^{-a}`. -/
theorem integral_Gamma_mul_Gamma_sub_mul_cpow_neg {a z : ℂ} {σ : ℝ} (hσ : 0 < σ) (hσa : σ < a.re)
    (hz : z ∈ slitPlane) :
    (2 * π : ℂ)⁻¹ *
        ∫ y : ℝ, Gamma (σ + y * I) * Gamma (a - (σ + y * I)) * z ^ (-(σ + y * I)) =
      Gamma a * (1 + z) ^ (-a) := by
  have hσ_ne : ∀ n : ℕ, σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have haσ_ne : ∀ n : ℕ, a.re - σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg (α := ℝ)]
  obtain ⟨hcont, C, _, hbound⟩ := continuous_and_norm_Gamma_mul_Gamma_sub_le hσ_ne haσ_ne
  let L : ℂ → ℂ := fun w ↦ (2 * π : ℂ)⁻¹ *
    ∫ y : ℝ, Gamma (σ + y * I) * Gamma (a - (σ + y * I)) * w ^ (-(σ + y * I))
  let R : ℂ → ℂ := fun w ↦ Gamma a * (1 + w) ^ (-a)
  have hanL : AnalyticOnNhd ℂ L slitPlane := by
    refine analyticOnNhd_const.mul ?_
    refine (TauCeti.analyticOnNhd_integral_cpow_neg_smul_slitPlane hcont.aestronglyMeasurable
      ⟨C, a.re - 1, hbound⟩ σ).congr isOpen_slitPlane fun w _ ↦ ?_
    exact integral_congr_ae (Eventually.of_forall fun y ↦ by
      simp [smul_eq_mul, mul_comm, mul_assoc])
  have hanR : AnalyticOnNhd ℂ R slitPlane := by
    refine DifferentiableOn.analyticOnNhd (fun w hw ↦ ?_) isOpen_slitPlane
    have h1w : 1 + w ∈ slitPlane := by
      simpa using TauCeti.ofReal_add_mem_slitPlane hw zero_le_one
    exact (((differentiableAt_id.const_add 1).cpow (differentiableAt_const _) h1w).const_mul
      _).differentiableWithinAt
  have hreal (r : ℝ) (hr : 0 < r) : L r = R r := by
    have hm := mellinInv_Gamma_mul_Gamma_sub hσ hσa hr
    unfold mellinInv at hm
    rw [real_smul] at hm
    dsimp [L, R]
    rw [← hm]
    push_cast
    rw [one_div]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y ↦ by
      simp [smul_eq_mul, mul_comm, mul_assoc])
  exact hanL.eqOn_slitPlane_of_ofReal_pos_eq hanR hreal hz

/-- Positive-exponent companion to `Complex.integrable_Gamma_mul_Gamma_sub_mul_cpow_neg`:
`y ↦ Γ(a + (σ + i y)) Γ(-(σ + i y)) z^{σ + i y}` is integrable on `ℝ` whenever `-σ` and
`Re a + σ` avoid the nonpositive integers and `z ∈ Complex.slitPlane`. -/
theorem integrable_Gamma_add_mul_Gamma_neg_mul_cpow {a z : ℂ} {σ : ℝ}
    (hσ : ∀ n : ℕ, -σ ≠ -n) (haσ : ∀ n : ℕ, a.re + σ ≠ -n) (hz : z ∈ slitPlane) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * z ^ ((σ : ℂ) + y * I) := by
  have h := integrable_Gamma_mul_Gamma_sub_mul_cpow_neg (a := a) (z := z) (σ := -σ)
    hσ (by simpa [sub_neg_eq_add] using haσ) hz
  refine h.comp_neg.congr (Eventually.of_forall fun y ↦ ?_)
  dsimp only [Function.comp_def]
  rw [ofReal_neg, ofReal_neg]
  have e1 : -(σ : ℂ) + -(y : ℂ) * I = -((σ : ℂ) + y * I) := by ring
  rw [e1, sub_neg_eq_add, neg_neg, mul_comm (Gamma _)]

/-- Positive-exponent form of the Mellin–Barnes integral of `(1 + z)^{-a}`: for `-Re a < σ < 0` and
`z ∈ Complex.slitPlane`,
`(2π)⁻¹ ∫_ℝ Γ(a + (σ + i y)) Γ(-(σ + i y)) z^{σ + i y} dy = Γ(a) (1 + z)^{-a}`. -/
theorem integral_Gamma_add_mul_Gamma_neg_mul_cpow {a z : ℂ} {σ : ℝ} (hσ : σ < 0)
    (haσ : -a.re < σ) (hz : z ∈ slitPlane) :
    (2 * π : ℂ)⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * z ^ (σ + y * I) =
      Gamma a * (1 + z) ^ (-a) := by
  have h := integral_Gamma_mul_Gamma_sub_mul_cpow_neg (a := a) (z := z) (σ := -σ)
    (neg_pos.2 hσ) (by linarith) hz
  rw [← h]
  congr 1
  rw [← integral_neg_eq_self]
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  rw [ofReal_neg, ofReal_neg]
  have e1 : -((σ : ℂ) + -(y : ℂ) * I) = -(σ : ℂ) + (y : ℂ) * I := by ring
  have e2 : a + ((σ : ℂ) + -(y : ℂ) * I) = a - (-(σ : ℂ) + (y : ℂ) * I) := by ring
  have e3 : (σ : ℂ) + -(y : ℂ) * I = -(-(σ : ℂ) + (y : ℂ) * I) := by ring
  rw [e1, e2, e3, mul_comm (Gamma _)]

/-! ### Barnes's first lemma (DLMF 5.13.3) -/

/-- The four-Gamma integrand `y ↦ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y)` of Barnes's first
lemma is integrable on `ℝ` whenever the real parts of `a`, `b`, `c`, `d` avoid the nonpositive
integers. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ}
    (ha : ∀ n : ℕ, a.re ≠ -n) (hb : ∀ n : ℕ, b.re ≠ -n)
    (hc : ∀ n : ℕ, c.re ≠ -n) (hd : ∀ n : ℕ, d.re ≠ -n) :
    Integrable fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
  obtain ⟨C₁, hC₁, h₁⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le ha
  obtain ⟨C₂, hC₂, h₂⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le hb
  obtain ⟨C₃, hC₃, h₃⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hc
  obtain ⟨C₄, _, h₄⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hd
  have hcont : Continuous fun y : ℝ ↦
      Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I) := by
    have hc_add {z : ℂ} (hz : ∀ n : ℕ, z.re ≠ -n) : Continuous fun y : ℝ ↦ Gamma (z + y * I) :=
      continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          hz m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
    have hc_sub {z : ℂ} (hz : ∀ n : ℕ, z.re ≠ -n) : Continuous fun y : ℝ ↦ Gamma (z - y * I) :=
      continuous_iff_continuousAt.2 fun y ↦
        (differentiableAt_Gamma _ fun m hm ↦
          hz m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
    exact (((hc_add ha).mul (hc_add hb)).mul (hc_sub hc)).mul (hc_sub hd)
  refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs
    (show 0 < 2 * π by positivity) (a.re + b.re + c.re + d.re - 2)).const_mul
    (C₁ * C₂ * C₃ * C₄)).mono' hcont.aestronglyMeasurable (Eventually.of_forall fun y ↦ ?_)
  have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
  rw [norm_mul, norm_mul, norm_mul]
  calc ‖Gamma (a + y * I)‖ * ‖Gamma (b + y * I)‖ * ‖Gamma (c - y * I)‖ * ‖Gamma (d - y * I)‖
      ≤ (C₁ * (1 + |y|) ^ (a.re - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₂ * (1 + |y|) ^ (b.re - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₃ * (1 + |y|) ^ (c.re - 1 / 2) * Real.exp (-π * |y| / 2)) *
          (C₄ * (1 + |y|) ^ (d.re - 1 / 2) * Real.exp (-π * |y| / 2)) := by
        refine mul_le_mul
          (mul_le_mul (mul_le_mul (h₁ y) (h₂ y) (norm_nonneg _) (by positivity)) (h₃ y)
            (norm_nonneg _) (by positivity))
          (h₄ y) (norm_nonneg _) (by positivity)
    _ = C₁ * C₂ * C₃ * C₄ *
          ((1 + |y|) ^ (a.re - 1 / 2) * (1 + |y|) ^ (b.re - 1 / 2) *
            (1 + |y|) ^ (c.re - 1 / 2) * (1 + |y|) ^ (d.re - 1 / 2)) *
          (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2) *
            Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2)) := by ring
    _ = C₁ * C₂ * C₃ * C₄ *
          ((1 + |y|) ^ (a.re + b.re + c.re + d.re - 2) * Real.exp (-(2 * π) * |y|)) := by
        rw [← Real.rpow_add h1y, ← Real.rpow_add h1y, ← Real.rpow_add h1y,
          ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        ring_nf

/-- **Barnes's first lemma (DLMF 5.13.3)**: for `a, b, c, d : ℂ` in the open right half-plane,
`(2π)⁻¹ ∫_ℝ Γ(a + i y) Γ(b + i y) Γ(c - i y) Γ(d - i y) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma {a b c d : ℂ} (ha : 0 < a.re)
    (hb : 0 < b.re) (hc : 0 < c.re) (hd : 0 < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) *
        Gamma (d - y * I) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have hb_ne : ∀ n : ℕ, b.re ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hd_ne : ∀ n : ℕ, d.re ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have hbd_mb (u : ℝ) (hu : 0 < u) :
      Gamma (b + d) * (1 + (u : ℂ)) ^ (-(b + d)) =
        (2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (b + y * I) * Gamma (d - y * I) * (u : ℂ) ^ (y * I - d) := by
    have hmb := integral_Gamma_mul_Gamma_sub_mul_cpow_neg (a := b + d) (z := (u : ℂ)) (σ := d.re)
      hd (by simp [add_re, hb]) (ofReal_mem_slitPlane.2 hu)
    rw [← hmb]
    congr 1
    rw [← integral_sub_left_eq_self _ volume d.im]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    have hd_eq : (d.re : ℂ) + ((d.im - y : ℝ) : ℂ) * I = d - y * I := by
      apply Complex.ext <;> simp
    rw [hd_eq, show b + d - (d - y * I) = b + y * I by ring,
      show -(d - y * I) = y * I - d by ring, mul_comm (Gamma (d - y * I))]
  let F : ℝ → ℝ → ℂ := fun u y ↦
    Gamma (b + y * I) * Gamma (d - y * I) *
      ((u : ℂ) ^ (a + y * I - 1) * (1 + (u : ℂ)) ^ (-(a + c)))
  -- Product-measure integrability on `(0, ∞) × ℝ` via factored real majorants.
  have hF_int : Integrable (uncurry F) ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    have hφ : Integrable (fun u : ℝ ↦ ‖(u : ℂ) ^ ((a.re : ℂ) - 1) *
        (1 + (u : ℂ)) ^ (-((a.re + c.re : ℝ) : ℂ))‖) (volume.restrict (Ioi 0)) :=
      (integrableOn_cpow_mul_one_add_cpow_Ioi (s := a.re) (a := (a.re + c.re : ℝ))
        (by simpa using ha) (by simp [hc])).norm
    obtain ⟨C₁, hC₁, h₁⟩ := TauCeti.exists_norm_Gamma_add_mul_I_le hb_ne
    obtain ⟨C₂, _, h₂⟩ := TauCeti.exists_norm_Gamma_sub_mul_I_le hd_ne
    have hψ_cont : Continuous fun y : ℝ ↦ ‖Gamma (b + y * I) * Gamma (d - y * I)‖ := by
      refine Continuous.norm (Continuous.mul (continuous_iff_continuousAt.2 fun y ↦ ?_)
        (continuous_iff_continuousAt.2 fun y ↦ ?_))
      · exact (differentiableAt_Gamma _ fun m hm ↦
          hb_ne m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
      · exact (differentiableAt_Gamma _ fun m hm ↦
          hd_ne m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
    have hψ : Integrable (fun y : ℝ ↦ ‖Gamma (b + y * I) * Gamma (d - y * I)‖) volume := by
      refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs Real.pi_pos
        (b.re + d.re - 1)).const_mul (C₁ * C₂)).mono' hψ_cont.aestronglyMeasurable
        (Eventually.of_forall fun y ↦ ?_)
      have h1y : 0 < 1 + |y| := by linarith [abs_nonneg y]
      rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul]
      calc ‖Gamma (b + y * I)‖ * ‖Gamma (d - y * I)‖
          ≤ (C₁ * (1 + |y|) ^ (b.re - 1 / 2) * Real.exp (-π * |y| / 2)) *
              (C₂ * (1 + |y|) ^ (d.re - 1 / 2) * Real.exp (-π * |y| / 2)) :=
            mul_le_mul (h₁ y) (h₂ y) (norm_nonneg _) (by positivity)
        _ = C₁ * C₂ * ((1 + |y|) ^ (b.re - 1 / 2) * (1 + |y|) ^ (d.re - 1 / 2)) *
              (Real.exp (-π * |y| / 2) * Real.exp (-π * |y| / 2)) := by ring
        _ = C₁ * C₂ * ((1 + |y|) ^ (b.re + d.re - 1) * Real.exp (-π * |y|)) := by
            rw [← Real.rpow_add h1y, ← Real.exp_add]
            ring_nf
    have hmeas_eq : (volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure ℝ) =
        ((volume : Measure ℝ).prod volume).restrict (Ioi (0 : ℝ) ×ˢ univ) := by
      simpa only [Measure.restrict_univ] using
        Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (Ioi (0 : ℝ)) univ
    have hF_meas : AEStronglyMeasurable (uncurry F)
        ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
      rw [hmeas_eq]
      refine ContinuousOn.aestronglyMeasurable (μ := (volume : Measure ℝ).prod volume) ?_
        (measurableSet_Ioi.prod MeasurableSet.univ)
      rintro ⟨u, y⟩ ⟨hu : 0 < u, -⟩
      have hu_slit : (u : ℂ) ∈ slitPlane := ofReal_mem_slitPlane.2 hu
      have h1u_slit : 1 + (u : ℂ) ∈ slitPlane := by
        simpa using TauCeti.ofReal_add_mem_slitPlane hu_slit zero_le_one
      refine ContinuousAt.continuousWithinAt ?_
      refine ContinuousAt.mul (ContinuousAt.mul ?_ ?_) (ContinuousAt.mul ?_ ?_)
      · exact (differentiableAt_Gamma _ fun m hm ↦
          hb_ne m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
      · exact (differentiableAt_Gamma _ fun m hm ↦
          hd_ne m (by simpa using congrArg re hm)).continuousAt.comp (by fun_prop)
      · exact ContinuousAt.cpow (by fun_prop) (by fun_prop) hu_slit
      · exact ContinuousAt.cpow (by fun_prop) continuousAt_const h1u_slit
    refine (hφ.mul_prod hψ).mono' hF_meas ?_
    rw [hmeas_eq]
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with ⟨u, y⟩ ⟨hu, _⟩
    have hu' : 0 < u := hu
    have h1u : 0 < 1 + u := by linarith
    dsimp [uncurry, F]
    rw [norm_mul, norm_mul, norm_mul, norm_mul, ← ofReal_one, ← ofReal_add,
      norm_cpow_eq_rpow_re_of_pos hu', norm_cpow_eq_rpow_re_of_pos h1u,
      norm_cpow_eq_rpow_re_of_pos hu', norm_cpow_eq_rpow_re_of_pos h1u]
    simp only [sub_re, add_re, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one,
      sub_self, add_zero, neg_re]
    ring_nf
    exact le_rfl
  -- Evaluate `∫_{u > 0} ∫_y F u y` both ways via `integral_integral_swap`.
  have hLHS : (2 * π : ℂ)⁻¹ * ∫ u in Ioi (0 : ℝ), ∫ y : ℝ, F u y =
      Gamma (b + d) * (Gamma (a + d) * Gamma (b + c) / Gamma (a + b + c + d)) := by
    have hinner (u : ℝ) (hu : 0 < u) :
        (2 * π : ℂ)⁻¹ * ∫ y : ℝ, F u y =
          Gamma (b + d) * ((u : ℂ) ^ (a + d - 1) * (1 + (u : ℂ)) ^ (-(a + b + c + d))) := by
      have hu_ne : (u : ℂ) ≠ 0 := ofReal_ne_zero.2 hu.ne'
      have h1u_ne : 1 + (u : ℂ) ≠ 0 := by
        rw [← ofReal_one, ← ofReal_add]
        exact ofReal_ne_zero.2 (by linarith)
      have hpull : (∫ y : ℝ, F u y) =
          ((u : ℂ) ^ (a + d - 1) * (1 + (u : ℂ)) ^ (-(a + c))) *
            ∫ y : ℝ, Gamma (b + y * I) * Gamma (d - y * I) * (u : ℂ) ^ (y * I - d) := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
        dsimp [F]
        have hpow : (u : ℂ) ^ (a + d - 1) * (u : ℂ) ^ (y * I - d) = (u : ℂ) ^ (a + y * I - 1) := by
          rw [← cpow_add _ _ hu_ne]
          congr 1
          ring
        rw [← hpow]
        ring
      have h1pow : (1 + (u : ℂ)) ^ (-(a + c)) * (1 + (u : ℂ)) ^ (-(b + d)) =
          (1 + (u : ℂ)) ^ (-(a + b + c + d)) := by
        rw [← cpow_add _ _ h1u_ne]
        congr 1
        ring
      rw [hpull, ← mul_left_comm ((u : ℂ) ^ (a + d - 1) * _), ← hbd_mb u hu]
      linear_combination Gamma (b + d) * (u : ℂ) ^ (a + d - 1) * h1pow
    rw [← integral_const_mul, setIntegral_congr_fun measurableSet_Ioi hinner, integral_const_mul,
      integral_cpow_mul_one_add_cpow_Ioi (s := a + d) (a := a + b + c + d)
        (by simp [add_re]; linarith) (by simp [add_re]; linarith),
      show a + b + c + d - (a + d) = b + c by ring]
  have hRHS : (2 * π : ℂ)⁻¹ * ∫ y : ℝ, ∫ u in Ioi (0 : ℝ), F u y =
      ((2 * π : ℂ)⁻¹ * ∫ y : ℝ,
        Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)) /
          Gamma (a + c) := by
    have hinner (y : ℝ) :
        ∫ u in Ioi (0 : ℝ), F u y =
          (Gamma (a + y * I) * Gamma (b + y * I) * Gamma (c - y * I) * Gamma (d - y * I)) /
            Gamma (a + c) := by
      dsimp [F]
      rw [integral_const_mul,
        integral_cpow_mul_one_add_cpow_Ioi (s := a + y * I) (a := a + c)
          (by simpa using ha) (by simp [add_re, hc]),
        show a + c - (a + y * I) = c - y * I by ring]
      ring
    simp_rw [hinner, integral_div, mul_div_assoc]
  have hswap : (2 * π : ℂ)⁻¹ * ∫ u in Ioi (0 : ℝ), ∫ y : ℝ, F u y =
      (2 * π : ℂ)⁻¹ * ∫ y : ℝ, ∫ u in Ioi (0 : ℝ), F u y := by
    rw [integral_integral_swap hF_int]
  rw [hLHS, hRHS] at hswap
  have hΓac : Gamma (a + c) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp [add_re]; linarith)
  rw [eq_div_iff hΓac] at hswap
  rw [← hswap]
  ring

/-- Shifted-contour form of Barnes's first lemma: on any vertical line `Re s = σ` separating the
left-opening poles `-a - ℕ`, `-b - ℕ` from the right-opening poles `c + ℕ`, `d + ℕ`
(that is, `-Re a < σ`, `-Re b < σ`, `σ < Re c`, `σ < Re d`),
`(2π)⁻¹ ∫_ℝ Γ(a + (σ + i y)) Γ(b + (σ + i y)) Γ(c - (σ + i y)) Γ(d - (σ + i y)) dy =
  Γ(a + c) Γ(a + d) Γ(b + c) Γ(b + d) / Γ(a + b + c + d)`. -/
theorem integral_Gamma_add_mul_Gamma_add_mul_Gamma_sub_mul_Gamma_sub {a b c d : ℂ} {σ : ℝ}
    (ha : -a.re < σ) (hb : -b.re < σ) (hc : σ < c.re) (hd : σ < d.re) :
    (2 * π : ℂ)⁻¹ * ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - (σ + y * I)) * Gamma (d - (σ + y * I)) =
      Gamma (a + c) * Gamma (a + d) * Gamma (b + c) * Gamma (b + d) / Gamma (a + b + c + d) := by
  have h := integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma
    (a := a + σ) (b := b + σ) (c := c - σ) (d := d - σ)
    (by simp [add_re]; linarith) (by simp [add_re]; linarith)
    (by simp [sub_re]; linarith) (by simp [sub_re]; linarith)
  have e1 : a + σ + (c - σ) = a + c := by ring
  have e2 : a + σ + (d - σ) = a + d := by ring
  have e3 : b + σ + (c - σ) = b + c := by ring
  have e4 : b + σ + (d - σ) = b + d := by ring
  have e5 : a + σ + (b + σ) + (c - σ) + (d - σ) = a + b + c + d := by ring
  rw [e1, e2, e3, e4, e5] at h
  rw [← h]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  dsimp only
  have s1 : a + ((σ : ℂ) + y * I) = a + σ + y * I := by ring
  have s2 : b + ((σ : ℂ) + y * I) = b + σ + y * I := by ring
  have s3 : c - ((σ : ℂ) + y * I) = c - σ - y * I := by ring
  have s4 : d - ((σ : ℂ) + y * I) = d - σ - y * I := by ring
  rw [s1, s2, s3, s4]

end Complex
