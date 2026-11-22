/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Basic
public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.MellinInversion
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.MeasureTheory.Integral.Prod

/-!
# Mellin–Barnes integrals for the Gauss hypergeometric function

Two classical Mellin–Barnes vertical-line integrals represent the Gauss hypergeometric family along
vertical lines `Re s = σ` separating left and right sequences of Gamma poles:

* **DLMF 15.6.6** in powers of `-z`, holomorphic on the cut plane `{z | -z ∈ Complex.slitPlane}`:
  `(2π Γ(a) Γ(b))⁻¹ ∫ Γ(a + s) Γ(b + s) Γ(-s) Γ(c + s)⁻¹ (-z)^s dy`,
  where `s = σ + i y` and `max (-Re a, -Re b) < σ < 0`.
* **DLMF 15.6.7** in powers of `1 - z`, holomorphic on `{z | 1 - z ∈ Complex.slitPlane}` (and
  absolutely integrable for every `z : ℂ`):
  `(2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫ Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s) (1 - z)^s dy`,
  where `s = σ + i y` and `max (-Re a, -Re b) < σ < min (0, Re (c - a - b))`.

This file proves convergence and holomorphy of both Mellin–Barnes integrals on their respective cut
planes, evaluates 15.6.6 against Euler's normalized integral `Complex.eulerIntegral` (`Re b < Re c`,
`-Re b < σ < 0`, `-z ∈ slitPlane`), evaluates 15.6.7 against `Complex.eulerIntegral` on the full
cut plane `{z | 1 - z ∈ slitPlane}`, and evaluates 15.6.7 against Mathlib's power series
`Complex.regularizedGaussHGFun` and `Complex.ordinaryHypergeometric` (`‖z‖ < 1`).

On any pole-free line `Re s = σ`, Stirling's vertical-strip bounds give
`O((1 + |y|)^K exp (-π |y|))` decay for the Gamma ratio in 15.6.6 locally uniformly in `c` (with
polynomial exponent `K` depending on the `c`-ball) and `O((1 + |y|)^K exp (-2π |y|))` decay for the
four-Gamma product in 15.6.7 at fixed `(a, b, c)`. Combined with `|arg w| < π` on `slitPlane` (and
`|arg w| ≤ π` on `ℂ`), this yields integrability and holomorphy across the respective cut planes
(jointly in `(c, z)` for 15.6.6).

When `Re b < Re c` and `max (-Re a, -Re b) < σ < 0` (so `0 < Re b < Re c`), inserting the
slit-plane binomial Mellin–Barnes integral `Complex.integral_Gamma_add_mul_Gamma_neg_mul_cpow`
at `t * (-z)` into `Complex.eulerIntegral` and swapping integrations by Fubini's theorem
evaluates Euler's integral to 15.6.6 across the whole cut plane `-z ∈ slitPlane`.
Similarly, inserting the slit-plane binomial Mellin–Barnes integral
`Complex.integral_Gamma_add_mul_Gamma_neg_mul_cpow` into `Complex.eulerIntegral` at
`1 - z * t = (1 - t) (1 + (t / (1 - t)) (1 - z))` and swapping integrations evaluates
`Complex.eulerIntegral` to 15.6.7 on the entire cut plane `1 - z ∈ slitPlane`.

Restricting 15.6.7 to the open unit disk `‖z‖ < 1` and combining it with
`Complex.regularizedGaussHGFun_eq_eulerIntegral` gives the Mellin–Barnes representations for
`Complex.regularizedGaussHGFun` and `Complex.ordinaryHypergeometric` on `‖z‖ < 1`.

## Main results

* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_inv_Gamma_mul_neg_cpow`,
  `Complex.analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_mul_inv_Gamma_mul_neg_cpow`:
  convergence and joint `(c, z)`-holomorphy of the Mellin–Barnes integral 15.6.6 on
  `{p | -p.2 ∈ slitPlane}`.
* `Complex.eulerIntegral_eq_mellinBarnes`: equality of `Complex.eulerIntegral` and the
  Mellin–Barnes integral 15.6.6 on `{z | -z ∈ slitPlane}` when `Re b < Re c` and
  `max (-Re a, -Re b) < σ < 0`.
* `Complex.integrable_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow`,
  `Complex.analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_mul_Gamma_mul_one_sub_cpow`:
  convergence (for all `z : ℂ`) and `z`-holomorphy (on `{z | 1 - z ∈ slitPlane}`) of the
  Mellin–Barnes integral 15.6.7.
* `Complex.eulerIntegral_eq_mellinBarnes_one_sub`: equality of `Complex.eulerIntegral` and the
  Mellin–Barnes integral 15.6.7 on the entire cut plane `{z | 1 - z ∈ slitPlane}`.
* `Complex.regularizedGaussHGFun_eq_mellinBarnes_one_sub`,
  `Complex.ordinaryHypergeometric_eq_mellinBarnes_one_sub`: equality of the regularized and
  ordinary Gauss series with the Mellin–Barnes integral 15.6.7 on the open unit disk `‖z‖ < 1`.

## References

* NIST Digital Library of Mathematical Functions, §15.6, equations
  [15.6.6](https://dlmf.nist.gov/15.6.E6) and [15.6.7](https://dlmf.nist.gov/15.6.E7).
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
      Ca * (1 + |y|) ^ Ka * Real.exp (-(π / 2) * |y|) := by
    simpa only [← add_assoc] using (hba y).trans_eq (by congr 2; ring)
  have h2 : ‖Gamma (b + (σ + y * I))‖ ≤
      Cb * (1 + |y|) ^ Kb * Real.exp (-(π / 2) * |y|) := by
    simpa only [← add_assoc] using (hbb y).trans_eq (by congr 2; ring)
  have h3 : ‖Gamma (-((σ : ℂ) + y * I))‖ ≤
      Cs * (1 + |y|) ^ Ks * Real.exp (-(π / 2) * |y|) := by
    rw [neg_add']
    exact (hbs y).trans_eq (by congr 2; ring)
  have h12 := TauCeti.mul_le_mul_one_add_abs_rpow_mul_exp (norm_nonneg _) (norm_nonneg _) h1 h2
  have h123 := TauCeti.mul_le_mul_one_add_abs_rpow_mul_exp
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _) h12 h3
  rw [norm_mul, norm_mul]
  refine h123.trans_eq ?_
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

/-- Continuity in `y` of the integrand of the Mellin–Barnes representation 15.6.6. -/
private theorem continuous_mellinBarnesIntegrand {a b : ℂ} (c z : ℂ) (hz : -z ∈ slitPlane)
    {σ : ℝ} (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hσ : ∀ n : ℕ, σ ≠ n) :
    Continuous fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ ((σ : ℂ) + y * I) := by
  have hGc : Continuous fun y : ℝ ↦ (Gamma (c + (σ + y * I)))⁻¹ :=
    differentiable_one_div_Gamma.continuous.comp (by fun_prop)
  have hpow : Continuous fun y : ℝ ↦ (-z) ^ ((σ : ℂ) + y * I) :=
    continuous_const.cpow (by fun_prop) (fun _ ↦ hz)
  exact ((continuous_three_Gamma ha hb hσ).mul hGc).mul hpow

/-- On every vertical line `Re s = σ` avoiding the poles of `Γ(a + s)`, `Γ(b + s)`, and `Γ(-s)`,
the Mellin–Barnes integrand of DLMF 15.6.6 is integrable for every `c : ℂ` and `-z ∈ slitPlane`. -/
theorem integrable_Gamma_mul_Gamma_mul_Gamma_mul_inv_Gamma_mul_neg_cpow {a b : ℂ} (c : ℂ) {z : ℂ}
    (hz : -z ∈ slitPlane) {σ : ℝ} (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hσ : ∀ n : ℕ, σ ≠ n) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ ((σ : ℂ) + y * I) := by
  let g : ℝ → ℂ := fun y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
      (Gamma (c + (σ + y * I)))⁻¹
  have hg_meas : AEStronglyMeasurable g :=
    ((continuous_three_Gamma ha hb hσ).mul
      (differentiable_one_div_Gamma.continuous.comp (by fun_prop))).aestronglyMeasurable
  obtain ⟨Cg, _hCg, Kg, hbg⟩ := exists_norm_three_Gamma_le ha hb hσ
  obtain ⟨Cc, _hCc, hbc⟩ := TauCeti.exists_norm_inv_Gamma_and_deriv_ball_add_I_le (c + σ)
  set p : ℝ := 3 / 2 - (c + σ).re
  have hg_bound : ∃ C R : ℝ, ∀ᵐ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-π * |y|) := by
    refine ⟨Cg * Cc, Kg + p, Eventually.of_forall fun y ↦ ?_⟩
    have hbg' : ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
        Cg * (1 + |y|) ^ Kg * Real.exp (-(3 * π / 2) * |y|) :=
      (hbg y).trans_eq (by congr 2; ring)
    have hinv : ‖(Gamma (c + (σ + y * I)))⁻¹‖ ≤
        Cc * (1 + |y|) ^ p * Real.exp ((π / 2) * |y|) := by
      simpa only [← add_assoc] using
        ((hbc (c + σ) (mem_ball_self zero_lt_one) y).1).trans_eq (by congr 2; ring)
    dsimp [g]
    rw [norm_mul]
    refine (TauCeti.mul_le_mul_one_add_abs_rpow_mul_exp (norm_nonneg _) (norm_nonneg _)
      hbg' hinv).trans_eq ?_
    congr 2
    ring
  refine (TauCeti.integrable_cpow_smul_of_norm_le_exp_neg_mul_abs hg_meas hg_bound σ
    (abs_arg_lt_pi_of_mem_slitPlane hz)).congr (Eventually.of_forall fun y ↦ ?_)
  simp only [g, smul_eq_mul, mul_comm]

/-- Pointwise Fréchet derivative in `(c, z)` of the Mellin–Barnes integrand of DLMF 15.6.6. -/
private theorem hasFDerivAt_mellinBarnesIntegrand (g : ℂ) (σ y : ℝ) {p : ℂ × ℂ}
    (hzp : -p.2 ∈ slitPlane) :
    HasFDerivAt
      (fun q : ℂ × ℂ ↦ g * (Gamma (q.1 + (σ + y * I)))⁻¹ * (-q.2) ^ ((σ : ℂ) + y * I))
      ((g * deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p.1 + (σ + y * I)) *
          (-p.2) ^ ((σ : ℂ) + y * I)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (-(g * (Gamma (p.1 + (σ + y * I)))⁻¹ *
          (((σ : ℂ) + y * I) * (-p.2) ^ ((σ : ℂ) + y * I - 1)))) •
          ContinuousLinearMap.snd ℂ ℂ ℂ) p := by
  have hd1 : HasFDerivAt (fun q : ℂ × ℂ ↦ (Gamma (q.1 + (σ + y * I)))⁻¹)
      (deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p.1 + (σ + y * I)) •
        ContinuousLinearMap.fst ℂ ℂ ℂ) p := by
    have h1 := (differentiable_one_div_Gamma (p.1 + (σ + y * I))).hasDerivAt.comp_hasFDerivAt p
      ((hasFDerivAt_fst (𝕜 := ℂ)).add (hasFDerivAt_const ((σ : ℂ) + y * I) p))
    exact h1.congr_fderiv (by ext <;> simp)
  have hd2 : HasFDerivAt (fun q : ℂ × ℂ ↦ (-q.2) ^ ((σ : ℂ) + y * I))
      ((-(((σ : ℂ) + y * I) * (-p.2) ^ ((σ : ℂ) + y * I - 1))) •
        ContinuousLinearMap.snd ℂ ℂ ℂ) p := by
    have h2 := ((hasDerivAt_id' (-p.2)).cpow_const (c := (σ : ℂ) + y * I) hzp).comp_hasFDerivAt p
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt (x := p)).neg
    exact h2.congr_fderiv (by ext <;> simp)
  exact ((hd1.const_mul g).mul hd2).congr_fderiv (by ext <;> simp; ring)

/-- Pointwise norm bound on the Fréchet derivative of the 15.6.6 Mellin–Barnes integrand from
vertical-line bounds on its factors. -/
private theorem norm_fderiv_mellinBarnesIntegrand_le {g : ℂ} {σ y Cg Kg Cc p_exp M θ : ℝ}
    {p : ℂ × ℂ}
    (hg : ‖g‖ ≤ Cg * (1 + |y|) ^ Kg * Real.exp (-(3 * π * |y| / 2)))
    (hi : ‖(Gamma (p.1 + (σ + y * I)))⁻¹‖ ≤ Cc * (1 + |y|) ^ p_exp * Real.exp (π * |y| / 2))
    (hd : ‖deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p.1 + (σ + y * I))‖ ≤
      Cc * (1 + |y|) ^ (p_exp + 1) * Real.exp (π * |y| / 2))
    (hpow0 : ‖(-p.2) ^ ((σ : ℂ) + y * I)‖ ≤ M * Real.exp (θ * |y|))
    (hpow1 : ‖((σ : ℂ) + y * I) * (-p.2) ^ ((σ : ℂ) + y * I - 1)‖ ≤
      M * (1 + |y|) * Real.exp (θ * |y|)) :
    ‖(g * deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p.1 + (σ + y * I)) *
        (-p.2) ^ ((σ : ℂ) + y * I)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
      (-(g * (Gamma (p.1 + (σ + y * I)))⁻¹ *
        (((σ : ℂ) + y * I) * (-p.2) ^ ((σ : ℂ) + y * I - 1)))) •
        ContinuousLinearMap.snd ℂ ℂ ℂ‖ ≤
      Cg * Cc * M * (‖ContinuousLinearMap.fst ℂ ℂ ℂ‖ + ‖ContinuousLinearMap.snd ℂ ℂ ℂ‖ + 1) *
        ((1 + |y|) ^ (Kg + p_exp + 1) * Real.exp (-((π - θ) * |y|))) := by
  set W : ℝ := Cg * Cc * M * ((1 + |y|) ^ (Kg + p_exp + 1) * Real.exp (-((π - θ) * |y|)))
  have hg' : ‖g‖ ≤ Cg * (1 + |y|) ^ Kg * Real.exp (-(3 * π / 2) * |y|) :=
    hg.trans_eq (by congr 2; ring)
  have hprod {v w : ℂ} {q₁ q₂ : ℝ} (hq : q₁ + q₂ = p_exp + 1)
      (hv : ‖v‖ ≤ Cc * (1 + |y|) ^ q₁ * Real.exp ((π / 2) * |y|))
      (hw : ‖w‖ ≤ M * (1 + |y|) ^ q₂ * Real.exp (θ * |y|)) :
      ‖g * v * w‖ ≤ W := by
    have hgv := TauCeti.mul_le_mul_one_add_abs_rpow_mul_exp (norm_nonneg _) (norm_nonneg _) hg' hv
    have hgvw := TauCeti.mul_le_mul_one_add_abs_rpow_mul_exp
      (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _) hgv hw
    rw [norm_mul, norm_mul]
    refine hgvw.trans_eq ?_
    dsimp [W]
    rw [mul_assoc (Cg * Cc * M), add_assoc Kg q₁ q₂, hq]
    congr 3 <;> ring
  have hi' : ‖(Gamma (p.1 + (σ + y * I)))⁻¹‖ ≤
      Cc * (1 + |y|) ^ p_exp * Real.exp ((π / 2) * |y|) :=
    hi.trans_eq (by congr 2; ring)
  have hd' : ‖deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p.1 + (σ + y * I))‖ ≤
      Cc * (1 + |y|) ^ (p_exp + 1) * Real.exp ((π / 2) * |y|) :=
    hd.trans_eq (by congr 2; ring)
  have hterm1 := hprod (add_zero (p_exp + 1)) hd' (by simpa using hpow0)
  have hterm2 : ‖-(g * (Gamma (p.1 + (σ + y * I)))⁻¹ *
      (((σ : ℂ) + y * I) * (-p.2) ^ ((σ : ℂ) + y * I - 1)))‖ ≤ W := by
    rw [norm_neg]
    exact hprod rfl hi' (by simpa [Real.rpow_one] using hpow1)
  calc ‖(g * deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p.1 + (σ + y * I)) *
          (-p.2) ^ ((σ : ℂ) + y * I)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
        (-(g * (Gamma (p.1 + (σ + y * I)))⁻¹ *
          (((σ : ℂ) + y * I) * (-p.2) ^ ((σ : ℂ) + y * I - 1)))) •
          ContinuousLinearMap.snd ℂ ℂ ℂ‖
      ≤ ‖g * deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p.1 + (σ + y * I)) *
          (-p.2) ^ ((σ : ℂ) + y * I)‖ * ‖ContinuousLinearMap.fst ℂ ℂ ℂ‖ +
        ‖-(g * (Gamma (p.1 + (σ + y * I)))⁻¹ *
          (((σ : ℂ) + y * I) * (-p.2) ^ ((σ : ℂ) + y * I - 1)))‖ *
          ‖ContinuousLinearMap.snd ℂ ℂ ℂ‖ := by
          refine (norm_add_le _ _).trans ?_; rw [norm_smul, norm_smul]
    _ ≤ W * ‖ContinuousLinearMap.fst ℂ ℂ ℂ‖ + W * ‖ContinuousLinearMap.snd ℂ ℂ ℂ‖ := by gcongr
    _ ≤ W * (‖ContinuousLinearMap.fst ℂ ℂ ℂ‖ + ‖ContinuousLinearMap.snd ℂ ℂ ℂ‖ + 1) := by
          have hW0 : 0 ≤ W := (norm_nonneg _).trans hterm1
          nlinarith
    _ = Cg * Cc * M * (‖ContinuousLinearMap.fst ℂ ℂ ℂ‖ + ‖ContinuousLinearMap.snd ℂ ℂ ℂ‖ + 1) *
          ((1 + |y|) ^ (Kg + p_exp + 1) * Real.exp (-((π - θ) * |y|))) := by
          dsimp [W]; ring

/-- On every vertical line `Re s = σ` avoiding the poles of `Γ(a + s)`, `Γ(b + s)`, and `Γ(-s)`,
the Mellin–Barnes integral of DLMF 15.6.6 is jointly holomorphic in `(c, z)` on
`{p : ℂ × ℂ | -p.2 ∈ slitPlane}`. -/
theorem analyticOnNhd_integral_Gamma_mul_Gamma_mul_Gamma_mul_inv_Gamma_mul_neg_cpow {a b : ℂ}
    {σ : ℝ} (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    AnalyticOnNhd ℂ
      (fun p : ℂ × ℂ ↦ ∫ y : ℝ,
        Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
          (Gamma (p.1 + (σ + y * I)))⁻¹ * (-p.2) ^ ((σ : ℂ) + y * I))
      {p | -p.2 ∈ slitPlane} := by
  have hopen : IsOpen {p : ℂ × ℂ | -p.2 ∈ slitPlane} :=
    isOpen_slitPlane.preimage (continuous_neg.comp continuous_snd)
  refine DifferentiableOn.analyticOnNhd_of_finiteDimensional (fun p₀ hp₀ ↦ ?_) hopen
  let G : ℝ → ℂ := fun y ↦
    Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))
  let F : ℂ × ℂ → ℝ → ℂ := fun p y ↦
    G y * (Gamma (p.1 + (σ + y * I)))⁻¹ * (-p.2) ^ ((σ : ℂ) + y * I)
  let F' : ℂ × ℂ → ℝ → (ℂ × ℂ) →L[ℂ] ℂ := fun p y ↦
    (G y * deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p.1 + (σ + y * I)) *
        (-p.2) ^ ((σ : ℂ) + y * I)) • ContinuousLinearMap.fst ℂ ℂ ℂ +
      (-(G y * (Gamma (p.1 + (σ + y * I)))⁻¹ *
        (((σ : ℂ) + y * I) * (-p.2) ^ ((σ : ℂ) + y * I - 1)))) • ContinuousLinearMap.snd ℂ ℂ ℂ
  -- Local product neighborhood around `p₀` and dominating parameters.
  obtain ⟨Cg, _hCg, Kg, hbg⟩ := exists_norm_three_Gamma_le ha hb hσ
  obtain ⟨Cc, _hCc, hbc⟩ := TauCeti.exists_norm_inv_Gamma_and_deriv_ball_add_I_le (p₀.1 + σ)
  obtain ⟨ε, hε, θ, hθ, M, _hM, hball⟩ := TauCeti.exists_ball_slitPlane_cpow_le hp₀ σ
  let U : Set (ℂ × ℂ) := ball p₀.1 1 ×ˢ ((fun z : ℂ ↦ -z) ⁻¹' ball (-p₀.2) ε)
  have hU_nhds : U ∈ 𝓝 p₀ := prod_mem_nhds (ball_mem_nhds p₀.1 zero_lt_one)
    ((continuous_neg.continuousAt).eventually (ball_mem_nhds (-p₀.2) hε))
  set p_exp : ℝ := 3 / 2 - (p₀.1 + σ).re
  set C_dom : ℝ := Cg * Cc * M *
    (‖ContinuousLinearMap.fst ℂ ℂ ℂ‖ + ‖ContinuousLinearMap.snd ℂ ℂ ℂ‖ + 1)
  -- Measurability and dominated Fréchet differentiability under the integral sign.
  have hF_meas : ∀ᶠ p in 𝓝 p₀, AEStronglyMeasurable (F p) volume := by
    filter_upwards [hU_nhds] with p hp
    exact (continuous_mellinBarnesIntegrand p.1 p.2 (hball (-p.2) hp.2).1 ha hb hσ
      ).aestronglyMeasurable
  have hF'_meas : AEStronglyMeasurable (F' p₀) volume := by
    refine Continuous.aestronglyMeasurable ?_
    have hG_cont := continuous_three_Gamma ha hb hσ
    have hd_cont : Continuous fun y : ℝ ↦
        deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p₀.1 + (σ + y * I)) :=
      (differentiable_one_div_Gamma.contDiff.continuous_deriv le_rfl).comp (by fun_prop)
    have hi_cont : Continuous fun y : ℝ ↦ (Gamma (p₀.1 + (σ + y * I)))⁻¹ :=
      differentiable_one_div_Gamma.continuous.comp (by fun_prop)
    have hp1 : Continuous fun y : ℝ ↦ (-p₀.2) ^ ((σ : ℂ) + y * I) :=
      continuous_const.cpow (by fun_prop) (fun _ ↦ hp₀)
    have hp2 : Continuous fun y : ℝ ↦ (-p₀.2) ^ ((σ : ℂ) + y * I - 1) :=
      continuous_const.cpow (by fun_prop) (fun _ ↦ hp₀)
    exact (((hG_cont.mul hd_cont).mul hp1).smul continuous_const).add
      (((hG_cont.mul hi_cont).mul ((by fun_prop : Continuous fun y : ℝ ↦ (σ : ℂ) + y * I).mul
        hp2)).neg.smul continuous_const)
  have h_diff : ∀ᵐ y : ℝ, ∀ p ∈ U, HasFDerivAt (F · y) (F' p y) p :=
    Eventually.of_forall fun y _ hp ↦ hasFDerivAt_mellinBarnesIntegrand (G y) σ y
      (hball _ hp.2).1
  have h_bound : ∀ᵐ y : ℝ, ∀ p ∈ U,
      ‖F' p y‖ ≤ C_dom * ((1 + |y|) ^ (Kg + p_exp + 1) * Real.exp (-((π - θ) * |y|))) := by
    refine Eventually.of_forall fun y p hp ↦ ?_
    have hp1 : p.1 + σ ∈ ball (p₀.1 + σ) 1 := by
      simpa [mem_ball_iff_norm, add_sub_add_right_eq_sub] using hp.1
    have hp_exp : 5 / 2 - (p₀.1 + (σ : ℂ)).re = p_exp + 1 := by dsimp [p_exp]; ring
    obtain ⟨hi, hd⟩ := hbc (p.1 + σ) hp1 y
    rw [add_assoc] at hi hd
    rw [hp_exp] at hd
    exact norm_fderiv_mellinBarnesIntegrand_le (hbg y) hi hd
      ((hball (-p.2) hp.2).2.1 y) ((hball (-p.2) hp.2).2.2 y)
  have h_dom_int := (TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (Kg + p_exp + 1)
    (sub_pos.mpr hθ)).const_mul C_dom
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le hU_nhds hF_meas
    (integrable_Gamma_mul_Gamma_mul_Gamma_mul_inv_Gamma_mul_neg_cpow p₀.1 hp₀ ha hb hσ)
    hF'_meas h_bound h_dom_int h_diff).differentiableAt.differentiableWithinAt

/-- Product integrability on `(0, 1) × ℝ` of a Beta-weighted kernel
`(t, y) ↦ t^{u y - 1} (1 - t)^{v y - 1} g y`, where `u, v : ℝ → ℂ` are continuous with
constant positive real parts `u₀, v₀` and `g : ℝ → ℂ` is continuous and integrable on `ℝ`. -/
private theorem integrable_beta_mul_profile {u₀ v₀ : ℝ} {u v : ℝ → ℂ} {g : ℝ → ℂ}
    (hu_cont : Continuous u) (hv_cont : Continuous v)
    (hu_re : ∀ y, (u y).re = u₀) (hv_re : ∀ y, (v y).re = v₀)
    (hu₀ : 0 < u₀) (hv₀ : 0 < v₀) (hg_cont : Continuous g) (hg_int : Integrable g) :
    Integrable
      (fun p : ℝ × ℝ ↦ (p.1 : ℂ) ^ (u p.2 - 1) * (1 - (p.1 : ℂ)) ^ (v p.2 - 1) * g p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  have hmeas_oo : (volume.restrict (Ioo (0 : ℝ) 1)).prod (volume : Measure ℝ) =
      volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
    simpa [Measure.volume_eq_prod] using
      Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
        (Ioo 0 1) univ
  have hφ : Integrable
      (fun t : ℝ ↦ ‖(t : ℂ) ^ ((u₀ : ℂ) - 1) * (1 - (t : ℂ)) ^ ((v₀ : ℂ) - 1)‖)
      (volume.restrict (Ioo (0 : ℝ) 1)) := by
    have hb_conv := betaIntegral_convergent (u := u₀) (v := v₀) (by simpa using hu₀)
      (by simpa using hv₀)
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hb_conv
    exact (hb_conv.mono_set Ioo_subset_Ioc_self).norm
  have hF_meas : AEStronglyMeasurable
      (fun p : ℝ × ℝ ↦ (p.1 : ℂ) ^ (u p.2 - 1) * (1 - (p.1 : ℂ)) ^ (v p.2 - 1) * g p.2)
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
    rw [hmeas_oo]
    refine ContinuousOn.aestronglyMeasurable (fun ⟨t, y⟩ ⟨⟨ht0, ht1⟩, _⟩ ↦ ?_)
      (measurableSet_Ioo.prod MeasurableSet.univ)
    have h1t_slit : 1 - (t : ℂ) ∈ slitPlane := by
      rw [← ofReal_one, ← ofReal_sub]
      exact ofReal_mem_slitPlane.2 (sub_pos.2 ht1)
    exact (((ContinuousAt.cpow (by fun_prop) ((hu_cont.sub continuous_const).continuousAt.comp
        continuousAt_snd) (ofReal_mem_slitPlane.2 ht0)).mul
      (ContinuousAt.cpow (by fun_prop) ((hv_cont.sub continuous_const).continuousAt.comp
        continuousAt_snd) h1t_slit)).mul
      (hg_cont.continuousAt.comp continuousAt_snd)).continuousWithinAt
  refine (hφ.mul_prod hg_int.norm).mono' hF_meas ?_
  rw [hmeas_oo]
  filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod MeasurableSet.univ)] with
    ⟨t, y⟩ ⟨⟨ht0, ht1⟩, _⟩
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  rw [← ofReal_one, ← ofReal_sub]
  simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos ht0, norm_cpow_eq_rpow_re_of_pos h1t,
    sub_re, ofReal_re, hu_re, hv_re]
  exact le_rfl

/-- Product integrability on `(0, 1) × ℝ` for Beta-times-Mellin–Barnes integrands whose
exponents `u y` and `v y` have constant positive real parts `u₀` and `v₀`. -/
private theorem integrable_beta_mul_mellinBarnes {a w : ℂ} {σ u₀ v₀ : ℝ}
    {u v : ℝ → ℂ} (hu_cont : Continuous u) (hv_cont : Continuous v)
    (hu_re : ∀ y, (u y).re = u₀) (hv_re : ∀ y, (v y).re = v₀)
    (hu₀ : 0 < u₀) (hv₀ : 0 < v₀) (hσ_ne : ∀ n : ℕ, -σ ≠ -n)
    (haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n) (hw : w ∈ slitPlane) :
    Integrable (fun p : ℝ × ℝ ↦ (p.1 : ℂ) ^ (u p.2 - 1) * (1 - (p.1 : ℂ)) ^ (v p.2 - 1) *
        (Gamma (a + (σ + p.2 * I)) * Gamma (-(σ + p.2 * I)) * w ^ ((σ : ℂ) + p.2 * I)))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  have hG1 : Continuous fun y : ℝ ↦ Gamma (a + ((σ : ℂ) + y * I)) := by
    have harg (y : ℝ) : a + ((σ : ℂ) + y * I) = (a + σ) + y * I := by ring
    simpa only [harg] using
      continuous_Gamma_add_mul_I (w := a + σ) (by simpa [add_re] using haσ_ne)
  have hG2 : Continuous fun y : ℝ ↦ Gamma (-((σ : ℂ) + y * I)) := by
    have harg (y : ℝ) : -((σ : ℂ) + y * I) = ((-σ : ℝ) : ℂ) - y * I := by push_cast; ring
    simpa only [harg] using
      continuous_Gamma_sub_mul_I (w := (-σ : ℝ)) (by simpa using hσ_ne)
  exact integrable_beta_mul_profile hu_cont hv_cont hu_re hv_re hu₀ hv₀
    ((hG1.mul hG2).mul (continuous_const.cpow (by fun_prop) (fun _ ↦ hw)))
    (integrable_Gamma_add_mul_Gamma_neg_mul_cpow hσ_ne haσ_ne hw)

/-- **Mellin–Barnes integral for Euler's hypergeometric integral**
([DLMF 15.6.6](https://dlmf.nist.gov/15.6.E6)). For `Re b < Re c`, `-z ∈ slitPlane`, and any
vertical line `Re s = σ` with `max (-Re a, -Re b) < σ < 0` (which in particular forces
`0 < Re b < Re c`),
`eulerIntegral a b c z = (2π Γ(a) Γ(b))⁻¹ ∫ Γ(a + s) Γ(b + s) Γ(-s) Γ(c + s)⁻¹ (-z)^s dy`. -/
theorem eulerIntegral_eq_mellinBarnes (a : ℂ) {b c z : ℂ} (hbc : b.re < c.re)
    (hz : -z ∈ slitPlane) {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    eulerIntegral a b c z = (2 * π * Gamma a * Gamma b)⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ ((σ : ℂ) + y * I) := by
  have hb : 0 < b.re := by linarith
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hbσ_pos : 0 < b.re + σ := by linarith
  have hσ_ne : ∀ n : ℕ, -σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  let s : ℝ → ℂ := fun y ↦ (σ : ℂ) + y * I
  let F : ℝ → ℝ → ℂ := fun t y ↦
    (t : ℂ) ^ (b + s y - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
      (Gamma (a + s y) * Gamma (-s y) * (-z) ^ s y)
  -- Substitute the slit-plane Mellin–Barnes integral at `t * (-z)` pointwise on `(0, 1)`.
  have hpoint : ∫ t : ℝ in 0..1,
        Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      (2 * π : ℂ)⁻¹ * ∫ t : ℝ in 0..1, ∫ y : ℝ, F t y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Ioo_ae_eq_Ioc] with t ht ht_mem
    rw [uIoc_of_le zero_le_one] at ht_mem
    obtain ⟨ht0, _ht1⟩ := ht.2 ht_mem
    have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0.ne'
    have hmb := integral_Gamma_add_mul_Gamma_neg_mul_cpow hσ haσ
      (TauCeti.ofReal_mul_mem_slitPlane ht0 hz)
    have hbase : 1 + (t : ℂ) * (-z) = 1 - z * (t : ℂ) := by ring
    have hsplit (y : ℝ) :
        (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
          (Gamma (a + s y) * Gamma (-s y) * ((t : ℂ) * (-z)) ^ s y) = F t y := by
      have hexp : b - 1 + s y = b + s y - 1 := by ring
      dsimp [F]
      rw [TauCeti.ofReal_mul_cpow ht0.le]
      calc (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
            (Gamma (a + s y) * Gamma (-s y) * ((t : ℂ) ^ s y * (-z) ^ s y))
          = ((t : ℂ) ^ (b - 1) * (t : ℂ) ^ s y) * (1 - (t : ℂ)) ^ (c - b - 1) *
              (Gamma (a + s y) * Gamma (-s y) * (-z) ^ s y) := by ring
        _ = F t y := by rw [← cpow_add _ _ ht_ne, hexp]
    calc Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a))
        = ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
            (Gamma a * (1 + (t : ℂ) * (-z)) ^ (-a)) := by rw [hbase]; ring
      _ = ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
            ((2 * π : ℂ)⁻¹ * ∫ y : ℝ, Gamma (a + s y) * Gamma (-s y) *
              ((t : ℂ) * (-z)) ^ s y) := by rw [hmb]
      _ = (2 * π : ℂ)⁻¹ * ∫ y : ℝ, F t y := by
            rw [← mul_left_comm ((2 * π : ℂ)⁻¹), ← integral_const_mul]
            congr 1
            exact integral_congr_ae (Eventually.of_forall hsplit)
  have hF_int : Integrable (Function.uncurry F) ((volume.restrict (uIoc 0 1)).prod volume) := by
    rw [uIoc_of_le zero_le_one, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact integrable_beta_mul_mellinBarnes (u := fun y ↦ b + s y) (v := fun _ ↦ c - b)
      (by fun_prop) continuous_const (fun _ ↦ by simp [s, add_re]) (fun _ ↦ rfl)
      hbσ_pos hcb hσ_ne haσ_ne hz
  -- Evaluate the inner `t`-integral as Euler's Beta function `B(b + s, c - b)`.
  have hinner (y : ℝ) : ∫ t : ℝ in 0..1, F t y =
      Gamma (c - b) * (Gamma (a + s y) * Gamma (b + s y) * Gamma (-s y) *
        (Gamma (c + s y))⁻¹ * (-z) ^ s y) := by
    have hsum : b + s y + (c - b) = c + s y := by ring
    dsimp [F]
    rw [intervalIntegral.integral_mul_const, ← betaIntegral,
      betaIntegral_eq_Gamma_mul_div (b + s y) (c - b)
        (by simpa [s, add_re] using hbσ_pos) hcb,
      hsum, div_eq_mul_inv]
    ring
  rw [intervalIntegral.integral_const_mul, intervalIntegral_integral_swap hF_int] at hpoint
  simp_rw [hinner, integral_const_mul] at hpoint
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have hpi : (2 * π : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero Real.pi_ne_zero
  rw [eulerIntegral_def]
  set J : ℂ := ∫ y : ℝ, Gamma (a + s y) * Gamma (b + s y) * Gamma (-s y) *
    (Gamma (c + s y))⁻¹ * (-z) ^ s y
  have hI : (∫ t : ℝ in 0..1, (t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        (1 - z * t) ^ (-a)) =
      (Gamma a)⁻¹ * ((2 * π : ℂ)⁻¹ * (Gamma (c - b) * J)) := by
    rw [← hpoint, inv_mul_cancel_left₀ hΓa]
  rw [hI]
  field_simp [hΓa, hΓb, hΓcb, hpi]

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
  have h1 : ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
      C₃ * (1 + |y|) ^ K₃ * Real.exp (-(3 * π / 2) * |y|) :=
    (hb₃ y).trans_eq (by congr 2; ring)
  have h2 : ‖Gamma (c - a - b - (σ + y * I))‖ ≤
      Cc * (1 + |y|) ^ Kc * Real.exp (-(π / 2) * |y|) := by
    simpa only [sub_add_eq_sub_sub] using (hbc y).trans_eq (by congr 2; ring)
  have hrew : ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
      Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ =
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
        ‖Gamma (c - a - b - (σ + y * I))‖ := by
    simp only [norm_mul]; ring
  rw [hrew]
  refine (TauCeti.mul_le_mul_one_add_abs_rpow_mul_exp (norm_nonneg _) (norm_nonneg _) h1
    h2).trans_eq ?_
  congr 2
  ring

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

private theorem four_Gamma_meas_and_bound {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    AEStronglyMeasurable (fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))) ∧
      ∃ C R : ℝ, ∀ᵐ y : ℝ,
        ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
            Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
          C * (1 + |y|) ^ R * Real.exp (-(2 * π) * |y|) := by
  obtain ⟨Cg, _, Kg, hbg⟩ := exists_norm_four_Gamma_le ha hb hc hσ
  exact ⟨(continuous_four_Gamma ha hb hc hσ).aestronglyMeasurable,
    Cg, Kg, Eventually.of_forall fun y ↦ by simpa [neg_mul] using hbg y⟩

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
  obtain ⟨hg_meas, hg_bound⟩ := four_Gamma_meas_and_bound ha hb hc hσ
  have harg : |(1 - z).arg| < 2 * π := (abs_arg_le_pi (1 - z)).trans_lt (by linarith [Real.pi_pos])
  refine (TauCeti.integrable_cpow_smul_of_norm_le_exp_neg_mul_abs hg_meas hg_bound σ harg).congr
    (Eventually.of_forall fun y ↦ ?_)
  simp only [smul_eq_mul, mul_comm]

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
  obtain ⟨hg_meas, hg_bound⟩ := four_Gamma_meas_and_bound ha hb hc hσ
  have hker := TauCeti.analyticOnNhd_integral_cpow_smul hg_meas hg_bound σ
  intro z hz
  have harg : |(1 - z).arg| < 2 * π :=
    (abs_arg_lt_pi_of_mem_slitPlane hz).trans (by linarith [Real.pi_pos])
  have han := (hker (1 - z) ⟨hz, harg⟩).comp (analyticAt_const.sub analyticAt_id)
  refine han.congr (Eventually.of_forall fun w ↦ ?_)
  dsimp only [Function.comp_def]
  congr 1
  ext y
  simp only [smul_eq_mul, mul_comm]

/-- Pointwise Mellin–Barnes expansion of the Euler integrand in powers of `1 - z` for `t ∈ (0, 1)`
and `1 - z ∈ Complex.slitPlane`, used in the Fubini proof of DLMF 15.6.7. -/
private theorem mul_eulerIntegrand_eq_integral_mellinBarnes_one_sub {a b c z : ℂ} {σ t : ℝ}
    (hz : 1 - z ∈ slitPlane) (hσ : σ < 0) (haσ : -a.re < σ) (ht0 : 0 < t) (ht1 : t < 1) :
    Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      (2 * π : ℂ)⁻¹ * ∫ y : ℝ, (t : ℂ) ^ (b + (σ + y * I) - 1) *
        (1 - (t : ℂ)) ^ (c - a - b - (σ + y * I) - 1) *
          (Gamma (a + (σ + y * I)) * Gamma (-(σ + y * I)) * (1 - z) ^ (σ + y * I)) := by
  have h1t : 0 < 1 - t := sub_pos.2 ht1
  have ht_ne : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
  have h1t_ne : (1 - (t : ℂ)) ≠ 0 := by
    rw [← ofReal_one, ← ofReal_sub]
    exact ofReal_ne_zero.2 h1t.ne'
  set q : ℝ := t / (1 - t)
  have hq : 0 < q := div_pos ht0 h1t
  have hfact : 1 - z * (t : ℂ) = ((1 - t : ℝ) : ℂ) * (1 + (q : ℂ) * (1 - z)) := by
    have h1t_ne' : ((1 - t : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 h1t.ne'
    dsimp [q]
    push_cast
    field_simp [h1t_ne']
    ring
  have hcpow_fact : (1 - z * (t : ℂ)) ^ (-a) =
      (1 - (t : ℂ)) ^ (-a) * (1 + (q : ℂ) * (1 - z)) ^ (-a) := by
    rw [hfact, ofReal_mul_cpow h1t.le]
    push_cast
    rfl
  have hreord : Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) *
        ((1 - (t : ℂ)) ^ (-a) * (1 + (q : ℂ) * (1 - z)) ^ (-a))) =
      ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - (t : ℂ)) ^ (-a)) *
        (Gamma a * (1 + (q : ℂ) * (1 - z)) ^ (-a)) := by ring
  rw [hcpow_fact, hreord,
    ← integral_Gamma_add_mul_Gamma_neg_mul_cpow hσ haσ (TauCeti.ofReal_mul_mem_slitPlane hq hz),
    ← mul_left_comm ((2 * π : ℂ)⁻¹), ← integral_const_mul]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
  have hq_pow : (q : ℂ) ^ ((σ : ℂ) + y * I) =
      (t : ℂ) ^ ((σ : ℂ) + y * I) * (1 - (t : ℂ)) ^ (-((σ : ℂ) + y * I)) := by
    dsimp [q]
    rw [ofReal_div, div_cpow_ofReal_nonneg ht0.le h1t.le, div_eq_mul_inv, ← cpow_neg,
      ofReal_sub, ofReal_one]
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
  dsimp only
  rw [ofReal_mul_cpow hq.le, hq_pow, ← hpow_t, ← hpow_1t]
  ring

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
  have hcb : 0 < (c - b).re := by simp only [sub_re] at hcab ⊢; linarith
  have hca : 0 < (c - a).re := by simp only [sub_re] at hcab ⊢; linarith
  have hbσ_pos : 0 < b.re + σ := by linarith
  have hcab_pos : 0 < (c - a - b).re - σ := by linarith
  have hσ_ne : ∀ n : ℕ, -σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  have haσ_ne : ∀ n : ℕ, a.re + σ ≠ -n := fun n _ ↦ by linarith [n.cast_nonneg (α := ℝ)]
  let s : ℝ → ℂ := fun y ↦ (σ : ℂ) + y * I
  let F : ℝ → ℝ → ℂ := fun t y ↦
    (t : ℂ) ^ (b + s y - 1) * (1 - (t : ℂ)) ^ (c - a - b - s y - 1) *
      (Gamma (a + s y) * Gamma (-s y) * (1 - z) ^ s y)
  -- Substitute the Mellin–Barnes representation pointwise on `(0, 1)` and exchange integrals.
  have hpoint : ∫ t : ℝ in 0..1,
        Gamma a * ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - z * t) ^ (-a)) =
      (2 * π : ℂ)⁻¹ * ∫ t : ℝ in 0..1, ∫ y : ℝ, F t y := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [Ioo_ae_eq_Ioc] with t ht ht_mem
    rw [uIoc_of_le zero_le_one] at ht_mem
    obtain ⟨ht0, ht1⟩ := ht.2 ht_mem
    exact mul_eulerIntegrand_eq_integral_mellinBarnes_one_sub hz hσ haσ ht0 ht1
  have hF_int : Integrable (Function.uncurry F) ((volume.restrict (uIoc 0 1)).prod volume) := by
    rw [uIoc_of_le zero_le_one, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    exact integrable_beta_mul_mellinBarnes (u := fun y ↦ b + s y)
      (v := fun y ↦ c - a - b - s y) (by fun_prop) (by fun_prop)
      (fun _ ↦ by simp [s, add_re]) (fun _ ↦ by simp [s, sub_re])
      hbσ_pos hcab_pos hσ_ne haσ_ne hz
  -- Evaluate the inner `t`-integral as Euler's Beta function `B(b + s, c - a - b - s)`.
  have hinner (y : ℝ) : ∫ t : ℝ in 0..1, F t y =
      (Gamma (a + s y) * Gamma (b + s y) * Gamma (c - a - b - s y) *
        Gamma (-s y) * (1 - z) ^ s y) / Gamma (c - a) := by
    dsimp [F]
    have hsum : b + s y + (c - a - b - s y) = c - a := by ring
    rw [intervalIntegral.integral_mul_const, ← betaIntegral,
      betaIntegral_eq_Gamma_mul_div (b + s y) (c - a - b - s y)
        (by simpa [s, add_re] using hbσ_pos) (by simpa [s, sub_re] using hcab_pos),
      hsum]
    ring
  rw [intervalIntegral.integral_const_mul, intervalIntegral_integral_swap hF_int] at hpoint
  simp_rw [hinner, integral_div] at hpoint
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
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
  have hb : 0 < b.re := by linarith
  have hbc : b.re < c.re := by simp only [sub_re] at hσc; linarith
  have h1z : 1 - z ∈ slitPlane := by
    simpa [sub_eq_add_neg] using mem_slitPlane_of_norm_lt_one (z := -z) (by simpa using hz)
  rw [regularizedGaussHGFun_eq_eulerIntegral a hb hbc hz,
    eulerIntegral_eq_mellinBarnes_one_sub h1z hσ hσc haσ hbσ]

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
