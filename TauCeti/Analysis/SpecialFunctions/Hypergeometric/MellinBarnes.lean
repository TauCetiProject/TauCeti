/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.SpecialFunctions.Gamma.MellinBarnes
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Vertical
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Mellin–Barnes integrals for the Gauss hypergeometric function

The Gauss hypergeometric function admits two classical Mellin–Barnes integral representations along
vertical lines `Re s = σ` separating left and right sequences of Gamma poles:

* **DLMF 15.6.6** in powers of `-z`, valid on the cut plane `{z | -z ∈ Complex.slitPlane}`:
  `(2π Γ(a) Γ(b))⁻¹ ∫ Γ(a + s) Γ(b + s) Γ(-s) Γ(c + s)⁻¹ (-z)^s dy`,
  where `s = σ + i y` and `max (-Re a, -Re b) < σ < 0`.
* **DLMF 15.6.7** in powers of `1 - z`, valid on the cut plane `{z | 1 - z ∈ Complex.slitPlane}`:
  `(2π Γ(a) Γ(b) Γ(c - a) Γ(c - b))⁻¹ ∫ Γ(a + s) Γ(b + s) Γ(c - a - b - s) Γ(-s) (1 - z)^s dy`,
  where `s = σ + i y` and `max (-Re a, -Re b) < σ < min (0, Re (c - a - b))`.

Stirling's vertical-strip bounds give `O((1 + |y|)^K exp (-π |y|))` decay for the Gamma ratios in
15.6.6 and `O((1 + |y|)^K exp (-2π |y|))` decay for the four-Gamma product in 15.6.7, uniformly on
compact subsets of `(c, z)`. Combined with `|arg w| < π` on `slitPlane`, this yields integrability
and holomorphy across the respective cut planes (jointly in `(c, z)` for 15.6.6) on every vertical
line avoiding the Gamma poles.

In the convergence region `0 < Re b < Re c`, inserting the binomial Mellin–Barnes integral
`Complex.integral_cpow_neg_mul_Gamma_mul_Gamma_sub` into `Complex.eulerIntegral` at negative real
arguments `z = -x` (`x > 0`) and swapping the integrations by Fubini's theorem evaluates Euler's
integral to the Mellin–Barnes integral 15.6.6; the slit-plane identity principle
`AnalyticOnNhd.eqOn_slitPlane_of_ofReal_pos_eq` then extends equality to all `-z ∈ slitPlane`.

For 15.6.7, expanding `(1 - z)^s` in its binomial series on `‖z‖ < 1 / 2` (where the series
majorant grows as `2^{|y|} = exp ((log 2) |y|)`, strictly dominated by `exp (-2π |y|)`) and
integrating term by term via Barnes's first lemma (`Complex.integral_Gamma_add_mul_Gamma_sub`)
recovers the Gauss power series `Complex.regularizedGaussHGFun`; analyticity on the open unit disk
extends the identity to all `‖z‖ < 1`.

## Main results

* `Complex.integrable_mellinBarnesIntegrand`,
  `Complex.analyticOnNhd_integral_mellinBarnesIntegrand`: convergence and joint `(c, z)`-holomorphy
  of the Mellin–Barnes integral 15.6.6 on `{p | -p.2 ∈ slitPlane}`.
* `Complex.eulerIntegral_eq_mellinBarnes`: equality of `Complex.eulerIntegral` and the
  Mellin–Barnes integral 15.6.6 on `{z | -z ∈ slitPlane}` when `0 < Re b < Re c`.
* `Complex.integrable_mellinBarnesOneSubIntegrand`,
  `Complex.analyticOnNhd_integral_mellinBarnesOneSubIntegrand`: convergence and `z`-holomorphy of
  the Mellin–Barnes integral 15.6.7 on `{z | 1 - z ∈ slitPlane}`.
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

/-! ### Local slit-plane and vertical-line bounds -/

/-- Around any `w₀ ∈ slitPlane`, there is an open ball inside `slitPlane` on which `w ^ (σ + i y)`
and its `w`-derivative `(σ + i y) w ^ (σ + i y - 1)` satisfy uniform exponential bounds in `|y|`
with rate strictly below `π`. -/
private theorem exists_ball_slitPlane_cpow_le {w₀ : ℂ} (hw₀ : w₀ ∈ slitPlane) (σ : ℝ) :
    ∃ ε > 0, ∃ θ < π, ∃ M > 0, ∀ w ∈ ball w₀ ε,
      w ∈ slitPlane ∧
        (∀ y : ℝ, ‖w ^ ((σ : ℂ) + y * I)‖ ≤ M * Real.exp (θ * |y|)) ∧
        (∀ y : ℝ, ‖((σ : ℂ) + y * I) * w ^ ((σ : ℂ) + y * I - 1)‖ ≤
          M * (1 + |y|) * Real.exp (θ * |y|)) := by
  have hr₀ : 0 < ‖w₀‖ := norm_pos_iff.mpr (slitPlane_ne_zero hw₀)
  have harg₀ : |w₀.arg| < π :=
    abs_lt.mpr ⟨neg_pi_lt_arg w₀, (arg_le_pi w₀).lt_of_ne (slitPlane_arg_ne_pi hw₀)⟩
  set θ : ℝ := (|w₀.arg| + π) / 2
  have hθ_lt : θ < π := by dsimp [θ]; linarith
  have hnhds : {w : ℂ | w ∈ slitPlane ∧ ‖w₀‖ / 2 < ‖w‖ ∧ ‖w‖ < 2 * ‖w₀‖ ∧ |w.arg| < θ} ∈ 𝓝 w₀ := by
    refine Filter.mem_of_superset
      (Filter.inter_mem (isOpen_slitPlane.mem_nhds hw₀) <|
        Filter.inter_mem
          (continuous_norm.continuousAt.eventually (Ioi_mem_nhds (half_lt_self hr₀))) <|
          Filter.inter_mem
            (continuous_norm.continuousAt.eventually (Iio_mem_nhds (by linarith)))
            ((continuous_abs.continuousAt.comp (continuousAt_arg hw₀)).eventually
              (Iio_mem_nhds (by dsimp [θ]; linarith))))
      fun w ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, h2, h3, h4⟩
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  let B (ρ : ℝ) : ℝ := max ((‖w₀‖ / 2) ^ ρ) ((2 * ‖w₀‖) ^ ρ)
  set M : ℝ := max (B σ) (max 1 |σ| * B (σ - 1)) + 1
  have hB_nonneg (ρ : ℝ) : 0 ≤ B ρ :=
    le_trans (Real.rpow_nonneg (by positivity) ρ) (le_max_left _ _)
  have hM : 0 < M := by
    have : 0 ≤ max (B σ) (max 1 |σ| * B (σ - 1)) := le_trans (hB_nonneg σ) (le_max_left _ _)
    dsimp [M]; linarith
  have hrpow_le {w : ℂ} (hw1 : ‖w₀‖ / 2 ≤ ‖w‖) (hw2 : ‖w‖ ≤ 2 * ‖w₀‖) (ρ : ℝ) :
      ‖w‖ ^ ρ ≤ B ρ := by
    rcases le_total 0 ρ with hρ | hρ
    · exact (Real.rpow_le_rpow (by positivity) hw2 hρ).trans (le_max_right _ _)
    · exact (Real.rpow_le_rpow_of_nonpos (by positivity) hw1 hρ).trans (le_max_left _ _)
  refine ⟨ε, hε, θ, hθ_lt, M, hM, fun w hw ↦ ?_⟩
  obtain ⟨hws, hw1, hw2, hwarg⟩ := hball hw
  have hexp {y : ℝ} (hwarg : |w.arg| < θ) : -(w.arg * y) ≤ θ * |y| :=
    (neg_le_abs _).trans <| (abs_mul w.arg y).le.trans
      (mul_le_mul_of_nonneg_right hwarg.le (abs_nonneg y))
  refine ⟨hws, fun y ↦ ?_, fun y ↦ ?_⟩
  · rw [norm_cpow_of_ne_zero (slitPlane_ne_zero hws), div_eq_mul_inv, ← Real.exp_neg]
    have hre : ((σ : ℂ) + y * I).re = σ := by simp
    have him : ((σ : ℂ) + y * I).im = y := by simp
    rw [hre, him]
    calc ‖w‖ ^ σ * Real.exp (-(w.arg * y))
        ≤ B σ * Real.exp (θ * |y|) :=
          mul_le_mul (hrpow_le hw1.le hw2.le σ) (Real.exp_le_exp.mpr (hexp hwarg))
            (Real.exp_pos _).le (hB_nonneg σ)
      _ ≤ M * Real.exp (θ * |y|) := by
          gcongr; dsimp [M]; linarith [le_max_left (B σ) (max 1 |σ| * B (σ - 1))]
  · rw [norm_mul, norm_cpow_of_ne_zero (slitPlane_ne_zero hws), div_eq_mul_inv, ← Real.exp_neg]
    have hre : ((σ : ℂ) + y * I - 1).re = σ - 1 := by simp
    have him : ((σ : ℂ) + y * I - 1).im = y := by simp
    rw [hre, him]
    have hlin : ‖(σ : ℂ) + y * I‖ ≤ max 1 |σ| * (1 + |y|) := by
      calc ‖(σ : ℂ) + y * I‖ ≤ |σ| + |y| := by
              simpa using norm_le_abs_re_add_abs_im ((σ : ℂ) + y * I)
        _ ≤ max 1 |σ| * 1 + max 1 |σ| * |y| :=
            add_le_add (by simp) (le_mul_of_one_le_left (abs_nonneg y) (le_max_left 1 |σ|))
        _ = max 1 |σ| * (1 + |y|) := by ring
    calc ‖(σ : ℂ) + y * I‖ * (‖w‖ ^ (σ - 1) * Real.exp (-(w.arg * y)))
        ≤ (max 1 |σ| * (1 + |y|)) * (B (σ - 1) * Real.exp (θ * |y|)) :=
          mul_le_mul hlin
            (mul_le_mul (hrpow_le hw1.le hw2.le (σ - 1)) (Real.exp_le_exp.mpr (hexp hwarg))
              (Real.exp_pos _).le (hB_nonneg (σ - 1)))
            (by positivity) (by positivity)
      _ = (max 1 |σ| * B (σ - 1)) * (1 + |y|) * Real.exp (θ * |y|) := by ring
      _ ≤ M * (1 + |y|) * Real.exp (θ * |y|) := by
          gcongr; dsimp [M]; linarith [le_max_right (B σ) (max 1 |σ| * B (σ - 1))]

/-- Translating the imaginary part by a fixed offset `t₀` changes `(1 + |t₀ + y|) ^ p` by at most a
constant factor `(1 + |t₀|) ^ |p|`. -/
private lemma one_add_abs_add_rpow_le (p t₀ y : ℝ) :
    (1 + |t₀ + y|) ^ p ≤ (1 + |t₀|) ^ |p| * (1 + |y|) ^ p := by
  rcases le_total 0 p with hp | hp
  · have h1 : 1 + |t₀ + y| ≤ (1 + |t₀|) * (1 + |y|) := by
      nlinarith [abs_add_le t₀ y, abs_nonneg t₀, abs_nonneg y]
    calc (1 + |t₀ + y|) ^ p ≤ ((1 + |t₀|) * (1 + |y|)) ^ p :=
            Real.rpow_le_rpow (by positivity) h1 hp
      _ = (1 + |t₀|) ^ |p| * (1 + |y|) ^ p := by
            rw [Real.mul_rpow (by positivity) (by positivity), abs_of_nonneg hp]
  · have h1 : (1 + |y|) * (1 + |t₀|)⁻¹ ≤ 1 + |t₀ + y| := by
      rw [← div_eq_mul_inv, div_le_iff₀ (by positivity)]
      have hsub : |y| ≤ |t₀| + |t₀ + y| := by
        simpa using abs_add_le (-t₀) (t₀ + y)
      nlinarith [abs_nonneg t₀, abs_nonneg y, abs_nonneg (t₀ + y)]
    calc (1 + |t₀ + y|) ^ p ≤ ((1 + |y|) * (1 + |t₀|)⁻¹) ^ p :=
            Real.rpow_le_rpow_of_nonpos (by positivity) h1 hp
      _ = (1 + |t₀|) ^ |p| * (1 + |y|) ^ p := by
            rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow (by positivity),
              ← Real.rpow_neg (by positivity), abs_of_nonpos hp, mul_comm]

/-- Shifted vertical-line Stirling bound: if `Re w` is not a nonpositive integer, then
`‖Γ(w + i y)‖ ≤ C (1 + |y|) ^ K exp (-π |y| / 2)` for all `y : ℝ`. -/
private theorem exists_norm_Gamma_add_I_le {w : ℂ} (hw : ∀ n : ℕ, w.re ≠ -n) :
    ∃ C > 0, ∃ K : ℝ, ∀ y : ℝ,
      ‖Gamma (w + y * I)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y| / 2)) := by
  obtain ⟨C₀, hC₀, hbnd⟩ := TauCeti.exists_norm_Gamma_vertical_line_le hw
  set p : ℝ := w.re - 1 / 2
  refine ⟨C₀ * (1 + |w.im|) ^ |p| * Real.exp (π * |w.im| / 2), by positivity, p, fun y ↦ ?_⟩
  have hw_eq : w + y * I = (w.re : ℂ) + ↑(w.im + y) * I := by
    apply Complex.ext <;> simp
  have h0 := hbnd (w.im + y)
  rw [← hw_eq] at h0
  have hrpow := one_add_abs_add_rpow_le p w.im y
  have hexp : Real.exp (-(π * |w.im + y| / 2)) ≤
      Real.exp (π * |w.im| / 2) * Real.exp (-(π * |y| / 2)) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have hsub : |y| ≤ |w.im| + |w.im + y| := by
      simpa using abs_add_le (-w.im) (w.im + y)
    nlinarith [Real.pi_pos]
  calc ‖Gamma (w + y * I)‖
      ≤ C₀ * (1 + |w.im + y|) ^ p * Real.exp (-(π * |w.im + y| / 2)) := h0
    _ ≤ C₀ * ((1 + |w.im|) ^ |p| * (1 + |y|) ^ p) *
          (Real.exp (π * |w.im| / 2) * Real.exp (-(π * |y| / 2))) := by gcongr
    _ = C₀ * (1 + |w.im|) ^ |p| * Real.exp (π * |w.im| / 2) *
          (1 + |y|) ^ p * Real.exp (-(π * |y| / 2)) := by ring

/-- Reflected shifted vertical-line Stirling bound for `y ↦ Γ(w - i y)`. -/
private theorem exists_norm_Gamma_sub_I_le {w : ℂ} (hw : ∀ n : ℕ, w.re ≠ -n) :
    ∃ C > 0, ∃ K : ℝ, ∀ y : ℝ,
      ‖Gamma (w - y * I)‖ ≤ C * (1 + |y|) ^ K * Real.exp (-(π * |y| / 2)) := by
  obtain ⟨C, hC, K, hbnd⟩ := exists_norm_Gamma_add_I_le hw
  refine ⟨C, hC, K, fun y ↦ ?_⟩
  simpa [sub_eq_add_neg] using hbnd (-y)

/-! ### DLMF 15.6.6: Mellin–Barnes representation in powers of `-z` -/

/-- Three-Gamma decay estimate for the fixed factors of 15.6.6: on any pole-free vertical line
`Re s = σ`, `‖Γ(a + s) Γ(b + s) Γ(-s)‖ ≤ C (1 + |y|) ^ K exp (-3π |y| / 2)`. -/
private theorem exists_norm_three_Gamma_le {a b : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    ∃ C > 0, ∃ K : ℝ, ∀ y : ℝ,
      ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ ≤
        C * (1 + |y|) ^ K * Real.exp (-(3 * π * |y| / 2)) := by
  obtain ⟨Ca, hCa, Ka, hba⟩ := exists_norm_Gamma_add_I_le (w := a + σ) (by simpa using ha)
  obtain ⟨Cb, hCb, Kb, hbb⟩ := exists_norm_Gamma_add_I_le (w := b + σ) (by simpa using hb)
  obtain ⟨Cs, hCs, Ks, hbs⟩ := exists_norm_Gamma_sub_I_le (w := -σ)
    (fun n hn ↦ hσ n (by simp at hn; linarith))
  refine ⟨Ca * Cb * Cs, by positivity, Ka + Kb + Ks, fun y ↦ ?_⟩
  have h1 : ‖Gamma (a + (σ + y * I))‖ ≤
      Ca * (1 + |y|) ^ Ka * Real.exp (-(π * |y| / 2)) := by
    simpa [add_assoc] using hba y
  have h2 : ‖Gamma (b + (σ + y * I))‖ ≤
      Cb * (1 + |y|) ^ Kb * Real.exp (-(π * |y| / 2)) := by
    simpa [add_assoc] using hbb y
  have h3 : ‖Gamma (-((σ : ℂ) + y * I))‖ ≤
      Cs * (1 + |y|) ^ Ks * Real.exp (-(π * |y| / 2)) := by
    rw [show -((σ : ℂ) + y * I) = (-σ : ℂ) - y * I by ring]
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
  have hGa : Continuous fun y : ℝ ↦ Gamma (a + (σ + y * I)) :=
    continuous_iff_continuousAt.mpr fun y ↦
      (differentiableAt_Gamma _ fun m hm ↦ ha m (by simpa using congrArg re hm)
        ).continuousAt.comp (by fun_prop)
  have hGb : Continuous fun y : ℝ ↦ Gamma (b + (σ + y * I)) :=
    continuous_iff_continuousAt.mpr fun y ↦
      (differentiableAt_Gamma _ fun m hm ↦ hb m (by simpa using congrArg re hm)
        ).continuousAt.comp (by fun_prop)
  have hGs : Continuous fun y : ℝ ↦ Gamma (-(σ + y * I)) :=
    continuous_iff_continuousAt.mpr fun y ↦
      (differentiableAt_Gamma _ fun m hm ↦ hσ m (by
        have hre := congrArg re hm; simp at hre; linarith)).continuousAt.comp (by fun_prop)
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
theorem integrable_mellinBarnesIntegrand {a b : ℂ} (c : ℂ) {z : ℂ} (hz : -z ∈ slitPlane)
    {σ : ℝ} (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hσ : ∀ n : ℕ, σ ≠ n) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ ((σ : ℂ) + y * I) := by
  obtain ⟨Cg, hCg, Kg, hbg⟩ := exists_norm_three_Gamma_le ha hb hσ
  obtain ⟨Ci, hCi, hbi⟩ := TauCeti.exists_norm_inv_Gamma_vertical_strip_le (c.re + σ) (c.re + σ)
  obtain ⟨ε, hε, θ, hθ, M, _hM, hball⟩ := exists_ball_slitPlane_cpow_le hz σ
  obtain ⟨-, hpow, -⟩ := hball (-z) (mem_ball_self hε)
  set p : ℝ := 1 / 2 - (c.re + σ)
  set C_tot : ℝ := Cg * (Ci * (1 + |c.im|) ^ |p| * Real.exp (π * |c.im| / 2)) * M
  refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (Kg + p)
    (sub_pos.mpr hθ)).const_mul C_tot).mono'
    (continuous_mellinBarnesIntegrand c z hz ha hb hσ).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  have hinv : ‖(Gamma (c + (σ + y * I)))⁻¹‖ ≤
      (Ci * (1 + |c.im|) ^ |p| * Real.exp (π * |c.im| / 2)) *
        (1 + |y|) ^ p * Real.exp (π * |y| / 2) := by
    have h0 := hbi (c + (σ + y * I)) (by simp)
    have him : (c + ((σ : ℂ) + y * I)).im = c.im + y := by simp
    rw [him] at h0
    have hrpow := one_add_abs_add_rpow_le p c.im y
    have hexp : Real.exp (π * |c.im + y| / 2) ≤
        Real.exp (π * |c.im| / 2) * Real.exp (π * |y| / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by have := abs_add_le c.im y; nlinarith [Real.pi_pos])
    calc ‖(Gamma (c + (σ + y * I)))⁻¹‖
        ≤ Ci * (1 + |c.im + y|) ^ p * Real.exp (π * |c.im + y| / 2) := h0
      _ ≤ Ci * ((1 + |c.im|) ^ |p| * (1 + |y|) ^ p) *
            (Real.exp (π * |c.im| / 2) * Real.exp (π * |y| / 2)) := by gcongr
      _ = (Ci * (1 + |c.im|) ^ |p| * Real.exp (π * |c.im| / 2)) *
            (1 + |y|) ^ p * Real.exp (π * |y| / 2) := by ring
  rw [norm_mul, norm_mul]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          ‖(Gamma (c + (σ + y * I)))⁻¹‖ * ‖(-z) ^ ((σ : ℂ) + y * I)‖
      ≤ (Cg * (1 + |y|) ^ Kg * Real.exp (-(3 * π * |y| / 2))) *
          ((Ci * (1 + |c.im|) ^ |p| * Real.exp (π * |c.im| / 2)) *
            (1 + |y|) ^ p * Real.exp (π * |y| / 2)) *
          (M * Real.exp (θ * |y|)) :=
        mul_le_mul (mul_le_mul (hbg y) hinv (norm_nonneg _) (by positivity)) (hpow y)
          (norm_nonneg _) (by positivity)
    _ = C_tot * ((1 + |y|) ^ Kg * (1 + |y|) ^ p) *
          (Real.exp (-(3 * π * |y| / 2)) * Real.exp (π * |y| / 2) * Real.exp (θ * |y|)) := by
        ring
    _ = C_tot * ((1 + |y|) ^ (Kg + p) * Real.exp (-((π - θ) * |y|))) := by
        rw [← Real.rpow_add (by positivity), ← Real.exp_add, ← Real.exp_add]
        ring_nf

/-- Uniform vertical-line bounds on `‖(Γ(c + s))⁻¹‖` and `‖deriv (Γ ·)⁻¹ (c + s)‖` for `c` in the
unit ball around `c₀`. -/
private theorem exists_inv_Gamma_and_deriv_ball_le (c₀ : ℂ) (σ : ℝ) :
    ∃ C > 0, ∀ c ∈ ball c₀ 1, ∀ y : ℝ,
      ‖(Gamma (c + (σ + y * I)))⁻¹‖ ≤
        C * (1 + |y|) ^ (3 / 2 - (c₀.re + σ - 1)) * Real.exp (π * |y| / 2) ∧
      ‖deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (c + (σ + y * I))‖ ≤
        C * (1 + |y|) ^ (3 / 2 - (c₀.re + σ - 1)) * Real.exp (π * |y| / 2) := by
  obtain ⟨Ci, hCi, hbi⟩ := TauCeti.exists_norm_inv_Gamma_vertical_strip_le
    (c₀.re + σ - 1) (c₀.re + σ + 1)
  obtain ⟨Cd, hCd, hbd⟩ := TauCeti.exists_norm_deriv_inv_Gamma_vertical_strip_le
    (c₀.re + σ - 1) (c₀.re + σ + 1)
  set p : ℝ := 3 / 2 - (c₀.re + σ - 1)
  set C_im : ℝ := (1 + (|c₀.im| + 1)) ^ (|p| + 1) * Real.exp (π * (|c₀.im| + 1) / 2)
  refine ⟨max Cd Ci * C_im, by positivity, fun c hc y ↦ ?_⟩
  have hcc : ‖c - c₀‖ < 1 := mem_ball_iff_norm.mp hc
  have hre_mem : (c + ((σ : ℂ) + y * I)).re ∈ Icc (c₀.re + σ - 1) (c₀.re + σ + 1) := by
    have hre : |c.re - c₀.re| ≤ 1 := by
      simpa [sub_re] using (abs_re_le_norm (c - c₀)).trans hcc.le
    obtain ⟨h1, h2⟩ := abs_le.mp hre
    simp only [add_re, ofReal_re, mul_I_re, ofReal_im, neg_zero, add_zero, mem_Icc]
    exact ⟨by linarith, by linarith⟩
  have him_le : |c.im| ≤ |c₀.im| + 1 := by
    have him : |c.im - c₀.im| ≤ 1 := by
      simpa [sub_im] using (abs_im_le_norm (c - c₀)).trans hcc.le
    linarith [abs_sub_abs_le_abs_sub c.im c₀.im, (abs_le.mp him).2]
  have hshift : (1 + |(c + ((σ : ℂ) + y * I)).im|) ^ p *
      Real.exp (π * |(c + ((σ : ℂ) + y * I)).im| / 2) ≤
      C_im * (1 + |y|) ^ p * Real.exp (π * |y| / 2) := by
    have him_eq : (c + ((σ : ℂ) + y * I)).im = c.im + y := by simp
    rw [him_eq]
    have hrp := one_add_abs_add_rpow_le p c.im y
    have hrp2 : (1 + |c.im|) ^ |p| ≤ (1 + (|c₀.im| + 1)) ^ (|p| + 1) :=
      (Real.rpow_le_rpow (by positivity) (by linarith) (abs_nonneg _)).trans
        (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg c₀.im]) (by linarith))
    have hexp : Real.exp (π * |c.im + y| / 2) ≤
        Real.exp (π * (|c₀.im| + 1) / 2) * Real.exp (π * |y| / 2) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by have := abs_add_le c.im y; nlinarith [Real.pi_pos])
    calc (1 + |c.im + y|) ^ p * Real.exp (π * |c.im + y| / 2)
        ≤ ((1 + |c.im|) ^ |p| * (1 + |y|) ^ p) *
            (Real.exp (π * (|c₀.im| + 1) / 2) * Real.exp (π * |y| / 2)) := by gcongr
      _ ≤ ((1 + (|c₀.im| + 1)) ^ (|p| + 1) * (1 + |y|) ^ p) *
            (Real.exp (π * (|c₀.im| + 1) / 2) * Real.exp (π * |y| / 2)) := by gcongr
      _ = C_im * (1 + |y|) ^ p * Real.exp (π * |y| / 2) := by ring
  refine ⟨?_, ?_⟩
  · have h12 : 1 / 2 - (c₀.re + σ - 1) ≤ p := by dsimp [p]; linarith
    have hrp_up : (1 + |(c + ((σ : ℂ) + y * I)).im|) ^ (1 / 2 - (c₀.re + σ - 1)) ≤
        (1 + |(c + ((σ : ℂ) + y * I)).im|) ^ p :=
      Real.rpow_le_rpow_of_exponent_le
        (le_add_of_nonneg_right (abs_nonneg _)) h12
    calc ‖(Gamma (c + (σ + y * I)))⁻¹‖
        ≤ Ci * ((1 + |(c + ((σ : ℂ) + y * I)).im|) ^ p *
            Real.exp (π * |(c + ((σ : ℂ) + y * I)).im| / 2)) := by
            refine (hbi _ hre_mem).trans ?_; rw [← mul_assoc]; gcongr
      _ ≤ max Cd Ci * (C_im * (1 + |y|) ^ p * Real.exp (π * |y| / 2)) :=
            mul_le_mul (le_max_right _ _) hshift (by positivity) (by positivity)
      _ = max Cd Ci * C_im * (1 + |y|) ^ p * Real.exp (π * |y| / 2) := by ring
  · calc ‖deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (c + (σ + y * I))‖
        ≤ Cd * ((1 + |(c + ((σ : ℂ) + y * I)).im|) ^ p *
            Real.exp (π * |(c + ((σ : ℂ) + y * I)).im| / 2)) := by
            simpa [mul_assoc, p] using hbd _ hre_mem
      _ ≤ max Cd Ci * (C_im * (1 + |y|) ^ p * Real.exp (π * |y| / 2)) :=
            mul_le_mul (le_max_left _ _) hshift (by positivity) (by positivity)
      _ = max Cd Ci * C_im * (1 + |y|) ^ p * Real.exp (π * |y| / 2) := by ring

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
    {p : ℂ × ℂ} (hCg : 0 < Cg) (hCc : 0 < Cc) (hM : 0 < M)
    (hg : ‖g‖ ≤ Cg * (1 + |y|) ^ Kg * Real.exp (-(3 * π * |y| / 2)))
    (hi : ‖(Gamma (p.1 + (σ + y * I)))⁻¹‖ ≤ Cc * (1 + |y|) ^ p_exp * Real.exp (π * |y| / 2))
    (hd : ‖deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p.1 + (σ + y * I))‖ ≤
      Cc * (1 + |y|) ^ p_exp * Real.exp (π * |y| / 2))
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
  have hterm1 : ‖g * deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p.1 + (σ + y * I)) *
      (-p.2) ^ ((σ : ℂ) + y * I)‖ ≤ W := by
    have h1y : (1 + |y|) ^ Kg * (1 + |y|) ^ p_exp ≤ (1 + |y|) ^ (Kg + p_exp + 1) := by
      rw [← Real.rpow_add (by positivity)]
      exact Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (abs_nonneg y)) (by linarith)
    rw [norm_mul, norm_mul]
    calc ‖g‖ * ‖deriv (fun w : ℂ ↦ (Gamma w)⁻¹) (p.1 + (σ + y * I))‖ *
            ‖(-p.2) ^ ((σ : ℂ) + y * I)‖
        ≤ (Cg * (1 + |y|) ^ Kg * Real.exp (-(3 * π * |y| / 2))) *
            (Cc * (1 + |y|) ^ p_exp * Real.exp (π * |y| / 2)) * (M * Real.exp (θ * |y|)) :=
          mul_le_mul (mul_le_mul hg hd (norm_nonneg _) (by positivity)) hpow0
            (norm_nonneg _) (by positivity)
      _ = Cg * Cc * M * ((1 + |y|) ^ Kg * (1 + |y|) ^ p_exp) *
            (Real.exp (-(3 * π * |y| / 2)) * Real.exp (π * |y| / 2) * Real.exp (θ * |y|)) := by
          ring
      _ ≤ Cg * Cc * M * (1 + |y|) ^ (Kg + p_exp + 1) * Real.exp (-((π - θ) * |y|)) := by
          rw [← Real.exp_add, ← Real.exp_add,
            show -(3 * π * |y| / 2) + π * |y| / 2 + θ * |y| = -((π - θ) * |y|) by ring]
          gcongr
      _ = W := by ring
  have hterm2 : ‖-(g * (Gamma (p.1 + (σ + y * I)))⁻¹ *
      (((σ : ℂ) + y * I) * (-p.2) ^ ((σ : ℂ) + y * I - 1)))‖ ≤ W := by
    rw [norm_neg, norm_mul, norm_mul]
    calc ‖g‖ * ‖(Gamma (p.1 + (σ + y * I)))⁻¹‖ *
            ‖((σ : ℂ) + y * I) * (-p.2) ^ ((σ : ℂ) + y * I - 1)‖
        ≤ (Cg * (1 + |y|) ^ Kg * Real.exp (-(3 * π * |y| / 2))) *
            (Cc * (1 + |y|) ^ p_exp * Real.exp (π * |y| / 2)) *
            (M * (1 + |y|) * Real.exp (θ * |y|)) :=
          mul_le_mul (mul_le_mul hg hi (norm_nonneg _) (by positivity)) hpow1
            (norm_nonneg _) (by positivity)
      _ = Cg * Cc * M * ((1 + |y|) ^ Kg * (1 + |y|) ^ p_exp * (1 + |y|) ^ (1 : ℝ)) *
            (Real.exp (-(3 * π * |y| / 2)) * Real.exp (π * |y| / 2) * Real.exp (θ * |y|)) := by
          rw [Real.rpow_one]; ring
      _ = W := by
          rw [← Real.rpow_add (by positivity), ← Real.rpow_add (by positivity),
            ← Real.exp_add, ← Real.exp_add]
          dsimp [W]; ring_nf
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
theorem analyticOnNhd_integral_mellinBarnesIntegrand {a b : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
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
  obtain ⟨Cg, hCg, Kg, hbg⟩ := exists_norm_three_Gamma_le ha hb hσ
  obtain ⟨Cc, hCc, hbc⟩ := exists_inv_Gamma_and_deriv_ball_le p₀.1 σ
  obtain ⟨ε, hε, θ, hθ, M, hM, hball⟩ := exists_ball_slitPlane_cpow_le hp₀ σ
  let U : Set (ℂ × ℂ) := ball p₀.1 1 ×ˢ ((fun z : ℂ ↦ -z) ⁻¹' ball (-p₀.2) ε)
  have hU_nhds : U ∈ 𝓝 p₀ := prod_mem_nhds (ball_mem_nhds p₀.1 zero_lt_one)
    ((continuous_neg.continuousAt).eventually (ball_mem_nhds (-p₀.2) hε))
  set p_exp : ℝ := 3 / 2 - (p₀.1.re + σ - 1)
  set C_dom : ℝ := Cg * Cc * M *
    (‖ContinuousLinearMap.fst ℂ ℂ ℂ‖ + ‖ContinuousLinearMap.snd ℂ ℂ ℂ‖ + 1)
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
      ‖F' p y‖ ≤ C_dom * ((1 + |y|) ^ (Kg + p_exp + 1) * Real.exp (-((π - θ) * |y|))) :=
    Eventually.of_forall fun y p hp ↦
      norm_fderiv_mellinBarnesIntegrand_le hCg hCc hM (hbg y) (hbc p.1 hp.1 y).1
        (hbc p.1 hp.1 y).2 ((hball (-p.2) hp.2).2.1 y) ((hball (-p.2) hp.2).2.2 y)
  have h_dom_int := (TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (Kg + p_exp + 1)
    (sub_pos.mpr hθ)).const_mul C_dom
  exact (hasFDerivAt_integral_of_dominated_of_fderiv_le hU_nhds hF_meas
    (integrable_mellinBarnesIntegrand p₀.1 hp₀ ha hb hσ) hF'_meas h_bound h_dom_int h_diff
    ).differentiableAt.differentiableWithinAt

/-- Product integrability on `(0, 1) × ℝ` of the Fubini kernel connecting `eulerIntegral` at `-x`
(`x > 0`) with the Mellin–Barnes integral 15.6.6. -/
private theorem integrable_eulerMellinKernel (a : ℂ) {b c : ℂ} (hbc : b.re < c.re) {x : ℝ}
    (hx : 0 < x) {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    Integrable
      (fun p : ℝ × ℝ ↦ ((p.1 : ℂ) ^ (b + (σ + p.2 * I) - 1) * (1 - (p.1 : ℂ)) ^ (c - b - 1)) *
        ((x : ℂ) ^ ((σ : ℂ) + p.2 * I) * Gamma (-(σ + p.2 * I)) * Gamma (a + (σ + p.2 * I))))
      ((volume.restrict (Ioo (0 : ℝ) 1)).prod volume) := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hbσ' : 0 < (b + σ).re := by simp; linarith
  have hf₁ : Integrable
      (fun t : ℝ ↦ ‖(t : ℂ) ^ (b + σ - 1) * (1 - (t : ℂ)) ^ (c - b - 1)‖) μ := by
    have hb_conv := betaIntegral_convergent hbσ' hcb
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at hb_conv
    exact (hb_conv.mono_set Ioo_subset_Ioc_self).norm
  have hf₂ : Integrable
      (fun y : ℝ ↦ ‖(x : ℂ) ^ (σ : ℂ) * Gamma (-(σ + y * I)) * Gamma (a + (σ + y * I))‖) := by
    have hg := (integrable_Gamma_add_mul_Gamma_sub (b := a + σ) (d := -σ)
      (fun n hn ↦ by simp at hn; linarith [n.cast_nonneg' (α := ℝ)])
      (fun n hn ↦ by simp at hn; linarith [n.cast_nonneg' (α := ℝ)])).const_mul ((x : ℂ) ^ (σ : ℂ))
    refine hg.norm.congr (Eventually.of_forall fun y ↦ ?_)
    dsimp only
    congr 1
    rw [show a + ((σ : ℂ) + y * I) = a + σ + y * I by ring,
      show -((σ : ℂ) + y * I) = (-σ : ℂ) - y * I by ring]
    ring
  refine (hf₁.mul_prod hf₂).mono' ?_ ?_
  · have hmeas_eq : μ.prod (volume : Measure ℝ) =
        volume.restrict (Ioo (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
      simpa [μ, Measure.volume_eq_prod] using
        Measure.prod_restrict (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
          (Ioo 0 1) univ
    rw [hmeas_eq]
    refine ContinuousOn.aestronglyMeasurable (continuousOn_of_forall_continuousAt fun p hp ↦ ?_)
      (measurableSet_Ioo.prod MeasurableSet.univ)
    obtain ⟨ht0, ht1⟩ := hp.1
    have hc1 : ContinuousAt (fun p : ℝ × ℝ ↦ (p.1 : ℂ) ^ (b + (σ + p.2 * I) - 1)) p :=
      ContinuousAt.cpow (continuous_ofReal.continuousAt.comp continuousAt_fst) (by fun_prop)
        (ofReal_mem_slitPlane.mpr ht0)
    have hc2 : ContinuousAt (fun p : ℝ × ℝ ↦ (1 - (p.1 : ℂ)) ^ (c - b - 1)) p := by
      refine ContinuousAt.cpow (by fun_prop) continuousAt_const ?_
      rw [← ofReal_one, ← ofReal_sub]
      exact ofReal_mem_slitPlane.mpr (by linarith)
    have hc3 : ContinuousAt (fun p : ℝ × ℝ ↦ (x : ℂ) ^ ((σ : ℂ) + p.2 * I)) p :=
      ContinuousAt.cpow continuousAt_const (by fun_prop) (ofReal_mem_slitPlane.mpr hx)
    have hc4 : ContinuousAt (fun p : ℝ × ℝ ↦ Gamma (-(σ + p.2 * I))) p := by
      refine (differentiableAt_Gamma _ fun m hm ↦ ?_).continuousAt.comp (by fun_prop)
      have hre := congrArg re hm; simp at hre; linarith [m.cast_nonneg' (α := ℝ)]
    have hc5 : ContinuousAt (fun p : ℝ × ℝ ↦ Gamma (a + (σ + p.2 * I))) p := by
      refine (differentiableAt_Gamma _ fun m hm ↦ ?_).continuousAt.comp (by fun_prop)
      have hre := congrArg re hm; simp at hre; linarith [m.cast_nonneg' (α := ℝ)]
    exact (hc1.mul hc2).mul ((hc3.mul hc4).mul hc5)
  · have hae : ∀ᵐ p : ℝ × ℝ ∂μ.prod volume, p.1 ∈ Ioo (0 : ℝ) 1 := by
      rw [Measure.ae_prod_iff_ae_ae]
      · filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
        exact Eventually.of_forall fun _ ↦ ht
      · exact measurableSet_Ioo.preimage measurable_fst
    filter_upwards [hae] with p hp
    simp only [norm_mul, norm_cpow_eq_rpow_re_of_pos hp.1, norm_cpow_eq_rpow_re_of_pos hx]
    have hre1 : (b + (↑σ + ↑p.2 * I) - 1).re = (b + ↑σ - 1).re := by simp
    have hre2 : ((σ : ℂ) + ↑p.2 * I).re = ((σ : ℂ)).re := by simp
    rw [hre1, hre2]

/-- Evaluation of `eulerIntegral` at a negative real argument `-x` (`x > 0`) as the Mellin–Barnes
integral 15.6.6, proved by inserting `integral_cpow_neg_mul_Gamma_mul_Gamma_sub` and swapping the
two integrals via Fubini's theorem. -/
private theorem eulerIntegral_neg_ofReal_eq_mellinBarnes (a : ℂ) {b c : ℂ} (hb : 0 < b.re)
    (hbc : b.re < c.re) {x : ℝ} (hx : 0 < x) {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ)
    (hbσ : -b.re < σ) :
    eulerIntegral a b c (-(x : ℂ)) = (2 * π * Gamma a * Gamma b)⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ ((σ : ℂ) + y * I) := by
  let μ : Measure ℝ := volume.restrict (Ioo (0 : ℝ) 1)
  let F : ℝ → ℝ → ℂ := fun t y ↦
    ((t : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
      ((x : ℂ) ^ ((σ : ℂ) + y * I) * Gamma (-(σ + y * I)) * Gamma (a + (σ + y * I)))
  have hcb : 0 < (c - b).re := by simpa using sub_pos.mpr hbc
  have hF : Integrable (Function.uncurry F) (μ.prod volume) :=
    integrable_eulerMellinKernel a hbc hx hσ haσ hbσ
  -- Integrating `y` first produces `2π Γ(a)` times the unnormalized Euler integral at `-x`.
  have h_y_first : ∫ t, (∫ y : ℝ, F t y) ∂μ =
      2 * π * Gamma a * (Gamma b * Gamma (c - b) * eulerIntegral a b c (-(x : ℂ))) := by
    set τ : ℝ := -σ
    have hτ_pos : 0 < τ := neg_pos.mpr hσ
    have hτ_lt : τ < a.re := by dsimp [τ]; linarith
    have hinner : ∀ᵐ t ∂μ, ∫ y : ℝ, F t y =
        2 * π * Gamma a *
          ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1) * (1 - (-(x : ℂ)) * t) ^ (-a)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      have hxt : 0 < x * t := mul_pos hx ht.1
      have hsplit (y : ℝ) : F t y =
          ((t : ℂ) ^ (b - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) *
            (((x * t : ℝ) : ℂ) ^ (-((τ : ℂ) + (-y : ℝ) * I)) *
              (Gamma ((τ : ℂ) + (-y : ℝ) * I) * Gamma (a - ((τ : ℂ) + (-y : ℝ) * I)))) := by
        have ht_pow : (t : ℂ) ^ (b + ((σ : ℂ) + y * I) - 1) =
            (t : ℂ) ^ (b - 1) * (t : ℂ) ^ ((σ : ℂ) + y * I) := by
          rw [show b + ((σ : ℂ) + y * I) - 1 = (b - 1) + ((σ : ℂ) + y * I) by ring,
            cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.1.ne'),
            cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.1.ne'),
            cpow_def_of_ne_zero (ofReal_ne_zero.mpr ht.1.ne'), mul_add, Complex.exp_add]
        have hxt_pow : (t : ℂ) ^ ((σ : ℂ) + y * I) * (x : ℂ) ^ ((σ : ℂ) + y * I) =
            ((x * t : ℝ) : ℂ) ^ ((σ : ℂ) + y * I) := by
          rw [ofReal_mul, mul_cpow_ofReal_nonneg hx.le ht.1.le, mul_comm]
        have hneg1 : -((τ : ℂ) + (-y : ℝ) * I) = (σ : ℂ) + y * I := by dsimp [τ]; push_cast; ring
        have hneg2 : (τ : ℂ) + (-y : ℝ) * I = -((σ : ℂ) + y * I) := by dsimp [τ]; push_cast; ring
        have hneg3 : a - ((τ : ℂ) + (-y : ℝ) * I) = a + ((σ : ℂ) + y * I) := by
          dsimp [τ]; push_cast; ring
        dsimp [F]
        rw [ht_pow, hneg3, hneg1, hneg2, ← hxt_pow]
        ring
      simp_rw [hsplit]
      rw [integral_const_mul, integral_neg_eq_self (fun y : ℝ ↦
        ((x * t : ℝ) : ℂ) ^ (-((τ : ℂ) + y * I)) *
          (Gamma ((τ : ℂ) + y * I) * Gamma (a - ((τ : ℂ) + y * I)))),
        integral_cpow_neg_mul_Gamma_mul_Gamma_sub hτ_pos hτ_lt hxt,
        show (1 : ℂ) + ((x * t : ℝ) : ℂ) = 1 - (-(x : ℂ)) * (t : ℂ) by push_cast; ring]
      ring
    rw [integral_congr_ae hinner, integral_const_mul]
    congr 1
    have hΓb : Gamma b * Gamma (c - b) ≠ 0 :=
      mul_ne_zero (Gamma_ne_zero_of_re_pos hb) (Gamma_ne_zero_of_re_pos hcb)
    rw [eulerIntegral_def, ← mul_assoc, mul_inv_cancel₀ hΓb, one_mul,
      intervalIntegral.integral_of_le zero_le_one, ← setIntegral_congr_set Ioo_ae_eq_Ioc]
  -- Integrating `t` first evaluates the Beta integral with parameters `b + σ + i y` and `c - b`.
  set J : ℂ := ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
    (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ ((σ : ℂ) + y * I)
  have h_t_first : ∫ y : ℝ, ∫ t, F t y ∂μ = Gamma (c - b) * J := by
    have hinner (y : ℝ) : ∫ t, F t y ∂μ =
        Gamma (c - b) *
          (Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
            (Gamma (c + (σ + y * I)))⁻¹ * (x : ℂ) ^ ((σ : ℂ) + y * I)) := by
      have hbeta : ∫ t, ((t : ℂ) ^ (b + (σ + y * I) - 1) * (1 - (t : ℂ)) ^ (c - b - 1)) ∂μ =
          Gamma (b + (σ + y * I)) * Gamma (c - b) / Gamma (c + (σ + y * I)) := by
        rw [show μ = volume.restrict (Ioo (0 : ℝ) 1) from rfl,
          setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
          ← betaIntegral, betaIntegral_eq_Gamma_mul_div _ _ (by simp; linarith) hcb]
        congr 2; ring
      simp only [F, integral_mul_const, hbeta, div_eq_mul_inv]
      ring
    simp_rw [hinner, integral_const_mul]
    rfl
  have hswap := integral_integral_swap hF
  rw [h_y_first, h_t_first] at hswap
  have hΓa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have hΓb : Gamma b ≠ 0 := Gamma_ne_zero_of_re_pos hb
  have hΓcb : Gamma (c - b) ≠ 0 := Gamma_ne_zero_of_re_pos hcb
  have h2pi : (2 * π : ℂ) ≠ 0 := by norm_num [Real.pi_ne_zero]
  calc eulerIntegral a b c (-(x : ℂ))
      = (2 * π * Gamma a * (Gamma b * Gamma (c - b)))⁻¹ *
          (2 * π * Gamma a * (Gamma b * Gamma (c - b) * eulerIntegral a b c (-(x : ℂ)))) := by
          field_simp [h2pi, hΓa, hΓb, hΓcb]
    _ = (2 * π * Gamma a * (Gamma b * Gamma (c - b)))⁻¹ * (Gamma (c - b) * J) := by
          rw [hswap]
    _ = (2 * π * Gamma a * Gamma b)⁻¹ * J := by
          field_simp [h2pi, hΓa, hΓb, hΓcb]

/-- **Mellin–Barnes integral for Euler's hypergeometric integral**
([DLMF 15.6.6](https://dlmf.nist.gov/15.6.E6)). For `0 < Re b < Re c`, `-z ∈ slitPlane`, and any
vertical line `Re s = σ` with `max (-Re a, -Re b) < σ < 0`,
`eulerIntegral a b c z = (2π Γ(a) Γ(b))⁻¹ ∫ Γ(a + s) Γ(b + s) Γ(-s) Γ(c + s)⁻¹ (-z)^s dy`. -/
theorem eulerIntegral_eq_mellinBarnes (a : ℂ) {b c z : ℂ} (hb : 0 < b.re) (hbc : b.re < c.re)
    (hz : -z ∈ slitPlane) {σ : ℝ} (hσ : σ < 0) (haσ : -a.re < σ) (hbσ : -b.re < σ) :
    eulerIntegral a b c z = (2 * π * Gamma a * Gamma b)⁻¹ *
      ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
        (Gamma (c + (σ + y * I)))⁻¹ * (-z) ^ ((σ : ℂ) + y * I) := by
  let f : ℂ → ℂ := fun w ↦ eulerIntegral a b c (-w)
  let g : ℂ → ℂ := fun w ↦ (2 * π * Gamma a * Gamma b)⁻¹ *
    ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) * Gamma (-(σ + y * I)) *
      (Gamma (c + (σ + y * I)))⁻¹ * (- -w) ^ ((σ : ℂ) + y * I)
  have hf : AnalyticOnNhd ℂ f slitPlane := by
    intro w hw
    have h1w : 1 - -w ∈ slitPlane := by
      simpa [sub_neg_eq_add] using TauCeti.ofReal_add_mem_slitPlane hw zero_le_one
    exact (analyticOnNhd_eulerIntegral hb hbc (a, -w) h1w).comp₂
      analyticAt_const (by fun_prop)
  have hg : AnalyticOnNhd ℂ g slitPlane := by
    have ha' : ∀ n : ℕ, a.re + σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
    have hb' : ∀ n : ℕ, b.re + σ ≠ -n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
    have hσ' : ∀ n : ℕ, σ ≠ n := fun n hn ↦ by linarith [n.cast_nonneg' (α := ℝ)]
    intro w hw
    exact analyticAt_const.mul <|
      (analyticOnNhd_integral_mellinBarnesIntegrand ha' hb' hσ' (c, -w) (by simpa using hw)).comp₂
        analyticAt_const (by fun_prop)
  have heq := hf.eqOn_slitPlane_of_ofReal_pos_eq hg
    (fun t ht ↦ by
      simpa [f, g] using eulerIntegral_neg_ofReal_eq_mellinBarnes a hb hbc ht hσ haσ hbσ) hz
  simpa [f, g] using heq

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
  obtain ⟨Cc, hCc, Kc, hbc⟩ := exists_norm_Gamma_sub_I_le (w := c - a - b - σ) (by simpa using hc)
  refine ⟨C₃ * Cc, by positivity, K₃ + Kc, fun y ↦ ?_⟩
  have h1 := hb₃ y
  have h2 : ‖Gamma (c - a - b - (σ + y * I))‖ ≤
      Cc * (1 + |y|) ^ Kc * Real.exp (-(π * |y| / 2)) := by
    simpa [sub_add_eq_sub_sub] using hbc y
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
  have hGa : Continuous fun y : ℝ ↦ Gamma (a + (σ + y * I)) :=
    continuous_iff_continuousAt.mpr fun y ↦
      (differentiableAt_Gamma _ fun m hm ↦ ha m (by simpa using congrArg re hm)
        ).continuousAt.comp (by fun_prop)
  have hGb : Continuous fun y : ℝ ↦ Gamma (b + (σ + y * I)) :=
    continuous_iff_continuousAt.mpr fun y ↦
      (differentiableAt_Gamma _ fun m hm ↦ hb m (by simpa using congrArg re hm)
        ).continuousAt.comp (by fun_prop)
  have hGc : Continuous fun y : ℝ ↦ Gamma (c - a - b - (σ + y * I)) :=
    continuous_iff_continuousAt.mpr fun y ↦
      (differentiableAt_Gamma _ fun m hm ↦ hc m (by
        have hre := congrArg re hm; simp at hre ⊢; linarith)).continuousAt.comp (by fun_prop)
  have hGs : Continuous fun y : ℝ ↦ Gamma (-(σ + y * I)) :=
    continuous_iff_continuousAt.mpr fun y ↦
      (differentiableAt_Gamma _ fun m hm ↦ hσ m (by
        have hre := congrArg re hm; simp at hre; linarith)).continuousAt.comp (by fun_prop)
  exact ((hGa.mul hGb).mul hGc).mul hGs

/-- On every vertical line `Re s = σ` avoiding the poles of all four Gamma factors, the
Mellin–Barnes integrand of DLMF 15.6.7 is integrable for every `z` with `1 - z ∈ slitPlane`. -/
theorem integrable_mellinBarnesOneSubIntegrand {a b c z : ℂ} (hz : 1 - z ∈ slitPlane)
    {σ : ℝ} (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
    (hc : ∀ n : ℕ, (c - a - b).re - σ ≠ -n) (hσ : ∀ n : ℕ, σ ≠ n) :
    Integrable fun y : ℝ ↦
      Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
        Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
        (1 - z) ^ ((σ : ℂ) + y * I) := by
  obtain ⟨Cg, hCg, Kg, hbg⟩ := exists_norm_four_Gamma_le ha hb hc hσ
  obtain ⟨ε, hε, θ, hθ, M, _hM, hball⟩ := exists_ball_slitPlane_cpow_le hz σ
  obtain ⟨-, hpow, -⟩ := hball (1 - z) (mem_ball_self hε)
  have h2pi_sub : 0 < 2 * π - θ := by linarith [Real.pi_pos]
  refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs Kg h2pi_sub).const_mul
    (Cg * M)).mono'
    ((continuous_four_Gamma ha hb hc hσ).mul
      (continuous_const.cpow (by fun_prop) (fun _ ↦ hz))).aestronglyMeasurable
    (Eventually.of_forall fun y ↦ ?_)
  rw [norm_mul]
  calc ‖Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I))‖ *
          ‖(1 - z) ^ ((σ : ℂ) + y * I)‖
      ≤ (Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|))) * (M * Real.exp (θ * |y|)) :=
        mul_le_mul (hbg y) (hpow y) (norm_nonneg _) (by positivity)
    _ = Cg * M * ((1 + |y|) ^ Kg * (Real.exp (-(2 * π * |y|)) * Real.exp (θ * |y|))) := by ring
    _ = Cg * M * ((1 + |y|) ^ Kg * Real.exp (-((2 * π - θ) * |y|))) := by
        rw [← Real.exp_add]; ring_nf

/-- On every vertical line `Re s = σ` avoiding the poles of all four Gamma factors, the
Mellin–Barnes integral of DLMF 15.6.7 is holomorphic on `{z | 1 - z ∈ slitPlane}`. -/
theorem analyticOnNhd_integral_mellinBarnesOneSubIntegrand {a b c : ℂ} {σ : ℝ}
    (ha : ∀ n : ℕ, a.re + σ ≠ -n) (hb : ∀ n : ℕ, b.re + σ ≠ -n)
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
  obtain ⟨Cg, hCg, Kg, hbg⟩ := exists_norm_four_Gamma_le ha hb hc hσ
  obtain ⟨ε, hε, θ, hθ, M, _hM, hball⟩ := exists_ball_slitPlane_cpow_le hz₀ σ
  let U : Set ℂ := (fun z : ℂ ↦ 1 - z) ⁻¹' ball (1 - z₀) ε
  have hU_nhds : U ∈ 𝓝 z₀ :=
    (continuous_const.sub continuous_id).continuousAt.eventually (ball_mem_nhds (1 - z₀) hε)
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
    (integrable_mellinBarnesOneSubIntegrand hz₀ ha hb hc hσ) hF'_meas h_bound h_dom_int h_diff
    ).2.differentiableAt.differentiableWithinAt

/-- Complex multichoose norm bound: `‖multichoose w n‖ ≤ multichoose r n` whenever `‖w‖ ≤ r`. -/
private lemma norm_multichoose_le_of_norm_le {w : ℂ} {r : ℝ} (hr : ‖w‖ ≤ r) (n : ℕ) :
    ‖Ring.multichoose w n‖ ≤ Ring.multichoose r n := by
  have hp : ‖(ascPochhammer ℂ n).eval w‖ ≤ (ascPochhammer ℝ n).eval r := by
    induction n with
    | zero => simp
    | succ k ih =>
      rw [ascPochhammer_succ_right, ascPochhammer_succ_right, Polynomial.eval_mul,
        Polynomial.eval_mul, norm_mul]
      have hnonneg : 0 ≤ (ascPochhammer ℝ k).eval r := (norm_nonneg _).trans ih
      have hstep : ‖(Polynomial.X + (k : Polynomial ℂ)).eval w‖ ≤
          (Polynomial.X + (k : Polynomial ℝ)).eval r := by
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_natCast]
        exact (norm_add_le w k).trans (by simpa using add_le_add_right hr (k : ℝ))
      exact mul_le_mul ih hstep (norm_nonneg _) hnonneg
  have hwc : (n ! : ℝ) * ‖Ring.multichoose w n‖ = ‖(ascPochhammer ℂ n).eval w‖ := by
    have h := congrArg norm (Ring.factorial_nsmul_multichoose_eq_ascPochhammer w n)
    rwa [nsmul_eq_mul, norm_mul, norm_natCast, Polynomial.ascPochhammer_smeval_cast,
      Polynomial.ascPochhammer_smeval_eq_eval] at h
  have hrc : (n ! : ℝ) * Ring.multichoose r n = (ascPochhammer ℝ n).eval r := by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer r n
    rwa [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_cast,
      Polynomial.ascPochhammer_smeval_eq_eval] at h
  exact le_of_mul_le_mul_left (by linarith) (Nat.cast_pos.mpr n.factorial_pos)

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
      have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (-s) n
      rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_cast,
        Polynomial.ascPochhammer_smeval_eq_eval, ← Gamma_add_nat_div_Gamma_eq (-s) hs_ne,
        show -s + (n : ℂ) = (n : ℂ) - s by ring] at h1
      field_simp [hGs, hfac] at h1 ⊢
      linear_combination h1
    calc Gamma (a + s) * Gamma (b + s) * Gamma (c - a - b - s) * Gamma (-s) *
            (Ring.multichoose (-s) n * z ^ n)
        = (Gamma (a + s) * Gamma (b + s) * Gamma (c - a - b - s)) *
            (Gamma (-s) * Ring.multichoose (-s) n) * z ^ n := by ring
      _ = (z ^ n / (n ! : ℂ)) *
            (Gamma (a + s) * Gamma (b + s) * Gamma (c - a - b - s) * Gamma ((n : ℂ) - s)) := by
            rw [hmc]; ring
  simp_rw [hFn]
  rw [integral_const_mul]
  have hbarnes := integral_Gamma_add_mul_Gamma_sub (a := a) (b := b) (c := c - a - b)
    (d := (n : ℂ)) haσ hbσ hσc (by simp; linarith [n.cast_nonneg' (α := ℝ)])
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
`(1 - ‖z‖)^{-(|σ| + |y|)} ≤ 2 ^ |σ| exp ((log 2) |y|)` is strictly dominated by `exp (-2π |y|)`. -/
private theorem integrable_tsum_multichoose_bound {Cg : ℝ} (hCg : 0 < Cg) (Kg σ : ℝ) {z : ℂ}
    (hz : ‖z‖ < 1 / 2) :
    Integrable fun y : ℝ ↦ ∑' n : ℕ,
      Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|)) *
        (Ring.multichoose (|σ| + |y|) n * ‖z‖ ^ n) := by
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
  refine ((TauCeti.integrable_one_add_abs_rpow_mul_exp_neg_mul_abs Kg hrate).const_mul
    (Cg * 2 ^ |σ|)).mono' ?_ (Eventually.of_forall fun y ↦ ?_)
  · rw [show (fun y : ℝ ↦ ∑' n : ℕ, Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|)) *
          (Ring.multichoose (|σ| + |y|) n * ‖z‖ ^ n)) =
        fun y : ℝ ↦ Cg * (1 + |y|) ^ Kg * Real.exp (-(2 * π * |y|)) *
          (1 / (1 - ‖z‖) ^ (|σ| + |y|)) from funext fun y ↦ (h_sum y).tsum_eq]
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

/-- Evaluation of DLMF 15.6.7 on the smaller disk `‖z‖ < 1 / 2` by expanding `(1 - z) ^ s` in its
binomial series and integrating term by term via `integral_four_Gamma_mul_multichoose`. -/
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
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) volume := by
    refine Continuous.aestronglyMeasurable <| (continuous_four_Gamma ha' hb' hc' hσ').mul ?_
    have hp_cont : Continuous fun y : ℝ ↦ (ascPochhammer ℂ n).eval (-((σ : ℂ) + y * I)) := by
      induction n with
      | zero => simp [continuous_const]
      | succ k ih =>
        simp only [ascPochhammer_succ_right, Polynomial.eval_mul, Polynomial.eval_add,
          Polynomial.eval_X, Polynomial.eval_natCast]
        exact ih.mul (by fun_prop)
    have hmc_eq (y : ℝ) : Ring.multichoose (-((σ : ℂ) + y * I)) n =
        (n ! : ℂ)⁻¹ * (ascPochhammer ℂ n).eval (-((σ : ℂ) + y * I)) := by
      have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (-((σ : ℂ) + y * I)) n
      rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_cast,
        Polynomial.ascPochhammer_smeval_eq_eval] at h
      rw [← h, inv_mul_cancel_left₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero)]
    simp_rw [hmc_eq]
    exact (continuous_const.mul hp_cont).mul continuous_const
  have h_bound (n : ℕ) : ∀ᵐ y : ℝ, ‖F n y‖ ≤ bound n y := by
    refine Eventually.of_forall fun y ↦ ?_
    have hnorm_le : ‖-((σ : ℂ) + y * I)‖ ≤ |σ| + |y| := by
      rw [norm_neg]; simpa using norm_le_abs_re_add_abs_im ((σ : ℂ) + y * I)
    have hmc := norm_multichoose_le_of_norm_le hnorm_le n
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
  have h_hasSum_int := hasSum_integral_of_dominated_convergence bound hF_meas h_bound
    h_bound_summable (integrable_tsum_multichoose_bound hCg Kg σ hz) h_lim
  have h_rhs_sum : HasSum (fun n : ℕ ↦ (regularizedGaussHGFunSeries a b c).coeff n * z ^ n)
      ((2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, G y * (1 - z) ^ ((σ : ℂ) + y * I)) := by
    simpa only [F, G, integral_four_Gamma_mul_multichoose a b c z hσ hσc haσ hbσ] using
      h_hasSum_int.mul_left (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹
  have hmem : z ∈ Metric.eball (0 : ℂ) (regularizedGaussHGFunSeries a b c).radius :=
    Metric.eball_subset_eball (radius_regularizedGaussHGFunSeries_ge_one a b c) <| by
      rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
  have h_lhs_sum : HasSum (fun n : ℕ ↦ (regularizedGaussHGFunSeries a b c).coeff n * z ^ n)
      (regularizedGaussHGFun a b c z) := by
    simpa [regularizedGaussHGFun, regularizedGaussHGFunSeries, regularizedHGFunSeries,
      FormalMultilinearSeries.ofScalars_apply_eq, coeff_regularizedGaussHGFunSeries, mul_comm] using
      (regularizedGaussHGFunSeries a b c).hasSum hmem
  simpa only [G, mul_assoc] using h_lhs_sum.unique h_rhs_sum

/-- **Mellin–Barnes integral for the regularized Gauss hypergeometric function**
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
      (analyticOnNhd_integral_mellinBarnesOneSubIntegrand ha' hb' hc' hσ' w h1w)
  have hfreq : ∃ᶠ w in 𝓝[≠] (0 : ℂ), regularizedGaussHGFun a b c w =
      (2 * π * Gamma a * Gamma b * Gamma (c - a) * Gamma (c - b))⁻¹ *
        ∫ y : ℝ, Gamma (a + (σ + y * I)) * Gamma (b + (σ + y * I)) *
          Gamma (c - a - b - (σ + y * I)) * Gamma (-(σ + y * I)) *
          (1 - w) ^ ((σ : ℂ) + y * I) := by
    let zseq : ℕ → ℂ := fun n ↦ (((n : ℝ) + 3)⁻¹ : ℝ)
    have htend : Tendsto zseq atTop (𝓝[≠] (0 : ℂ)) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, Eventually.of_forall fun n ↦ ?_⟩
      · have hreal : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 3)⁻¹) atTop (𝓝 (0 : ℝ)) :=
          tendsto_inv_atTop_zero.comp <|
            (tendsto_natCast_atTop_atTop (R := ℝ)).atTop_add (tendsto_const_nhds (x := (3 : ℝ)))
        exact (continuous_ofReal.tendsto 0).comp hreal
      · exact ofReal_ne_zero.mpr (by positivity)
    refine htend.frequently (Eventually.of_forall fun n : ℕ ↦ ?_).frequently
    have hnorm : ‖zseq n‖ < 1 / 2 := by
      simp only [zseq, norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ ((n : ℝ) + 3)⁻¹)]
      rw [inv_lt_comm₀ (by positivity) (by positivity)]
      norm_num
      linarith [n.cast_nonneg' (α := ℝ)]
    exact regularizedGaussHGFun_eq_mellinBarnes_one_sub_of_norm_lt_half a b c hnorm hσ hσc haσ hbσ
  exact h_lhs.eqOn_of_preconnected_of_frequently_eq h_rhs (convex_ball 0 1).isPreconnected
    (mem_ball_self zero_lt_one) hfreq (by simpa using hz)

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
