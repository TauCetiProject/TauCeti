/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.MellinTransform
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Mellin inversion, slit-plane holomorphy, and the first-order Perron cutoff

Mathlib's `mellinInv σ f y` is `(1 / 2π) ∫ y^{-(σ + i t)} • f(σ + i t) dt`. For positive real `y`
the kernel `t ↦ y^{-(σ + i t)}` has constant norm `y^{-σ}`, so integrability of `f` along the
vertical line `Re s = σ` implies integrability of the Mellin inversion integrand.

Evaluating this integral for `f(s) = 1 / (s(s + 1))` gives the continuous first-order cutoff
`max (1 - x) 0`, used for sums smoothed by `1 - n/x`. The migration motivating this computation is
the Prime Number Theorem and more project by Alex Kontorovich, Terence Tao and contributors,
`PrimeNumberTheoremAnd/PerronFormula.lean` (`Perron.formulaLtOne`, `Perron.formulaGtOne`). The proof
here composes Mathlib's interval-power Mellin transforms and Mellin inversion, independently of
that project's contour argument.

When the vertical profile `g y = f(σ + i y)` satisfies an exponential decay bound
`‖g y‖ ≤ C (1 + |y|) ^ R e^{-α |y|}` almost everywhere — such as the `α = π` or `α = 2π` decay
produced by Stirling's formula for balanced ratios of Gamma factors in Mellin–Barnes integrals —
the principal power `w ^ (±(σ + i y))` extends the integral from `(0, ∞)` to the sector
`{w : ℂ | w ∈ Complex.slitPlane ∧ |arg w| < α}` (which equals all of `Complex.slitPlane` when
`π ≤ α`): at each point `w₀` of that sector, `|arg w|` stays strictly below `α` on a neighborhood
in `slitPlane`, leaving positive exponential margin for integrability and differentiation under
the integral sign.

## Main results

* `Complex.VerticalIntegrable.integrable_cpow_smul`: the integrand of the Mellin inversion
  integral of a vertically integrable function is integrable for `y > 0`.
* `TauCeti.verticalIntegrable_inv_mul_add_one`: `1 / (s(s+1))` is integrable on lines avoiding
  `Re s = 0, -1`, including negative lines.
* `TauCeti.mellinInv_inv_mul_add_one`: its inverse Mellin transform is `max (1 - x) 0` for
  positive `x`, on every line `Re s = c > 0`.
* `TauCeti.integrable_cpow_div_mul_add_one`: absolute convergence of `x^s / (s(s+1))` for
  `x ≥ 0` on every line avoiding the two poles.
* `TauCeti.integral_cpow_div_mul_add_one`: its integral is `2π * max (1 - 1/x) 0` for
  positive `x` and `c`. At the cutoff `x = 1` this value is zero.
* `TauCeti.integrable_cpow_smul_of_norm_le_exp_neg_mul_abs`,
  `TauCeti.integrable_cpow_neg_smul_of_norm_le_exp_neg_mul_abs`: integrability on `ℝ` of
  `y ↦ w ^ (±(σ + i y)) • g y` whenever `|arg w| < α` and
  `‖g y‖ = O((1 + |y|) ^ R e^{-α |y|})` almost everywhere.
* `TauCeti.hasDerivAt_integral_cpow_smul`, `TauCeti.hasDerivAt_integral_cpow_neg_smul`:
  differentiation under the integral sign at any `w₀ ∈ Complex.slitPlane` with `|arg w₀| < α`.
* `TauCeti.differentiableOn_integral_cpow_smul`, `TauCeti.analyticOnNhd_integral_cpow_smul`,
  `TauCeti.differentiableOn_integral_cpow_neg_smul`,
  `TauCeti.analyticOnNhd_integral_cpow_neg_smul`: complex differentiability and holomorphy on
  `{w : ℂ | w ∈ Complex.slitPlane ∧ |arg w| < α}`.
-/

public section

open Real Set MeasureTheory Filter Topology
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

/-- The kernel `1 / (s(s+1))` is integrable on each vertical line avoiding its two poles. -/
theorem verticalIntegrable_inv_mul_add_one {c : ℝ} (hc : c ≠ 0) (hc1 : c ≠ -1) :
    VerticalIntegrable (fun s : ℂ ↦ (s * (s + 1))⁻¹) c := by
  let d := min |c| |c + 1|
  have h1 : c + 1 ≠ 0 := by simpa using sub_ne_zero.mpr hc1
  have hd : 0 < d := lt_min (abs_pos.mpr hc) (abs_pos.mpr h1)
  have hmajor : Integrable (fun t : ℝ ↦ (d ^ 2 + t ^ 2)⁻¹) := by
    simpa only [add_comm] using (integrable_inv_sq_add_sq hd.ne')
  refine hmajor.mono' (by fun_prop) (Filter.Eventually.of_forall fun t ↦ ?_)
  rw [norm_inv, norm_mul]
  have hnorm (a : ℝ) (ha : d ≤ |a|) :
      Real.sqrt (d ^ 2 + t ^ 2) ≤ ‖(a : ℂ) + t * I‖ := by
    apply (Real.sqrt_le_left (norm_nonneg _)).mpr
    rw [Complex.sq_norm, Complex.normSq_add_mul_I]
    nlinarith only [ha, hd.le, sq_abs a]
  have hshift : (c : ℂ) + t * I + 1 = ((c + 1 : ℝ) : ℂ) + t * I := by
    push_cast
    ring
  apply inv_anti₀ (by positivity)
  calc
    d ^ 2 + t ^ 2 = (Real.sqrt (d ^ 2 + t ^ 2)) ^ 2 :=
      (Real.sq_sqrt (by positivity)).symm
    _ ≤ ‖(c : ℂ) + t * I‖ * ‖(c : ℂ) + t * I + 1‖ := by
      rw [sq, hshift]
      exact mul_le_mul (hnorm c (min_le_left _ _)) (hnorm (c + 1) (min_le_right _ _))
        (Real.sqrt_nonneg _) (norm_nonneg _)

/-- The inverse Mellin transform of `1 / (s(s+1))` is the continuous first-order cutoff. -/
theorem mellinInv_inv_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    mellinInv c (fun s : ℂ ↦ (s * (s + 1))⁻¹) x = (max (1 - x) 0 : ℝ) := by
  have hm (t : ℝ) : mellin (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) ((c : ℂ) + t * I) =
      ((((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))⁻¹) :=
    (hasMellin_max_one_sub_zero (by simpa using hc)).2
  have hv : VerticalIntegrable (mellin (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ))) c := by
    simpa only [VerticalIntegrable, hm] using
      verticalIntegrable_inv_mul_add_one hc.ne' (by linarith)
  have h := mellinInv_mellin_eq c (fun u : ℝ ↦ ((max (1 - u) 0 : ℝ) : ℂ)) hx
    (hasMellin_max_one_sub_zero (by simpa using hc)).1 hv (by fun_prop)
  rw [mellinInv] at h ⊢
  simpa only [hm] using h

private lemma riesz_integrand_eq {x : ℝ} (hx : 0 ≤ x) (s : ℂ) :
    ((x⁻¹ : ℝ) : ℂ) ^ (-s) • (s * (s + 1))⁻¹ = (x : ℂ) ^ s / (s * (s + 1)) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow_ofReal_nonneg hx, Complex.cpow_neg, inv_inv,
    smul_eq_mul, ← div_eq_mul_inv]

/-- The first-order Perron kernel is absolutely integrable for `x ≥ 0` on every line away from
`Re s = 0, -1`. At `x = 0` the integrand vanishes. -/
theorem integrable_cpow_div_mul_add_one {c x : ℝ} (hc : c ≠ 0) (hc1 : c ≠ -1) (hx : 0 ≤ x) :
    Integrable (fun t : ℝ ↦ (x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) := by
  rcases hx.eq_or_lt with rfl | hx
  · have hz (t : ℝ) : (c : ℂ) + t * I ≠ 0 := by
      intro h
      apply hc
      simpa using congrArg Complex.re h
    apply (integrable_zero ℝ ℂ volume).congr
    exact Filter.Eventually.of_forall fun t ↦ by
      simp only [Pi.zero_apply, Complex.ofReal_zero, Complex.zero_cpow (hz t), zero_div]
  · simpa only [riesz_integrand_eq hx.le] using
      (verticalIntegrable_inv_mul_add_one hc hc1).integrable_cpow_smul (inv_pos.mpr hx)

/-- The integral of `x^s / (s(s+1))` on a positive vertical line is the continuous cutoff
weight times `2π`. In particular, its value at `x = 1` is zero. -/
theorem integral_cpow_div_mul_add_one {c x : ℝ} (hc : 0 < c) (hx : 0 < x) :
    (∫ t : ℝ, (x : ℂ) ^ ((c : ℂ) + t * I) /
      (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))) =
      ((2 * π : ℝ) : ℂ) * (max (1 - x⁻¹) 0 : ℝ) := by
  have h := mellinInv_inv_mul_add_one hc (inv_pos.mpr hx)
  simp only [mellinInv, riesz_integrand_eq hx.le] at h
  have hπ : ((2 * π : ℝ) : ℂ) ≠ 0 := by exact_mod_cast mul_ne_zero two_ne_zero pi_ne_zero
  apply (inv_mul_eq_iff_eq_mul₀ hπ).mp
  simpa only [Complex.real_smul, one_div, Complex.ofReal_inv] using h

/-- If `g : ℝ → E` is strongly measurable and satisfies
`‖g y‖ ≤ C (1 + |y|) ^ R e^{-α |y|}` almost everywhere, then `y ↦ w ^ (σ + i y) • g y` is
integrable on `ℝ` for every `σ : ℝ` and every `w : ℂ` with `|arg w| < α`. -/
theorem integrable_cpow_smul_of_norm_le_exp_neg_mul_abs {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} {α : ℝ} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ᵐ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-α * |y|))
    (σ : ℝ) {w : ℂ} (harg : |w.arg| < α) :
    Integrable fun y : ℝ ↦ w ^ ((σ : ℂ) + y * I) • g y := by
  rcases eq_or_ne w 0 with rfl | hw
  · refine (integrable_zero ℝ E volume).congr ?_
    have hne : ∀ᵐ y : ℝ, y ≠ 0 := by rw [ae_iff]; simp
    filter_upwards [hne] with y hy
    have hs : (σ : ℂ) + y * I ≠ 0 := fun h ↦ hy (by simpa using congrArg Complex.im h)
    simp [Complex.zero_cpow hs]
  obtain ⟨C, R, hg⟩ := hg_bound
  set C' : ℝ := max C 0
  set δ : ℝ := α - |w.arg|
  have hδ : 0 < δ := sub_pos.2 harg
  refine ((integrable_one_add_abs_rpow_mul_exp_neg_mul_abs R hδ).const_mul
    (‖w‖ ^ σ * C')).mono'
    ((Continuous.const_cpow (by fun_prop) (Or.inl hw)).aestronglyMeasurable.smul hg_meas) ?_
  filter_upwards [hg] with y hgy
  have hg' : ‖g y‖ ≤ C' * (1 + |y|) ^ R * Real.exp (-α * |y|) :=
    hgy.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)) (Real.exp_nonneg _))
  have hpow : ‖w ^ ((σ : ℂ) + y * I)‖ ≤ ‖w‖ ^ σ * Real.exp (|w.arg| * |y|) := by
    simpa using Complex.norm_cpow_le_rpow_mul_exp_abs_arg_mul_abs_im w ((σ : ℂ) + y * I)
  rw [norm_smul]
  calc ‖w ^ ((σ : ℂ) + y * I)‖ * ‖g y‖
      ≤ (‖w‖ ^ σ * Real.exp (|w.arg| * |y|)) * (C' * (1 + |y|) ^ R * Real.exp (-α * |y|)) :=
        mul_le_mul hpow hg' (norm_nonneg _) (by positivity)
    _ = ‖w‖ ^ σ * C' * ((1 + |y|) ^ R * (Real.exp (|w.arg| * |y|) * Real.exp (-α * |y|))) := by
        ring
    _ = ‖w‖ ^ σ * C' * ((1 + |y|) ^ R * Real.exp (-δ * |y|)) := by
        rw [← Real.exp_add]; dsimp [δ]; ring_nf

/-- Negated-exponent companion to `TauCeti.integrable_cpow_smul_of_norm_le_exp_neg_mul_abs`:
`y ↦ w ^ (-(σ + i y)) • g y` is integrable on `ℝ` whenever `|arg w| < α`. -/
theorem integrable_cpow_neg_smul_of_norm_le_exp_neg_mul_abs {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} {α : ℝ} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ᵐ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-α * |y|))
    (σ : ℝ) {w : ℂ} (harg : |w.arg| < α) :
    Integrable fun y : ℝ ↦ w ^ (-((σ : ℂ) + y * I)) • g y := by
  obtain ⟨C, R, hg⟩ := hg_bound
  have hqmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  have hg_neg : ∀ᵐ y : ℝ, ‖g (-y)‖ ≤ C * (1 + |y|) ^ R * Real.exp (-α * |y|) := by
    filter_upwards [hqmp.tendsto_ae.eventually hg] with y hy
    simpa [abs_neg] using hy
  have h := integrable_cpow_smul_of_norm_le_exp_neg_mul_abs
    (hg_meas.comp_quasiMeasurePreserving hqmp) ⟨C, R, hg_neg⟩ (-σ) harg
  refine h.comp_neg.congr (Eventually.of_forall fun y ↦ ?_)
  simp only [Function.comp_def, neg_neg, ofReal_neg]; congr 2; ring

/-- **Differentiation under a Mellin–Barnes integral.** If `g : ℝ → E` is strongly measurable and
satisfies `‖g y‖ ≤ C (1 + |y|) ^ R e^{-α |y|}` almost everywhere, then
`w ↦ ∫ y : ℝ, w ^ (σ + i y) • g y` has complex derivative
`∫ y : ℝ, ((σ + i y) * w₀ ^ (σ + i y - 1)) • g y` at every `w₀ ∈ Complex.slitPlane` with
`|arg w₀| < α`. -/
theorem hasDerivAt_integral_cpow_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} {α : ℝ} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ᵐ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-α * |y|))
    (σ : ℝ) {w₀ : ℂ} (hw₀ : w₀ ∈ slitPlane) (harg : |w₀.arg| < α) :
    HasDerivAt (fun w : ℂ ↦ ∫ y : ℝ, w ^ ((σ : ℂ) + y * I) • g y)
      (∫ y : ℝ, (((σ : ℂ) + y * I) * w₀ ^ ((σ : ℂ) + y * I - 1)) • g y) w₀ := by
  obtain ⟨C, R, hg⟩ := hg_bound
  set C' : ℝ := max C 0
  obtain ⟨U, hU, r₀, r₁, α', hr₀, hα', hU_bounds⟩ :=
    Complex.exists_mem_nhds_slitPlane_norm_and_arg_lt hw₀ harg
  set δ : ℝ := α - α'
  have hδ : 0 < δ := sub_pos.2 hα'
  set M₁ : ℝ := max (r₀ ^ (σ - 1)) (r₁ ^ (σ - 1))
  set S : ℝ := max |σ| 1
  have : 0 < M₁ := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have : 0 < S := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hF_meas : ∀ᶠ w in 𝓝 w₀, AEStronglyMeasurable (fun y : ℝ ↦ w ^ ((σ : ℂ) + y * I) • g y) :=
    Filter.eventually_of_mem hU fun w hw ↦
      (Continuous.const_cpow (by fun_prop)
        (Or.inl (slitPlane_ne_zero (hU_bounds w hw).1))).aestronglyMeasurable.smul hg_meas
  have hF'_meas : AEStronglyMeasurable
      (fun y : ℝ ↦ (((σ : ℂ) + y * I) * w₀ ^ ((σ : ℂ) + y * I - 1)) • g y) :=
    ((Continuous.mul (by fun_prop) (Continuous.const_cpow (by fun_prop)
      (Or.inl (slitPlane_ne_zero hw₀)))).aestronglyMeasurable).smul hg_meas
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun (w : ℂ) (y : ℝ) ↦ w ^ ((σ : ℂ) + y * I) • g y)
    (F' := fun (w : ℂ) (y : ℝ) ↦ (((σ : ℂ) + y * I) * w ^ ((σ : ℂ) + y * I - 1)) • g y)
    (bound := fun y : ℝ ↦ S * M₁ * C' * ((1 + |y|) ^ (R + 1) * Real.exp (-δ * |y|)))
    hU hF_meas (integrable_cpow_smul_of_norm_le_exp_neg_mul_abs hg_meas ⟨C, R, hg⟩ σ harg)
    hF'_meas ?_ ((integrable_one_add_abs_rpow_mul_exp_neg_mul_abs (R + 1) hδ).const_mul _) ?_).2
  · filter_upwards [hg] with y hgy w hw
    obtain ⟨_, hw_lo, hw_hi, hw_arg⟩ := hU_bounds w hw
    have hs_norm : ‖(σ : ℂ) + y * I‖ ≤ S * (1 + |y|) :=
      (norm_add_le _ _).trans <| by
        simp only [Complex.norm_real, Real.norm_eq_abs, norm_mul, Complex.norm_I, mul_one]
        nlinarith [le_max_left |σ| 1, le_max_right |σ| 1, abs_nonneg y]
    have hw_pow : ‖w ^ ((σ : ℂ) + y * I - 1)‖ ≤ M₁ * Real.exp (α' * |y|) := by
      simpa using Complex.norm_cpow_le_max_rpow_mul_exp hr₀ hw_lo hw_hi hw_arg ((σ : ℂ) + y * I - 1)
    have hg' : ‖g y‖ ≤ C' * (1 + |y|) ^ R * Real.exp (-α * |y|) :=
      hgy.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)) (Real.exp_nonneg _))
    rw [norm_smul, norm_mul]
    calc ‖(σ : ℂ) + y * I‖ * ‖w ^ ((σ : ℂ) + y * I - 1)‖ * ‖g y‖
        ≤ (S * (1 + |y|)) * (M₁ * Real.exp (α' * |y|)) *
            (C' * (1 + |y|) ^ R * Real.exp (-α * |y|)) :=
          mul_le_mul (mul_le_mul hs_norm hw_pow (norm_nonneg _) (by positivity)) hg'
            (norm_nonneg _) (by positivity)
      _ = S * M₁ * C' * ((1 + |y|) ^ R * (1 + |y|)) *
            (Real.exp (α' * |y|) * Real.exp (-α * |y|)) := by ring
      _ = S * M₁ * C' * ((1 + |y|) ^ (R + 1) * Real.exp (-δ * |y|)) := by
          rw [← Real.rpow_add_one (by linarith [abs_nonneg y] : (1 + |y|) ≠ 0), ← Real.exp_add]
          dsimp [δ]; ring_nf
  · exact Eventually.of_forall fun y w hw ↦
      (Complex.hasStrictDerivAt_cpow_const (hU_bounds w hw).1).hasDerivAt.smul_const (g y)

/-- Negated-exponent companion to `TauCeti.hasDerivAt_integral_cpow_smul`:
`w ↦ ∫ y : ℝ, w ^ (-(σ + i y)) • g y` has complex derivative
`∫ y : ℝ, (-(σ + i y) * w₀ ^ (-(σ + i y) - 1)) • g y` at every `w₀ ∈ Complex.slitPlane` with
`|arg w₀| < α`. -/
theorem hasDerivAt_integral_cpow_neg_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} {α : ℝ} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ᵐ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-α * |y|))
    (σ : ℝ) {w₀ : ℂ} (hw₀ : w₀ ∈ slitPlane) (harg : |w₀.arg| < α) :
    HasDerivAt (fun w : ℂ ↦ ∫ y : ℝ, w ^ (-((σ : ℂ) + y * I)) • g y)
      (∫ y : ℝ, (-((σ : ℂ) + y * I) * w₀ ^ (-((σ : ℂ) + y * I) - 1)) • g y) w₀ := by
  obtain ⟨C, R, hg⟩ := hg_bound
  have hqmp := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving
  have hg_neg : ∀ᵐ y : ℝ, ‖g (-y)‖ ≤ C * (1 + |y|) ^ R * Real.exp (-α * |y|) := by
    filter_upwards [hqmp.tendsto_ae.eventually hg] with y hy
    simpa [abs_neg] using hy
  have h := hasDerivAt_integral_cpow_smul (g := fun y ↦ g (-y))
    (hg_meas.comp_quasiMeasurePreserving hqmp) ⟨C, R, hg_neg⟩ (-σ) hw₀ harg
  refine (h.congr_of_eventuallyEq (Eventually.of_forall fun w ↦ ?_)).congr_deriv ?_
  · rw [← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [ofReal_neg]; congr 2; ring
  · rw [← integral_neg_eq_self]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [ofReal_neg, neg_neg]
    rw [show -(σ : ℂ) + -(y : ℂ) * I = -((σ : ℂ) + y * I) by ring]

/-- If `g : ℝ → E` is strongly measurable and satisfies
`‖g y‖ ≤ C (1 + |y|) ^ R e^{-α |y|}` almost everywhere, then `w ↦ ∫ y : ℝ, w ^ (σ + i y) • g y`
is complex differentiable on `{w : ℂ | w ∈ Complex.slitPlane ∧ |arg w| < α}`. -/
theorem differentiableOn_integral_cpow_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} {α : ℝ} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ᵐ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-α * |y|)) (σ : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ ↦ ∫ y : ℝ, w ^ ((σ : ℂ) + y * I) • g y)
      {w : ℂ | w ∈ slitPlane ∧ |w.arg| < α} :=
  fun _ hw ↦ (hasDerivAt_integral_cpow_smul hg_meas hg_bound σ
    hw.1 hw.2).differentiableAt.differentiableWithinAt

/-- If `g : ℝ → E` is strongly measurable and satisfies
`‖g y‖ ≤ C (1 + |y|) ^ R e^{-α |y|}` almost everywhere, then `w ↦ ∫ y : ℝ, w ^ (σ + i y) • g y`
is holomorphic on `{w : ℂ | w ∈ Complex.slitPlane ∧ |arg w| < α}`. -/
theorem analyticOnNhd_integral_cpow_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {g : ℝ → E} {α : ℝ} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ᵐ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-α * |y|)) (σ : ℝ) :
    AnalyticOnNhd ℂ (fun w : ℂ ↦ ∫ y : ℝ, w ^ ((σ : ℂ) + y * I) • g y)
      {w : ℂ | w ∈ slitPlane ∧ |w.arg| < α} :=
  (differentiableOn_integral_cpow_smul hg_meas hg_bound σ).analyticOnNhd
    (isOpen_slitPlane_inter_abs_arg_lt α)

/-- Negated-exponent companion to `TauCeti.differentiableOn_integral_cpow_smul`:
`w ↦ ∫ y : ℝ, w ^ (-(σ + i y)) • g y` is complex differentiable on
`{w : ℂ | w ∈ Complex.slitPlane ∧ |arg w| < α}`. -/
theorem differentiableOn_integral_cpow_neg_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {g : ℝ → E} {α : ℝ} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ᵐ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-α * |y|)) (σ : ℝ) :
    DifferentiableOn ℂ (fun w : ℂ ↦ ∫ y : ℝ, w ^ (-((σ : ℂ) + y * I)) • g y)
      {w : ℂ | w ∈ slitPlane ∧ |w.arg| < α} :=
  fun _ hw ↦ (hasDerivAt_integral_cpow_neg_smul hg_meas hg_bound σ
    hw.1 hw.2).differentiableAt.differentiableWithinAt

/-- Negated-exponent companion to `TauCeti.analyticOnNhd_integral_cpow_smul`:
`w ↦ ∫ y : ℝ, w ^ (-(σ + i y)) • g y` is holomorphic on
`{w : ℂ | w ∈ Complex.slitPlane ∧ |arg w| < α}`. -/
theorem analyticOnNhd_integral_cpow_neg_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {g : ℝ → E} {α : ℝ} (hg_meas : AEStronglyMeasurable g)
    (hg_bound : ∃ C R : ℝ, ∀ᵐ y : ℝ, ‖g y‖ ≤ C * (1 + |y|) ^ R * Real.exp (-α * |y|)) (σ : ℝ) :
    AnalyticOnNhd ℂ (fun w : ℂ ↦ ∫ y : ℝ, w ^ (-((σ : ℂ) + y * I)) • g y)
      {w : ℂ | w ∈ slitPlane ∧ |w.arg| < α} :=
  (differentiableOn_integral_cpow_neg_smul hg_meas hg_bound σ).analyticOnNhd
    (isOpen_slitPlane_inter_abs_arg_lt α)

end TauCeti
