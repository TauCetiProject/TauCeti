/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.EndFraming
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.SpecialFunctions.JapaneseBracket.Basic

/-!
# The background of a vortex divisor and the regular scalar equation

Let `D` be an effective divisor of degree `m` on the plane, a multiset of points `a ∈ ℂ`, and let
`P_D = ∏_{a ∈ D} (X - a)` be the monic polynomial with root multiset `D`. By
`TauCeti.Vortex.equation_amplitudeField_eq_zero_iff` and
`TauCeti.Vortex.tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log`, the field
`amplitudeField u P_D` is a framed degree-`m` vortex exactly when `u` solves the scalar problem

`Δu = (exp (2u) |P_D|² - 1) / 8`,  `u(z) + m log |z| → 0` at infinity.

Following Taubes, fix `c > 0` and split off the explicit **background potential**
`b(z) = -(1/2) ∑_{a ∈ D} log (|z - a|² + c)` (`backgroundPotential`), writing `u = b + w / 2`.
The background is smooth, with `b(z) + m log |z| → 0`, and

* `Δb = -g / 2` for the **background source** `g(z) = ∑_{a ∈ D} 4 c / (|z - a|² + c)²`
  (`backgroundSource`), a smooth function with `0 ≤ g ≤ 4 m / c` and `∫ g = 4π m`;
* `exp (2b) |P_D|² = ρ` for the **background density**
  `ρ(z) = ∏_{a ∈ D} |z - a|² / (|z - a|² + c)` (`backgroundDensity`), a smooth function with
  `0 ≤ ρ ≤ 1` and `1 - ρ ∈ L²`.

Consequently (`laplacian_backgroundPotential_add_eq_iff`,
`tendsto_backgroundPotential_add_add_mul_log_iff`) the scalar problem for `u` is equivalent to the
**regular scalar equation**

`Δw = (ρ exp w - 1) / 4 + g`,  `w → 0` at infinity,

whose coefficients are smooth and bounded, with no point masses at the zeros and no logarithmic
growth. For a `C²` function `w` this is exactly the condition for the reconstructed field to be a
framed vortex (`equation_amplitudeField_backgroundPotential_eq_zero_iff`,
`tendsto_sectionValue_amplitudeField_backgroundPotential_iff`), and its section vanishes at each
`a` to the order `count a D` (`exists_sectionValue_amplitudeField_eq_pow_count_mul`), so repeated
points of `D` are included. The total `∫ g = 4π m` is the mass of the point charges
`4π ∑ n_z δ_z` in the distributional equation for `log |α|²`
(`TauCeti.Vortex.integral_laplacian_mul_log_normSq`), now spread smoothly over the plane.

In the notation of Jaffe and Taubes, `ρ = exp u₀` and `g` is their `g₀`, with their parameter `λ`
equal to `c`; the factor `1 / 4` in the regular equation reflects the curvature normalization
`*iF_a = (1 - |α|²) / 8` of `TauCeti.Vortex.equation`. The existence of a solution `w` of the
regular equation is not proved here.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, §3.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg-Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter InnerProductSpace Laplacian MeasureTheory Polynomial Topology

/-- The background potential `b(z) = -(1/2) ∑_{a ∈ D} log (|z - a|² + c)` of a divisor `D`.
For `c > 0` it is smooth, and `exp (2b) |P_D|²` is the background density
(`exp_two_mul_backgroundPotential_mul_norm_eval_sq`). -/
def backgroundPotential (D : Multiset ℂ) (c : ℝ) (z : ℂ) : ℝ :=
  -(D.map fun a ↦ Real.log (‖z - a‖ ^ 2 + c)).sum / 2

/-- The background source `g(z) = ∑_{a ∈ D} 4 c / (|z - a|² + c)²`, so that
`Δb = -g / 2` for the background potential `b` (`laplacian_backgroundPotential`). -/
def backgroundSource (D : Multiset ℂ) (c : ℝ) (z : ℂ) : ℝ :=
  (D.map fun a ↦ 4 * c / (‖z - a‖ ^ 2 + c) ^ 2).sum

/-- The background density `ρ(z) = ∏_{a ∈ D} |z - a|² / (|z - a|² + c)`, the coefficient of the
nonlinearity in the regular scalar equation. -/
def backgroundDensity (D : Multiset ℂ) (c : ℝ) (z : ℂ) : ℝ :=
  (D.map fun a ↦ ‖z - a‖ ^ 2 / (‖z - a‖ ^ 2 + c)).prod

variable {D : Multiset ℂ} {c : ℝ}

@[simp]
theorem backgroundPotential_zero (c : ℝ) : backgroundPotential 0 c = 0 := by
  funext z
  simp [backgroundPotential]

@[simp]
theorem backgroundPotential_cons (a : ℂ) (D : Multiset ℂ) (c : ℝ) (z : ℂ) :
    backgroundPotential (a ::ₘ D) c z =
      -Real.log (‖z - a‖ ^ 2 + c) / 2 + backgroundPotential D c z := by
  simp only [backgroundPotential, Multiset.map_cons, Multiset.sum_cons]
  ring

@[simp]
theorem backgroundSource_zero (c : ℝ) : backgroundSource 0 c = 0 := by
  funext z
  simp [backgroundSource]

@[simp]
theorem backgroundSource_cons (a : ℂ) (D : Multiset ℂ) (c : ℝ) (z : ℂ) :
    backgroundSource (a ::ₘ D) c z =
      4 * c / (‖z - a‖ ^ 2 + c) ^ 2 + backgroundSource D c z := by
  simp [backgroundSource]

@[simp]
theorem backgroundDensity_zero (c : ℝ) : backgroundDensity 0 c = 1 := by
  funext z
  simp [backgroundDensity]

@[simp]
theorem backgroundDensity_cons (a : ℂ) (D : Multiset ℂ) (c : ℝ) (z : ℂ) :
    backgroundDensity (a ::ₘ D) c z =
      ‖z - a‖ ^ 2 / (‖z - a‖ ^ 2 + c) * backgroundDensity D c z := by
  simp [backgroundDensity]

private theorem contDiff_log_norm_sub_sq_add (a : ℂ) (hc : 0 < c) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun z : ℂ ↦ Real.log (‖z - a‖ ^ 2 + c) :=
  (((contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)).add contDiff_const).log
    fun z ↦ by
      simp only [Function.comp_apply, id]
      positivity

/-- For `c > 0` the background potential is smooth. -/
theorem contDiff_backgroundPotential (D : Multiset ℂ) (hc : 0 < c) {n : WithTop ℕ∞} :
    ContDiff ℝ n (backgroundPotential D c) := by
  induction D using Multiset.induction_on with
  | empty =>
    rw [backgroundPotential_zero]
    exact contDiff_zero_fun
  | cons a D ih =>
    have hfun : backgroundPotential (a ::ₘ D) c =
        fun z ↦ -Real.log (‖z - a‖ ^ 2 + c) / 2 + backgroundPotential D c z :=
      funext (backgroundPotential_cons a D c)
    rw [hfun]
    exact ((contDiff_log_norm_sub_sq_add a hc).neg.div_const _).add ih

/-- The Laplacian of the background potential is `-g / 2`, for the background source `g`. -/
theorem laplacian_backgroundPotential (D : Multiset ℂ) (hc : 0 < c) (z : ℂ) :
    Δ (backgroundPotential D c) z = -backgroundSource D c z / 2 := by
  induction D using Multiset.induction_on with
  | empty =>
    have h := laplacian_const (E := ℂ) (c := (0 : ℝ))
    simp only [backgroundPotential_zero, backgroundSource_zero, Pi.zero_apply, neg_zero, zero_div]
    exact congrFun h z
  | cons a D ih =>
    have hfun : backgroundPotential (a ::ₘ D) c =
        (fun z : ℂ ↦ -Real.log (‖z - a‖ ^ 2 + c) / 2) + backgroundPotential D c :=
      funext fun w ↦ by simp [backgroundPotential_cons]
    have h₁ : ContDiffAt ℝ 2 (fun z : ℂ ↦ -Real.log (‖z - a‖ ^ 2 + c) / 2) z :=
      ((contDiff_log_norm_sub_sq_add a hc).neg.div_const _).contDiffAt
    have hlog : Δ (fun z : ℂ ↦ Real.log (‖z - a‖ ^ 2 + c)) z =
        4 * c / (‖z - a‖ ^ 2 + c) ^ 2 := by
      have := congrFun (laplacian_comp_add_right
        (fun y : ℂ ↦ Real.log (‖y‖ ^ 2 + c)) (-a)) z
      simp only [← sub_eq_add_neg] at this
      rw [this, TauCeti.laplacian_log_norm_sq_add hc, Complex.finrank_real_complex]
      field_simp
      ring
    have hhalf : Δ (fun z : ℂ ↦ -Real.log (‖z - a‖ ^ 2 + c) / 2) z =
        -(4 * c / (‖z - a‖ ^ 2 + c) ^ 2) / 2 := by
      have hs := laplacian_smul (x := z) (-(1 / 2) : ℝ)
        ((contDiff_log_norm_sub_sq_add a hc (n := 2)).contDiffAt)
      rw [← hlog]
      convert hs using 2
      · funext w
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      · simp only [smul_eq_mul]
        ring
    rw [hfun, ContDiffAt.laplacian_add h₁
      (contDiff_backgroundPotential D hc).contDiffAt, hhalf, ih, backgroundSource_cons]
    ring

/-- The background potential divides out the modulus of the divisor polynomial:
`exp (2b) |P_D|² = ρ`. -/
theorem exp_two_mul_backgroundPotential_mul_norm_eval_sq (D : Multiset ℂ) (hc : 0 < c)
    (z : ℂ) :
    Real.exp (2 * backgroundPotential D c z) * ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2 =
      backgroundDensity D c z := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons a D ih =>
    have hpos : 0 < ‖z - a‖ ^ 2 + c := by positivity
    rw [backgroundPotential_cons, backgroundDensity_cons, ← ih]
    simp only [Multiset.map_cons, Multiset.prod_cons, eval_mul, eval_sub, eval_X, eval_C,
      norm_mul, mul_pow]
    rw [show 2 * (-Real.log (‖z - a‖ ^ 2 + c) / 2 + backgroundPotential D c z) =
        -Real.log (‖z - a‖ ^ 2 + c) + 2 * backgroundPotential D c z by ring,
      Real.exp_add, Real.exp_neg, Real.exp_log hpos]
    field_simp

theorem backgroundSource_nonneg (D : Multiset ℂ) (hc : 0 ≤ c) (z : ℂ) :
    0 ≤ backgroundSource D c z :=
  Multiset.sum_nonneg fun _ hx ↦ by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
    positivity

/-- The background source is bounded by `4 m / c`, where `m` is the degree of the divisor. -/
theorem backgroundSource_le (D : Multiset ℂ) (hc : 0 < c) (z : ℂ) :
    backgroundSource D c z ≤ 4 * D.card / c := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons a D ih =>
    rw [backgroundSource_cons, Multiset.card_cons]
    have h : 4 * c / (‖z - a‖ ^ 2 + c) ^ 2 ≤ 4 / c := by
      rw [div_le_div_iff₀ (by positivity) hc]
      nlinarith [sq_nonneg ‖z - a‖, norm_nonneg (z - a)]
    have h' : 4 * ((D.card + 1 : ℕ) : ℝ) / c = 4 / c + 4 * D.card / c := by
      push_cast
      ring
    linarith

theorem backgroundDensity_nonneg (D : Multiset ℂ) (hc : 0 ≤ c) (z : ℂ) :
    0 ≤ backgroundDensity D c z :=
  Multiset.prod_nonneg fun _ hx ↦ by
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hx
    positivity

theorem backgroundDensity_le_one (D : Multiset ℂ) (hc : 0 ≤ c) (z : ℂ) :
    backgroundDensity D c z ≤ 1 := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons a D ih =>
    rw [backgroundDensity_cons]
    have ht : ‖z - a‖ ^ 2 / (‖z - a‖ ^ 2 + c) ≤ 1 := by
      rcases (add_nonneg (sq_nonneg ‖z - a‖) hc).eq_or_lt with h | h
      · simp [← h]
      · exact (div_le_one h).2 (by linarith)
    simpa using mul_le_mul ht ih (backgroundDensity_nonneg D hc z) zero_le_one

/-- The defect `1 - ρ` is bounded by the sum `∑_{a ∈ D} c / (|z - a|² + c)` of the defects of
the single points of `D`, which decay like `|z|⁻²`. -/
theorem one_sub_backgroundDensity_le (D : Multiset ℂ) (hc : 0 < c) (z : ℂ) :
    1 - backgroundDensity D c z ≤ (D.map fun a ↦ c / (‖z - a‖ ^ 2 + c)).sum := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons a D ih =>
    have hpos : 0 < ‖z - a‖ ^ 2 + c := by positivity
    set t := ‖z - a‖ ^ 2 / (‖z - a‖ ^ 2 + c)
    have ht₀ : 0 ≤ t := by positivity
    have ht₁ : t ≤ 1 := (div_le_one hpos).2 (by linarith)
    have hρ := backgroundDensity_le_one D hc.le z
    have hct : 1 - t = c / (‖z - a‖ ^ 2 + c) := by
      simp only [t]
      field_simp
      ring
    rw [backgroundDensity_cons, Multiset.map_cons, Multiset.sum_cons, ← hct]
    nlinarith [backgroundDensity_nonneg D hc.le z]

private theorem tendsto_neg_log_norm_sub_sq_add_div_two_add_log (a : ℂ) (hc : 0 < c) :
    Tendsto (fun z : ℂ ↦ -Real.log (‖z - a‖ ^ 2 + c) / 2 + Real.log ‖z‖) (cocompact ℂ)
      (𝓝 0) := by
  have hz : ∀ᶠ z : ℂ in cocompact ℂ, z ≠ 0 :=
    (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have hinv : Tendsto (fun z : ℂ ↦ z⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  have hg : Continuous fun w : ℂ ↦ ‖1 - a * w‖ ^ 2 + c * ‖w‖ ^ 2 := by fun_prop
  have hlim : Tendsto (fun z : ℂ ↦ ‖1 - a * z⁻¹‖ ^ 2 + c * ‖z⁻¹‖ ^ 2) (cocompact ℂ) (𝓝 1) := by
    have h1 : ‖1 - a * 0‖ ^ 2 + c * ‖(0 : ℂ)‖ ^ 2 = 1 := by norm_num
    have h := (hg.tendsto 0).comp hinv
    rwa [h1] at h
  have hlog := ((Real.continuousAt_log one_ne_zero).tendsto.comp hlim).div_const (-2)
  rw [Real.log_one, zero_div] at hlog
  refine hlog.congr' ?_
  filter_upwards [hz] with z hz
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  have hq : ‖1 - a * z⁻¹‖ ^ 2 + c * ‖z⁻¹‖ ^ 2 = (‖z - a‖ ^ 2 + c) / ‖z‖ ^ 2 := by
    have h1 : 1 - a * z⁻¹ = (z - a) / z := by field_simp
    rw [h1, norm_div, norm_inv]
    field_simp
  rw [Function.comp_apply, hq, Real.log_div (by positivity) (by positivity), Real.log_pow]
  push_cast
  ring

/-- The background potential has the logarithmic growth `-m log |z|` of a degree-`m` framing:
`b(z) + m log |z| → 0` at infinity. -/
theorem tendsto_backgroundPotential_add_mul_log (D : Multiset ℂ) (hc : 0 < c) :
    Tendsto (fun z ↦ backgroundPotential D c z + D.card * Real.log ‖z‖) (cocompact ℂ)
      (𝓝 0) := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons a D ih =>
    have h := (tendsto_neg_log_norm_sub_sq_add_div_two_add_log a hc).add ih
    rw [add_zero] at h
    refine h.congr fun z ↦ ?_
    rw [backgroundPotential_cons, Multiset.card_cons]
    push_cast
    ring

/-- For `c > 0` the background density is smooth. -/
theorem contDiff_backgroundDensity (D : Multiset ℂ) (hc : 0 < c) {n : WithTop ℕ∞} :
    ContDiff ℝ n (backgroundDensity D c) := by
  induction D using Multiset.induction_on with
  | empty =>
    rw [backgroundDensity_zero]
    exact contDiff_const
  | cons a D ih =>
    have hfun : backgroundDensity (a ::ₘ D) c =
        fun z ↦ ‖z - a‖ ^ 2 / (‖z - a‖ ^ 2 + c) * backgroundDensity D c z :=
      funext (backgroundDensity_cons a D c)
    have hsq : ContDiff ℝ n fun z : ℂ ↦ ‖z - a‖ ^ 2 :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    rw [hfun]
    exact (hsq.div (hsq.add contDiff_const) fun z ↦ by positivity).mul ih

/-- For `c > 0` the background source is smooth. -/
theorem contDiff_backgroundSource (D : Multiset ℂ) (hc : 0 < c) {n : WithTop ℕ∞} :
    ContDiff ℝ n (backgroundSource D c) := by
  induction D using Multiset.induction_on with
  | empty =>
    rw [backgroundSource_zero]
    exact contDiff_zero_fun
  | cons a D ih =>
    have hfun : backgroundSource (a ::ₘ D) c =
        fun z ↦ 4 * c / (‖z - a‖ ^ 2 + c) ^ 2 + backgroundSource D c z :=
      funext (backgroundSource_cons a D c)
    have hsq : ContDiff ℝ n fun z : ℂ ↦ ‖z - a‖ ^ 2 :=
      (contDiff_norm_sq ℝ).comp (contDiff_id.sub contDiff_const)
    rw [hfun]
    exact (contDiff_const.div ((hsq.add contDiff_const).pow 2) fun z ↦ by positivity).add ih

-- The single-point source profile is a rescaled Japanese bracket with `r = 4`.
private theorem inv_norm_sq_add_sq_eq_rpow (hc : 0 < c) (z : ℂ) :
    ((‖z‖ ^ 2 + c) ^ 2)⁻¹ = (√c ^ 2 + ‖z‖ ^ 2) ^ (-4 / 2 : ℝ) := by
  rw [Real.sq_sqrt hc.le, show (-4 / 2 : ℝ) = -(2 : ℕ) by norm_num,
    Real.rpow_neg (by positivity), Real.rpow_natCast, add_comm]

private theorem integrable_div_norm_sub_sq_add_sq (a : ℂ) (hc : 0 < c) (k : ℝ) :
    Integrable fun z : ℂ ↦ k / (‖z - a‖ ^ 2 + c) ^ 2 := by
  have h : Integrable fun z : ℂ ↦ ((‖z‖ ^ 2 + c) ^ 2)⁻¹ := by
    simpa only [inv_norm_sq_add_sq_eq_rpow hc] using
      TauCeti.integrable_rpow_neg_sq_add_norm_sq volume (c := √c) (r := 4)
        (Real.sqrt_pos.2 hc).ne' (by norm_num [Complex.finrank_real_complex])
  simpa [div_eq_mul_inv] using (h.comp_sub_right a).const_mul k

private theorem integral_inv_norm_sq_add_sq (hc : 0 < c) :
    ∫ z : ℂ, ((‖z‖ ^ 2 + c) ^ 2)⁻¹ = Real.pi / c := by
  simp only [inv_norm_sq_add_sq_eq_rpow hc]
  rw [TauCeti.integral_rpow_neg_sq_add_norm_sq (Real.sqrt_pos.2 hc)
    (by norm_num [Complex.finrank_real_complex]), Complex.finrank_real_complex]
  norm_num [Real.Gamma_two, Real.rpow_neg (Real.sqrt_nonneg c), Real.sq_sqrt hc.le]
  field_simp

/-- The background source is integrable. -/
theorem integrable_backgroundSource (D : Multiset ℂ) (hc : 0 < c) :
    Integrable (backgroundSource D c) := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons a D ih =>
    have hfun : backgroundSource (a ::ₘ D) c =
        fun z ↦ 4 * c / (‖z - a‖ ^ 2 + c) ^ 2 + backgroundSource D c z :=
      funext (backgroundSource_cons a D c)
    rw [hfun]
    exact (integrable_div_norm_sub_sq_add_sq a hc _).add ih

/-- The background source has total integral `4π m`, the total mass of the point charges of a
degree-`m` divisor. -/
theorem integral_backgroundSource (D : Multiset ℂ) (hc : 0 < c) :
    ∫ z, backgroundSource D c z = 4 * Real.pi * D.card := by
  induction D using Multiset.induction_on with
  | empty => simp
  | cons a D ih =>
    have hfun : backgroundSource (a ::ₘ D) c =
        fun z ↦ 4 * c / (‖z - a‖ ^ 2 + c) ^ 2 + backgroundSource D c z :=
      funext (backgroundSource_cons a D c)
    have hone : ∫ z : ℂ, 4 * c / (‖z - a‖ ^ 2 + c) ^ 2 = 4 * Real.pi := by
      simp only [div_eq_mul_inv]
      rw [integral_const_mul,
        integral_sub_right_eq_self (fun z : ℂ ↦ ((‖z‖ ^ 2 + c) ^ 2)⁻¹) a,
        integral_inv_norm_sq_add_sq hc]
      field_simp
    rw [hfun, integral_add (integrable_div_norm_sub_sq_add_sq a hc _)
      (integrable_backgroundSource D hc), hone, ih, Multiset.card_cons]
    push_cast
    ring

/-- The defect `1 - ρ` of the background density is square integrable. -/
theorem memLp_one_sub_backgroundDensity (D : Multiset ℂ) (hc : 0 < c) :
    MemLp (fun z ↦ 1 - backgroundDensity D c z) 2 := by
  have hsum : MemLp (fun z : ℂ ↦ (D.map fun a ↦ c / (‖z - a‖ ^ 2 + c)).sum) 2 := by
    induction D using Multiset.induction_on with
    | empty => simp
    | cons a D ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons]
      refine MemLp.add ?_ ih
      refine (memLp_two_iff_integrable_sq
        (continuous_const.div (by fun_prop) fun z ↦ by positivity).aestronglyMeasurable).2 ?_
      simpa [div_pow] using integrable_div_norm_sub_sq_add_sq a hc (c ^ 2)
  have hmeas : Continuous fun z ↦ 1 - backgroundDensity D c z :=
    continuous_const.sub (contDiff_backgroundDensity D hc (n := 0)).continuous
  refine hsum.mono hmeas.aestronglyMeasurable (Eventually.of_forall fun z ↦ ?_)
  have hle := one_sub_backgroundDensity_le D hc z
  have h₀ : 0 ≤ 1 - backgroundDensity D c z := sub_nonneg.2 (backgroundDensity_le_one D hc.le z)
  rw [Real.norm_of_nonneg h₀, Real.norm_of_nonneg (h₀.trans hle)]
  exact one_sub_backgroundDensity_le D hc z

/-- **The regular scalar equation.** At a point where `w` is `C²`, the function `u = b + w / 2`
solves the vortex scalar equation `Δu = (exp (2u) |P_D|² - 1) / 8` exactly when `w` solves
`Δw = (ρ exp w - 1) / 4 + g`. -/
theorem laplacian_backgroundPotential_add_eq_iff (D : Multiset ℂ) (hc : 0 < c) {w : ℂ → ℝ}
    {z : ℂ} (hw : ContDiffAt ℝ 2 w z) :
    Δ (fun z ↦ backgroundPotential D c z + w z / 2) z =
        (Real.exp (2 * (backgroundPotential D c z + w z / 2)) *
          ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2 - 1) / 8 ↔
      Δ w z = (backgroundDensity D c z * Real.exp (w z) - 1) / 4 + backgroundSource D c z := by
  have hfun : (fun z ↦ backgroundPotential D c z + w z / 2) =
      backgroundPotential D c + ((1 / 2 : ℝ) • w) := by
    funext z
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hΔ : Δ (fun z ↦ backgroundPotential D c z + w z / 2) z =
      -backgroundSource D c z / 2 + Δ w z / 2 := by
    have hw' : ContDiffAt ℝ 2 ((1 / 2 : ℝ) • w) z := contDiffAt_const.smul hw
    rw [hfun, ContDiffAt.laplacian_add (contDiff_backgroundPotential D hc).contDiffAt hw',
      laplacian_smul _ hw, laplacian_backgroundPotential D hc, smul_eq_mul]
    ring
  have hexp : Real.exp (2 * (backgroundPotential D c z + w z / 2)) *
      ‖((D.map fun a ↦ X - C a).prod).eval z‖ ^ 2 =
        backgroundDensity D c z * Real.exp (w z) := by
    rw [← exp_two_mul_backgroundPotential_mul_norm_eval_sq D hc z,
      show 2 * (backgroundPotential D c z + w z / 2) = 2 * backgroundPotential D c z + w z by
        ring, Real.exp_add]
    ring
  rw [hΔ, hexp]
  constructor <;> intro h <;> linarith

/-- The degree-`m` logarithmic boundary condition `u(z) + m log |z| → 0` for `u = b + w / 2` is
exactly the decay `w → 0` at infinity. -/
theorem tendsto_backgroundPotential_add_add_mul_log_iff (D : Multiset ℂ) (hc : 0 < c)
    (w : ℂ → ℝ) :
    Tendsto (fun z ↦ backgroundPotential D c z + w z / 2 + D.card * Real.log ‖z‖)
        (cocompact ℂ) (𝓝 0) ↔
      Tendsto w (cocompact ℂ) (𝓝 0) := by
  have hb := tendsto_backgroundPotential_add_mul_log D hc
  constructor
  · intro h
    have h' := (h.sub hb).const_mul 2
    rw [sub_zero, mul_zero] at h'
    refine h'.congr fun z ↦ ?_
    ring
  · intro h
    have h' := hb.add (h.div_const 2)
    rw [zero_div, add_zero] at h'
    refine h'.congr fun z ↦ ?_
    ring

/-- For a `C²` function `w`, the field reconstructed from `u = b + w / 2` and the divisor
polynomial `P_D` solves the plane vortex equation everywhere exactly when `w` solves the regular
scalar equation everywhere. -/
theorem equation_amplitudeField_backgroundPotential_eq_zero_iff (D : Multiset ℂ) (hc : 0 < c)
    {w : ℂ → ℝ} (hw : ContDiff ℝ 2 w) :
    equation (amplitudeField (fun z ↦ backgroundPotential D c z + w z / 2)
        ((D.map fun a ↦ X - C a).prod).eval) = 0 ↔
      ∀ z, Δ w z = (backgroundDensity D c z * Real.exp (w z) - 1) / 4 +
        backgroundSource D c z := by
  rw [funext_iff]
  refine forall_congr' fun z ↦ ?_
  rw [Pi.zero_apply, equation_amplitudeField_eq_zero_iff
    ((contDiff_backgroundPotential D hc).add (hw.div_const 2)).contDiffAt
    ((Polynomial.differentiable _).differentiableAt),
    laplacian_backgroundPotential_add_eq_iff D hc hw.contDiffAt]

/-- The field reconstructed from `u = b + w / 2` and `P_D` has the degree-`m` end framing
`α(z) (z / |z|)⁻ᵐ → 1` exactly when `w → 0` at infinity. -/
theorem tendsto_sectionValue_amplitudeField_backgroundPotential_iff (D : Multiset ℂ)
    (hc : 0 < c) (w : ℂ → ℝ) :
    Tendsto (fun z ↦ sectionValue (amplitudeField (fun z ↦ backgroundPotential D c z + w z / 2)
        ((D.map fun a ↦ X - C a).prod).eval) z * ((z / (‖z‖ : ℂ)) ^ D.card)⁻¹)
        (cocompact ℂ) (𝓝 1) ↔
      Tendsto w (cocompact ℂ) (𝓝 0) := by
  have hmonic : ((D.map fun a ↦ X - C a).prod).Monic :=
    monic_multiset_prod_of_monic _ _ fun a _ ↦ monic_X_sub_C a
  have h := tendsto_sectionValue_amplitudeField_mul_inv_phase_iff_log hmonic
    (fun z ↦ backgroundPotential D c z + w z / 2)
  rw [natDegree_multiset_prod_X_sub_C_eq_card] at h
  rw [h, tendsto_backgroundPotential_add_add_mul_log_iff D hc]

/-- The section reconstructed from `P_D` vanishes at each point `a` to the order `count a D`:
it is `(z - a) ^ (count a D)` times a function nonvanishing at `a` and as regular as the
amplitude `u`. -/
theorem exists_sectionValue_amplitudeField_eq_pow_count_mul (D : Multiset ℂ) {u : ℂ → ℝ}
    {n : WithTop ℕ∞} (hu : ContDiff ℝ n u) (a : ℂ) :
    ∃ g : ℂ → ℂ, ContDiff ℝ n g ∧ g a ≠ 0 ∧ ∀ z,
      sectionValue (amplitudeField u ((D.map fun a ↦ X - C a).prod).eval) z =
        (z - a) ^ D.count a * g z := by
  classical
  set Q := ((D.filter (· ≠ a)).map fun b ↦ X - C b).prod
  have hsplit : (D.map fun b ↦ X - C b).prod = (X - C a) ^ D.count a * Q := by
    conv_lhs => rw [← Multiset.filter_add_not (· = a) D]
    rw [Multiset.map_add, Multiset.prod_add, Multiset.filter_eq', Multiset.map_replicate,
      Multiset.prod_replicate]
  have hQ : Q.eval a ≠ 0 := by
    simp only [Q, eval_multiset_prod, Multiset.map_map, Function.comp_def, eval_sub, eval_X,
      eval_C]
    refine Multiset.prod_ne_zero fun h ↦ ?_
    obtain ⟨b, hb, hab⟩ := Multiset.mem_map.1 h
    exact (Multiset.of_mem_filter hb) (sub_eq_zero.1 hab).symm
  have hQd : ContDiff ℝ n fun z ↦ Q.eval z :=
    (Q.differentiable.contDiff (n := n)).restrict_scalars ℝ
  refine ⟨fun z ↦ (Real.exp (u z) : ℂ) * Q.eval z,
    (Complex.ofRealCLM.contDiff.comp hu.exp).mul hQd,
    mul_ne_zero (by simp) hQ, fun z ↦ ?_⟩
  rw [sectionValue_amplitudeField, hsplit, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  ring

end TauCeti.Vortex
