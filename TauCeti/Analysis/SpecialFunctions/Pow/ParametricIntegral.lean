/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Complex.Arg
import TauCeti.Analysis.SpecialFunctions.Pow.Complex
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Parametric differentiation and holomorphy of slit-plane power integrals

For a complex parameter `z` in `Complex.slitPlane` and any complex exponent `s`, the principal
power `((t : ℂ) + w) ^ s` along the nonnegative real half-line `t ≥ 0` has norm bounded above by
`C * (1 + t) ^ s.re` (with `C > 0`) locally uniformly for `w` near `z`
(`TauCeti.exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow`), and `‖((t : ℂ) + z) ^ s‖` is
bounded below by `c * (1 + t) ^ s.re` (with `c > 0`) pointwise at each `z ∈ slitPlane`
(`TauCeti.exists_pos_mul_one_add_rpow_le_norm_ofReal_add_cpow`).

Consequently, for any measure `μ` on `ℝ` and weight `g : ℝ → ℂ`, integrability of
`t ↦ g t * ((t : ℂ) + z) ^ s` on `(0, ∞)` is independent of `z ∈ slitPlane`, is equivalent to
almost-everywhere strong measurability of `g` with respect to `μ.restrict (Ioi 0)` together with
integrability of `t ↦ ‖g t‖ * (1 + t) ^ s.re`, and is preserved when `s.re` decreases.
Differentiating under the integral sign then shows that

`w ↦ ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + w) ^ s ∂μ`

is holomorphic on `slitPlane` with derivative
`s * ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + z) ^ (s - 1) ∂μ`. These theorems drive the slit-plane
holomorphy and partial-derivative formulas for Carlson's symmetric elliptic integrals `R_C`, `R_J`,
`R_D`, and `R_G`.

In the dual Mellin–Barnes setting, the base `w` is raised to a vertical-line exponent `σ + i y`
with `y ∈ ℝ`, where `‖w ^ (σ + i y)‖ ≤ ‖w‖ ^ σ * exp (|arg w| * |y|)`. Whenever a measurable weight
`g : ℝ → ℂ` decays faster than `exp (-|arg z| * |y|)`, the vertical integral
`∫ y : ℝ, g y * z ^ (σ + i y)` converges, and at `z ∈ slitPlane` it may be differentiated under the
integral sign. When `g` satisfies `‖g y‖ ≤ C * exp (-c * |y|)` for every `c < π`, this makes
`w ↦ ∫ y : ℝ, g y * w ^ (σ + i y)` holomorphic on the entire `slitPlane`.

## Main results

* `TauCeti.integrableOn_norm_mul_one_add_rpow_of_le` — monotonicity of integrability of
  `t ↦ ‖g t‖ * (1 + t) ^ r` on `(0, ∞)` in the real exponent `r`.
* `TauCeti.integrableOn_mul_ofReal_add_cpow_iff_norm_mul_one_add_rpow` — exact characterization of
  integrability of `t ↦ g t * ((t : ℂ) + z) ^ s` on `(0, ∞)` for `z ∈ slitPlane`.
* `TauCeti.integrableOn_mul_ofReal_add_cpow_iff`,
  `TauCeti.integrableOn_mul_ofReal_add_cpow_of_re_le` — independence of `z ∈ slitPlane` and
  monotonicity in `s.re`.
* `TauCeti.hasDerivAt_integral_mul_ofReal_add_cpow` — differentiation under the integral sign for
  `w ↦ ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + w) ^ s ∂μ` on `slitPlane`.
* `TauCeti.differentiableOn_integral_mul_ofReal_add_cpow`,
  `TauCeti.analyticOnNhd_integral_mul_ofReal_add_cpow` — complex differentiability and holomorphy
  on `slitPlane`.
* `TauCeti.norm_cpow_add_mul_I_le`, `TauCeti.aestronglyMeasurable_cpow_add_mul_I` — norm bound and
  measurability of `y ↦ z ^ (σ + i y)` for an arbitrary complex base `z`.
* `TauCeti.integrable_mul_cpow_add_mul_I_of_norm_le_exp`,
  `TauCeti.hasDerivAt_integral_mul_cpow_add_mul_I_of_norm_le_exp` — integrability and
  differentiation under the integral sign for `w ↦ ∫ y : ℝ, g y * w ^ (σ + i y)` under exponential
  decay of `g`.
* `TauCeti.differentiableOn_integral_mul_cpow_add_mul_I`,
  `TauCeti.analyticOnNhd_integral_mul_cpow_add_mul_I` — slit-plane differentiability and holomorphy
  when `g y = O(exp (-c |y|))` for every `c < π`.
-/

public section

open MeasureTheory Set Filter Complex Topology

namespace TauCeti

/-- Decreasing the real exponent `r` preserves integrability of `t ↦ ‖g t‖ * (1 + t) ^ r` on
`(0, ∞)`, since `1 ≤ 1 + t` there. -/
theorem integrableOn_norm_mul_one_add_rpow_of_le {E : Type*} [SeminormedAddCommGroup E]
    {μ : Measure ℝ} {g : ℝ → E} {r₁ r₂ : ℝ} (hr : r₁ ≤ r₂)
    (hg : IntegrableOn (fun t : ℝ => ‖g t‖ * (1 + t) ^ r₂) (Ioi 0) μ) :
    IntegrableOn (fun t : ℝ => ‖g t‖ * (1 + t) ^ r₁) (Ioi 0) μ := by
  have hrpow_cont : ContinuousOn (fun t : ℝ => (1 + t) ^ (r₁ - r₂)) (Ioi 0) :=
    (by fun_prop : Continuous fun t : ℝ => 1 + t).continuousOn.rpow_const
      fun t ht => Or.inl (by have : (0 : ℝ) < t := ht; linarith)
  have hmeas : AEStronglyMeasurable (fun t : ℝ => ‖g t‖ * (1 + t) ^ r₁) (μ.restrict (Ioi 0)) := by
    refine (hg.aestronglyMeasurable.mul
      (hrpow_cont.aestronglyMeasurable measurableSet_Ioi)).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have h1t : 0 < 1 + t := by have : (0 : ℝ) < t := ht; linarith
    rw [Pi.mul_apply, mul_assoc, ← Real.rpow_add h1t, add_sub_cancel]
  refine hg.mono' hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have h1t : 1 ≤ 1 + t := by have : (0 : ℝ) < t := ht; linarith
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity))]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1t hr) (norm_nonneg _)

/-- For `z ∈ slitPlane` and any `s : ℂ`, `t ↦ g t * ((t : ℂ) + z) ^ s` is integrable on `(0, ∞)`
with respect to `μ` if and only if `g` is almost-everywhere strongly measurable with respect to
`μ.restrict (Ioi 0)` and `t ↦ ‖g t‖ * (1 + t) ^ s.re` is integrable on `(0, ∞)` with respect to
`μ`. -/
theorem integrableOn_mul_ofReal_add_cpow_iff_norm_mul_one_add_rpow {μ : Measure ℝ}
    {g : ℝ → ℂ} {z : ℂ} (hz : z ∈ slitPlane) (s : ℂ) :
    IntegrableOn (fun t : ℝ => g t * ((t : ℂ) + z) ^ s) (Ioi 0) μ ↔
      AEStronglyMeasurable g (μ.restrict (Ioi 0)) ∧
        IntegrableOn (fun t : ℝ => ‖g t‖ * (1 + t) ^ s.re) (Ioi 0) μ := by
  constructor
  · intro hg
    have hinv_cont : ContinuousOn (fun t : ℝ => ((t : ℂ) + z) ^ (-s)) (Ioi 0) :=
      continuousOn_ofReal_add_cpow (Or.inl hz) (-s)
    have hg_meas : AEStronglyMeasurable g (μ.restrict (Ioi 0)) := by
      refine (hg.aestronglyMeasurable.mul
        (hinv_cont.aestronglyMeasurable measurableSet_Ioi)).congr ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hne : ((t : ℂ) + z) ^ s ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero
          (slitPlane_ne_zero (ofReal_add_mem_slitPlane hz (le_of_lt ht)))]
        exact Complex.exp_ne_zero _
      rw [Pi.mul_apply, Complex.cpow_neg, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    obtain ⟨c, hc, hlow⟩ := exists_pos_mul_one_add_rpow_le_norm_ofReal_add_cpow hz s
    have hrpow_cont : ContinuousOn (fun t : ℝ => (1 + t) ^ s.re) (Ioi 0) :=
      (by fun_prop : Continuous fun t : ℝ => 1 + t).continuousOn.rpow_const
        fun t ht => Or.inl (by have : (0 : ℝ) < t := ht; linarith)
    refine ⟨hg_meas, (hg.norm.const_mul c⁻¹).mono'
      (hg_meas.norm.mul (hrpow_cont.aestronglyMeasurable measurableSet_Ioi)) ?_⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (by positivity)), norm_mul]
    calc ‖g t‖ * (1 + t) ^ s.re
        = c⁻¹ * (‖g t‖ * (c * (1 + t) ^ s.re)) := by field_simp
      _ ≤ c⁻¹ * (‖g t‖ * ‖((t : ℂ) + z) ^ s‖) := by
          gcongr
          exact hlow t ht0
  · rintro ⟨hg_meas, hg_int⟩
    obtain ⟨U, hU, _, C, _, hbound⟩ :=
      exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow hz s
    have hzU : z ∈ U := mem_of_mem_nhds hU
    have hcpow_cont : ContinuousOn (fun t : ℝ => ((t : ℂ) + z) ^ s) (Ioi 0) :=
      continuousOn_ofReal_add_cpow (Or.inl hz) s
    refine (hg_int.const_mul C).mono'
      (hg_meas.mul (hcpow_cont.aestronglyMeasurable measurableSet_Ioi)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_mul]
    calc ‖g t‖ * ‖((t : ℂ) + z) ^ s‖
        ≤ ‖g t‖ * (C * (1 + t) ^ s.re) :=
          mul_le_mul_of_nonneg_left (hbound z hzU t (le_of_lt ht)) (norm_nonneg _)
      _ = C * (‖g t‖ * (1 + t) ^ s.re) := by ring

/-- Integrability of `t ↦ g t * ((t : ℂ) + z) ^ s` on `(0, ∞)` is preserved when moving between
points of `slitPlane` and nonincreasing `s.re`. -/
theorem integrableOn_mul_ofReal_add_cpow_of_re_le {μ : Measure ℝ} {g : ℝ → ℂ} {z₁ z₂ s₁ s₂ : ℂ}
    (hz₁ : z₁ ∈ slitPlane) (hz₂ : z₂ ∈ slitPlane) (hs : s₂.re ≤ s₁.re)
    (hg : IntegrableOn (fun t : ℝ => g t * ((t : ℂ) + z₁) ^ s₁) (Ioi 0) μ) :
    IntegrableOn (fun t : ℝ => g t * ((t : ℂ) + z₂) ^ s₂) (Ioi 0) μ := by
  rw [integrableOn_mul_ofReal_add_cpow_iff_norm_mul_one_add_rpow hz₁ s₁] at hg
  rw [integrableOn_mul_ofReal_add_cpow_iff_norm_mul_one_add_rpow hz₂ s₂]
  exact ⟨hg.1, integrableOn_norm_mul_one_add_rpow_of_le hs hg.2⟩

/-- Integrability of `t ↦ g t * ((t : ℂ) + z) ^ s` on `(0, ∞)` does not depend on the point
`z ∈ slitPlane`. -/
theorem integrableOn_mul_ofReal_add_cpow_iff {μ : Measure ℝ} {g : ℝ → ℂ} {z₁ z₂ : ℂ}
    (hz₁ : z₁ ∈ slitPlane) (hz₂ : z₂ ∈ slitPlane) (s : ℂ) :
    IntegrableOn (fun t : ℝ => g t * ((t : ℂ) + z₁) ^ s) (Ioi 0) μ ↔
      IntegrableOn (fun t : ℝ => g t * ((t : ℂ) + z₂) ^ s) (Ioi 0) μ :=
  ⟨integrableOn_mul_ofReal_add_cpow_of_re_le hz₁ hz₂ le_rfl,
    integrableOn_mul_ofReal_add_cpow_of_re_le hz₂ hz₁ le_rfl⟩

/-- **Differentiation under a slit-plane power integral.** If `z ∈ slitPlane` and
`t ↦ g t * ((t : ℂ) + z) ^ s` is integrable on `(0, ∞)`, then
`w ↦ ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + w) ^ s ∂μ` has derivative
`s * ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + z) ^ (s - 1) ∂μ` at `z`. -/
theorem hasDerivAt_integral_mul_ofReal_add_cpow {μ : Measure ℝ} {g : ℝ → ℂ} {z : ℂ}
    (hz : z ∈ slitPlane) {s : ℂ}
    (hg : IntegrableOn (fun t : ℝ => g t * ((t : ℂ) + z) ^ s) (Ioi 0) μ) :
    HasDerivAt (fun w : ℂ => ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + w) ^ s ∂μ)
      (s * ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + z) ^ (s - 1) ∂μ) z := by
  obtain ⟨hg_meas, hg_norm⟩ :=
    (integrableOn_mul_ofReal_add_cpow_iff_norm_mul_one_add_rpow hz s).mp hg
  obtain ⟨U, hU, hU_slit, C, _, hC⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow hz (s - 1)
  have hs1 : (s - 1).re ≤ s.re := by simp
  have hbound_int : IntegrableOn (fun t : ℝ => ‖s‖ * C * (‖g t‖ * (1 + t) ^ (s - 1).re))
      (Ioi 0) μ :=
    (integrableOn_norm_mul_one_add_rpow_of_le hs1 hg_norm).const_mul (‖s‖ * C)
  have hF_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun t : ℝ => g t * ((t : ℂ) + w) ^ s) (μ.restrict (Ioi 0)) := by
    filter_upwards [hU] with w hw
    exact hg_meas.mul ((continuousOn_ofReal_add_cpow (Or.inl (hU_slit hw)) s).aestronglyMeasurable
      measurableSet_Ioi)
  have hF'_meas : AEStronglyMeasurable
      (fun t : ℝ => g t * (s * ((t : ℂ) + z) ^ (s - 1))) (μ.restrict (Ioi 0)) :=
    hg_meas.mul (((continuousOn_ofReal_add_cpow (Or.inl hz) (s - 1)).const_smul
      s).aestronglyMeasurable measurableSet_Ioi)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ.restrict (Ioi 0))
    (F := fun (w : ℂ) (t : ℝ) => g t * ((t : ℂ) + w) ^ s)
    (F' := fun (w : ℂ) (t : ℝ) => g t * (s * ((t : ℂ) + w) ^ (s - 1)))
    (bound := fun t : ℝ => ‖s‖ * C * (‖g t‖ * (1 + t) ^ (s - 1).re))
    hU hF_meas hg hF'_meas ?_ hbound_int ?_
  · refine key.2.congr_deriv ?_
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    rw [norm_mul, norm_mul]
    calc ‖g t‖ * (‖s‖ * ‖((t : ℂ) + w) ^ (s - 1)‖)
        ≤ ‖g t‖ * (‖s‖ * (C * (1 + t) ^ (s - 1).re)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (hC w hw t (le_of_lt ht)) (norm_nonneg s)) (norm_nonneg _)
      _ = ‖s‖ * C * (‖g t‖ * (1 + t) ^ (s - 1).re) := by ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have hw_mem : (t : ℂ) + w ∈ slitPlane :=
      ofReal_add_mem_slitPlane (hU_slit hw) (le_of_lt ht)
    have hd := (((hasDerivAt_id w).const_add (t : ℂ)).cpow_const (c := s) hw_mem).const_mul (g t)
    exact hd.congr_deriv (by simp only [id, mul_one])

/-- If `t ↦ g t * ((t : ℂ) + z₀) ^ s` is integrable on `(0, ∞)` at some `z₀ ∈ slitPlane`, then
`w ↦ ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + w) ^ s ∂μ` is complex differentiable on `slitPlane`. -/
theorem differentiableOn_integral_mul_ofReal_add_cpow {μ : Measure ℝ} {g : ℝ → ℂ} {z₀ s : ℂ}
    (hz₀ : z₀ ∈ slitPlane)
    (hg : IntegrableOn (fun t : ℝ => g t * ((t : ℂ) + z₀) ^ s) (Ioi 0) μ) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + w) ^ s ∂μ) slitPlane :=
  fun _ hz => (hasDerivAt_integral_mul_ofReal_add_cpow hz
    ((integrableOn_mul_ofReal_add_cpow_iff hz₀ hz s).mp hg)).differentiableAt.differentiableWithinAt

/-- If `t ↦ g t * ((t : ℂ) + z₀) ^ s` is integrable on `(0, ∞)` at some `z₀ ∈ slitPlane`, then
`w ↦ ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + w) ^ s ∂μ` is holomorphic on `slitPlane`. -/
theorem analyticOnNhd_integral_mul_ofReal_add_cpow {μ : Measure ℝ} {g : ℝ → ℂ} {z₀ s : ℂ}
    (hz₀ : z₀ ∈ slitPlane)
    (hg : IntegrableOn (fun t : ℝ => g t * ((t : ℂ) + z₀) ^ s) (Ioi 0) μ) :
    AnalyticOnNhd ℂ (fun w : ℂ => ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + w) ^ s ∂μ) slitPlane :=
  (differentiableOn_integral_mul_ofReal_add_cpow hz₀ hg).analyticOnNhd isOpen_slitPlane

/-- For any complex base `z` and vertical-line exponent `σ + i y`, the principal power
`z ^ (σ + i y)` has norm at most `‖z‖ ^ σ * exp (|arg z| * |y|)`. -/
theorem norm_cpow_add_mul_I_le (z : ℂ) (σ y : ℝ) :
    ‖z ^ ((σ : ℂ) + y * I)‖ ≤ ‖z‖ ^ σ * Real.exp (|z.arg| * |y|) := by
  have hre : ((σ : ℂ) + y * I).re = σ := by simp
  have him : ((σ : ℂ) + y * I).im = y := by simp
  calc ‖z ^ ((σ : ℂ) + y * I)‖
      ≤ ‖z‖ ^ ((σ : ℂ) + y * I).re / Real.exp (z.arg * ((σ : ℂ) + y * I).im) :=
        Complex.norm_cpow_le _ _
    _ = ‖z‖ ^ σ * Real.exp (-(z.arg * y)) := by
        rw [hre, him, div_eq_mul_inv, ← Real.exp_neg]
    _ ≤ ‖z‖ ^ σ * Real.exp (|z.arg| * |y|) := by
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
          (Real.rpow_nonneg (norm_nonneg z) σ)
        exact (neg_le_abs _).trans (abs_mul z.arg y).le

/-- For any complex base `z` and real `σ`, `y ↦ z ^ (σ + i y)` is almost-everywhere strongly
measurable with respect to Lebesgue measure on `ℝ` (vanishing off `y = 0` when `z = 0`). -/
theorem aestronglyMeasurable_cpow_add_mul_I (z : ℂ) (σ : ℝ) :
    AEStronglyMeasurable (fun y : ℝ => z ^ ((σ : ℂ) + y * I)) volume := by
  rcases eq_or_ne z 0 with rfl | hz
  · refine (aestronglyMeasurable_const (b := (0 : ℂ))).congr ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with y hy
    have hne : (σ : ℂ) + y * I ≠ 0 := fun h => hy (by simpa using congrArg Complex.im h)
    exact (Complex.zero_cpow hne).symm
  · have heq : (fun y : ℝ => z ^ ((σ : ℂ) + y * I)) =
        fun y : ℝ => Complex.exp (Complex.log z * ((σ : ℂ) + y * I)) :=
      funext fun y => Complex.cpow_def_of_ne_zero hz _
    rw [heq]
    exact Continuous.aestronglyMeasurable (by fun_prop)

/-- If `g : ℝ → ℂ` is almost-everywhere strongly measurable and satisfies
`‖g y‖ ≤ C * exp (-c * |y|)` for an exponent `c > |arg z|`, then `y ↦ g y * z ^ (σ + i y)` is
integrable on `ℝ`. This applies to any complex base `z` (including `0` and the negative real axis
when `π < c`). -/
theorem integrable_mul_cpow_add_mul_I_of_norm_le_exp {g : ℝ → ℂ}
    (hg_meas : AEStronglyMeasurable g volume) {z : ℂ} {σ c C : ℝ}
    (hc : |z.arg| < c) (hg : ∀ y : ℝ, ‖g y‖ ≤ C * Real.exp (-c * |y|)) :
    Integrable (fun y : ℝ => g y * z ^ ((σ : ℂ) + y * I)) := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hg 0)
  have hrate : 0 < c - |z.arg| := sub_pos.mpr hc
  refine ((integrable_exp_neg_mul_abs hrate).const_mul (C * ‖z‖ ^ σ)).mono'
    (hg_meas.mul (aestronglyMeasurable_cpow_add_mul_I z σ)) (Eventually.of_forall fun y => ?_)
  rw [norm_mul]
  calc ‖g y‖ * ‖z ^ ((σ : ℂ) + y * I)‖
      ≤ (C * Real.exp (-c * |y|)) * (‖z‖ ^ σ * Real.exp (|z.arg| * |y|)) :=
        mul_le_mul (hg y) (norm_cpow_add_mul_I_le z σ y) (norm_nonneg _) (by positivity)
    _ = C * ‖z‖ ^ σ * Real.exp (-((c - |z.arg|) * |y|)) := by
        rw [mul_mul_mul_comm, ← Real.exp_add]
        congr 2
        ring

/-- **Differentiation under a vertical-line power integral.** If `z ∈ slitPlane`, `g` is
almost-everywhere strongly measurable, and `‖g y‖ ≤ C * exp (-c * |y|)` for some `c > |arg z|`,
then `w ↦ ∫ y : ℝ, g y * w ^ (σ + i y)` has complex derivative
`∫ y : ℝ, g y * ((σ + i y) * z ^ (σ + i y - 1))` at `z`. -/
theorem hasDerivAt_integral_mul_cpow_add_mul_I_of_norm_le_exp {g : ℝ → ℂ}
    (hg_meas : AEStronglyMeasurable g volume) {z : ℂ} (hz : z ∈ slitPlane)
    {σ c C : ℝ} (hc : |z.arg| < c) (hg : ∀ y : ℝ, ‖g y‖ ≤ C * Real.exp (-c * |y|)) :
    HasDerivAt (fun w : ℂ => ∫ y : ℝ, g y * w ^ ((σ : ℂ) + y * I))
      (∫ y : ℝ, g y * (((σ : ℂ) + y * I) * z ^ ((σ : ℂ) + y * I - 1))) z := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg (g 0)).trans (hg 0)
  have hz_norm : 0 < ‖z‖ := norm_pos_iff.mpr (slitPlane_ne_zero hz)
  set θ : ℝ := (|z.arg| + c) / 2
  set ε : ℝ := (c - θ) / 2
  have hε : 0 < ε := by dsimp [ε, θ]; linarith
  set M : ℝ := max ((‖z‖ / 2) ^ (σ - 1)) ((2 * ‖z‖) ^ (σ - 1))
  have hM : 0 < M := lt_of_lt_of_le (Real.rpow_pos_of_pos (half_pos hz_norm) _) (le_max_left _ _)
  set U : Set ℂ :=
    slitPlane ∩ {w : ℂ | |w.arg| < θ} ∩ {w : ℂ | ‖z‖ / 2 < ‖w‖ ∧ ‖w‖ < 2 * ‖z‖}
  have hU : U ∈ 𝓝 z := by
    refine Filter.inter_mem (Filter.inter_mem (isOpen_slitPlane.mem_nhds hz) ?_) ?_
    · exact (continuous_abs.continuousAt.comp (Complex.continuousAt_arg hz)).preimage_mem_nhds
        (Iio_mem_nhds (by dsimp [θ]; linarith))
    · exact continuous_norm.continuousAt.preimage_mem_nhds
        (Ioo_mem_nhds (by linarith) (by linarith))
  have hsub (y : ℝ) : (σ : ℂ) + y * I - 1 = ((σ - 1 : ℝ) : ℂ) + y * I := by
    push_cast; ring
  have hF_meas : ∀ᶠ w in 𝓝 z,
      AEStronglyMeasurable (fun y : ℝ => g y * w ^ ((σ : ℂ) + y * I)) volume :=
    Eventually.of_forall fun w => hg_meas.mul (aestronglyMeasurable_cpow_add_mul_I w σ)
  have hF'_meas : AEStronglyMeasurable
      (fun y : ℝ => g y * (((σ : ℂ) + y * I) * z ^ ((σ : ℂ) + y * I - 1))) volume := by
    simp_rw [hsub]
    exact hg_meas.mul
      (((by fun_prop : Continuous fun y : ℝ => (σ : ℂ) + y * I).aestronglyMeasurable).mul
        (aestronglyMeasurable_cpow_add_mul_I z (σ - 1)))
  have hbound_int :
      Integrable (fun y : ℝ => C * (|σ| + ε⁻¹) * M * Real.exp (-(ε * |y|))) :=
    (integrable_exp_neg_mul_abs hε).const_mul (C * (|σ| + ε⁻¹) * M)
  have hlin (y : ℝ) : ‖(σ : ℂ) + y * I‖ ≤ (|σ| + ε⁻¹) * Real.exp (ε * |y|) := by
    have hnorm : ‖(σ : ℂ) + y * I‖ ≤ |σ| + |y| := by
      simpa using Complex.norm_le_abs_re_add_abs_im ((σ : ℂ) + y * I)
    have hexpy : |y| ≤ ε⁻¹ * Real.exp (ε * |y|) := by
      have h1 : ε * |y| ≤ Real.exp (ε * |y|) := by linarith [Real.add_one_le_exp (ε * |y|)]
      calc |y| = ε⁻¹ * (ε * |y|) := by field_simp
        _ ≤ ε⁻¹ * Real.exp (ε * |y|) := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hε.le)
    have hσexp : |σ| ≤ |σ| * Real.exp (ε * |y|) :=
      le_mul_of_one_le_right (abs_nonneg σ) (Real.one_le_exp (by positivity))
    linarith
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun (w : ℂ) (y : ℝ) => g y * w ^ ((σ : ℂ) + y * I))
    (F' := fun (w : ℂ) (y : ℝ) => g y * (((σ : ℂ) + y * I) * w ^ ((σ : ℂ) + y * I - 1)))
    (bound := fun y : ℝ => C * (|σ| + ε⁻¹) * M * Real.exp (-(ε * |y|)))
    hU hF_meas (integrable_mul_cpow_add_mul_I_of_norm_le_exp hg_meas hc hg) hF'_meas
    (Eventually.of_forall fun y w hw => by
      have hrpow : ‖w‖ ^ (σ - 1) ≤ M := by
        rcases le_or_gt (σ - 1) 0 with hσ | hσ
        · exact (Real.rpow_le_rpow_of_nonpos (half_pos hz_norm) hw.2.1.le hσ).trans
            (le_max_left _ _)
        · exact (Real.rpow_le_rpow (norm_nonneg w) hw.2.2.le hσ.le).trans (le_max_right _ _)
      have hw_pow : ‖w ^ ((σ : ℂ) + y * I - 1)‖ ≤ M * Real.exp (θ * |y|) := by
        rw [hsub]
        refine (norm_cpow_add_mul_I_le w (σ - 1) y).trans ?_
        exact mul_le_mul hrpow
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hw.1.2.le (abs_nonneg y)))
          (Real.exp_pos _).le hM.le
      rw [norm_mul, norm_mul]
      calc ‖g y‖ * (‖(σ : ℂ) + y * I‖ * ‖w ^ ((σ : ℂ) + y * I - 1)‖)
          ≤ (C * Real.exp (-c * |y|)) *
              (((|σ| + ε⁻¹) * Real.exp (ε * |y|)) * (M * Real.exp (θ * |y|))) :=
            mul_le_mul (hg y)
              (mul_le_mul (hlin y) hw_pow (norm_nonneg _) (by positivity))
              (by positivity) (by positivity)
        _ = C * (|σ| + ε⁻¹) * M * Real.exp (-(ε * |y|)) := by
            have hexp_sum : -c * |y| + (ε * |y| + θ * |y|) = -(ε * |y|) := by
              dsimp [ε, θ]; ring
            rw [← hexp_sum, Real.exp_add, Real.exp_add]
            ring)
    hbound_int
    (Eventually.of_forall fun y w hw =>
      (((hasDerivAt_id w).cpow_const hw.1.1).const_mul (g y)).congr_deriv (by simp))).2

/-- If `g` is almost-everywhere strongly measurable and satisfies `‖g y‖ ≤ C * exp (-c * |y|)` for
every `c < π`, then `w ↦ ∫ y : ℝ, g y * w ^ (σ + i y)` is complex differentiable on `slitPlane`. -/
theorem differentiableOn_integral_mul_cpow_add_mul_I {g : ℝ → ℂ}
    (hg_meas : AEStronglyMeasurable g volume) (σ : ℝ)
    (hg : ∀ c < Real.pi, ∃ C : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * Real.exp (-c * |y|)) :
    DifferentiableOn ℂ (fun w : ℂ => ∫ y : ℝ, g y * w ^ ((σ : ℂ) + y * I)) slitPlane := by
  intro z hz
  have harg : |z.arg| < Real.pi := Complex.abs_arg_lt_pi_of_mem_slitPlane hz
  obtain ⟨C, hC⟩ := hg ((|z.arg| + Real.pi) / 2) (by linarith)
  exact (hasDerivAt_integral_mul_cpow_add_mul_I_of_norm_le_exp hg_meas hz (by linarith)
    hC).differentiableAt.differentiableWithinAt

/-- If `g` is almost-everywhere strongly measurable and satisfies `‖g y‖ ≤ C * exp (-c * |y|)` for
every `c < π`, then `w ↦ ∫ y : ℝ, g y * w ^ (σ + i y)` is holomorphic on `slitPlane`. -/
theorem analyticOnNhd_integral_mul_cpow_add_mul_I {g : ℝ → ℂ}
    (hg_meas : AEStronglyMeasurable g volume) (σ : ℝ)
    (hg : ∀ c < Real.pi, ∃ C : ℝ, ∀ y : ℝ, ‖g y‖ ≤ C * Real.exp (-c * |y|)) :
    AnalyticOnNhd ℂ (fun w : ℂ => ∫ y : ℝ, g y * w ^ ((σ : ℂ) + y * I)) slitPlane :=
  (differentiableOn_integral_mul_cpow_add_mul_I hg_meas σ hg).analyticOnNhd isOpen_slitPlane

end TauCeti

end
