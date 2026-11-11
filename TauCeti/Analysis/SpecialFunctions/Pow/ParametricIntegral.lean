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
import TauCeti.Analysis.SpecialFunctions.Pow.Complex

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

end TauCeti

end
