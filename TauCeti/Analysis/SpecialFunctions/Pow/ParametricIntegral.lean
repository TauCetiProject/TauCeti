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
power `((t : ℂ) + z) ^ s` along the nonnegative real half-line `t ≥ 0` has norm comparable to
`(1 + t) ^ s.re`, locally uniformly in `z`:

`c * (1 + t) ^ s.re ≤ ‖((t : ℂ) + z) ^ s‖ ≤ C * (1 + t) ^ s.re`.

Both directions hold without any sign restriction on `s.re`: `‖(t : ℂ) + w‖` is bounded below by a
positive multiple of `1 + t` on a small neighborhood of `z` in `slitPlane` and bounded above by a
multiple of `1 + t` by the triangle inequality, while `|arg ((t : ℂ) + w)| ≤ π` controls the
exponential factor `exp (-arg ((t : ℂ) + w) * s.im)`.

Consequently, for any measure `μ` on `ℝ` and weight `g : ℝ → ℂ`, integrability of
`t ↦ g t * ((t : ℂ) + z) ^ s` on `(0, ∞)` is independent of `z ∈ slitPlane`, is equivalent to
strong measurability of `g` together with integrability of `t ↦ ‖g t‖ * (1 + t) ^ s.re`, and is
preserved when `s.re` decreases. Differentiating under the integral sign then shows that

`w ↦ ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + w) ^ s ∂μ`

is holomorphic on `slitPlane` with derivative
`s * ∫ t in Ioi (0 : ℝ), g t * ((t : ℂ) + z) ^ (s - 1) ∂μ`. These theorems drive the slit-plane
holomorphy and partial-derivative formulas for Carlson's symmetric elliptic integrals `R_C`, `R_J`,
`R_D`, and `R_G`.

## Main results

* `TauCeti.exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow` — locally uniform upper bound
  `‖((t : ℂ) + w) ^ s‖ ≤ C * (1 + t) ^ s.re` for `w` near `z ∈ slitPlane` and `t ≥ 0`.
* `TauCeti.exists_pos_mul_one_add_rpow_le_norm_ofReal_add_cpow` — matching lower bound
  `c * (1 + t) ^ s.re ≤ ‖((t : ℂ) + z) ^ s‖` for `z ∈ slitPlane` and `t ≥ 0`.
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

/-- Near any `z ∈ slitPlane`, the principal power `((t : ℂ) + w) ^ s` is bounded by a constant
multiple of `(1 + t) ^ s.re` uniformly in `w` and in `t ≥ 0`, with no sign restriction on `s`. -/
theorem exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow {z : ℂ} (hz : z ∈ slitPlane)
    (s : ℂ) :
    ∃ U ∈ 𝓝 z, U ⊆ slitPlane ∧ ∃ C, 0 < C ∧
      ∀ w ∈ U, ∀ t : ℝ, 0 ≤ t → ‖((t : ℂ) + w) ^ s‖ ≤ C * (1 + t) ^ s.re := by
  obtain ⟨c, hc, hlow⟩ := exists_pos_forall_mem_ball_mul_one_add_le_norm_add hz
  set M : ℝ := 1 + ‖z‖ + c
  have hM : 1 ≤ M := by
    have : 0 ≤ ‖z‖ := norm_nonneg z
    linarith
  have hM0 : 0 < M := zero_lt_one.trans_le hM
  refine ⟨Metric.ball z c ∩ slitPlane,
    Filter.inter_mem (Metric.ball_mem_nhds z hc) (isOpen_slitPlane.mem_nhds hz),
    Set.inter_subset_right,
    max (c ^ s.re) (M ^ s.re) * Real.exp (Real.pi * |s.im|), by positivity, ?_⟩
  intro w hw t ht
  have hw_ball : w ∈ Metric.ball z c := hw.1
  have h1t : 0 < 1 + t := by linarith
  -- Lower bound `c * (1 + t) ≤ ‖(t : ℂ) + w‖` from the uniform slit-plane distance estimate.
  have hlower : c * (1 + t) ≤ ‖(t : ℂ) + w‖ := by
    rw [add_comm (t : ℂ) w]
    exact hlow w hw_ball ⟨t, ht⟩
  -- Upper bound `‖(t : ℂ) + w‖ ≤ M * (1 + t)` from the triangle inequality on `ball z c`.
  have hupper : ‖(t : ℂ) + w‖ ≤ M * (1 + t) := by
    have hwz : ‖w - z‖ < c := by simpa [dist_eq_norm] using hw_ball
    have hw_norm : ‖w‖ ≤ ‖z‖ + c := by
      calc ‖w‖ = ‖(w - z) + z‖ := by ring_nf
        _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
        _ ≤ c + ‖z‖ := by linarith
        _ = ‖z‖ + c := add_comm _ _
    calc ‖(t : ℂ) + w‖ ≤ ‖(t : ℂ)‖ + ‖w‖ := norm_add_le _ _
      _ = t + ‖w‖ := by rw [Complex.norm_real, Real.norm_of_nonneg ht]
      _ ≤ t + (‖z‖ + c) := by linarith
      _ ≤ M * (1 + t) := by
        have : 0 ≤ (‖z‖ + c) * t := mul_nonneg (by positivity) ht
        linarith
  -- Bound the radial factor `‖(t : ℂ) + w‖ ^ s.re` according to the sign of `s.re`.
  have hrpow : ‖(t : ℂ) + w‖ ^ s.re ≤ max (c ^ s.re) (M ^ s.re) * (1 + t) ^ s.re := by
    rcases le_or_gt s.re 0 with hs | hs
    · calc ‖(t : ℂ) + w‖ ^ s.re
          ≤ (c * (1 + t)) ^ s.re := Real.rpow_le_rpow_of_nonpos (by positivity) hlower hs
        _ = c ^ s.re * (1 + t) ^ s.re := Real.mul_rpow hc.le h1t.le
        _ ≤ max (c ^ s.re) (M ^ s.re) * (1 + t) ^ s.re := by
          gcongr
          exact le_max_left _ _
    · calc ‖(t : ℂ) + w‖ ^ s.re
          ≤ (M * (1 + t)) ^ s.re := Real.rpow_le_rpow (norm_nonneg _) hupper hs.le
        _ = M ^ s.re * (1 + t) ^ s.re := Real.mul_rpow hM0.le h1t.le
        _ ≤ max (c ^ s.re) (M ^ s.re) * (1 + t) ^ s.re := by
          gcongr
          exact le_max_right _ _
  -- Bound the angular factor `1 / exp (arg * s.im) ≤ exp (π * |s.im|)`.
  have hexp : (Real.exp (((t : ℂ) + w).arg * s.im))⁻¹ ≤ Real.exp (Real.pi * |s.im|) := by
    rw [← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    calc -(((t : ℂ) + w).arg * s.im)
        ≤ |((t : ℂ) + w).arg * s.im| := neg_le_abs _
      _ = |((t : ℂ) + w).arg| * |s.im| := abs_mul _ _
      _ ≤ Real.pi * |s.im| := by
        gcongr
        exact Complex.abs_arg_le_pi _
  calc ‖((t : ℂ) + w) ^ s‖
      ≤ ‖(t : ℂ) + w‖ ^ s.re / Real.exp (((t : ℂ) + w).arg * s.im) :=
        Complex.norm_cpow_le _ _
    _ = ‖(t : ℂ) + w‖ ^ s.re * (Real.exp (((t : ℂ) + w).arg * s.im))⁻¹ := div_eq_mul_inv _ _
    _ ≤ (max (c ^ s.re) (M ^ s.re) * (1 + t) ^ s.re) * Real.exp (Real.pi * |s.im|) :=
        mul_le_mul hrpow hexp (by positivity) (by positivity)
    _ = max (c ^ s.re) (M ^ s.re) * Real.exp (Real.pi * |s.im|) * (1 + t) ^ s.re := by ring

/-- For `z ∈ slitPlane` and any `s : ℂ`, `‖((t : ℂ) + z) ^ s‖` is bounded below by a positive
multiple of `(1 + t) ^ s.re` for all `t ≥ 0`. -/
theorem exists_pos_mul_one_add_rpow_le_norm_ofReal_add_cpow {z : ℂ} (hz : z ∈ slitPlane)
    (s : ℂ) :
    ∃ c, 0 < c ∧ ∀ t : ℝ, 0 ≤ t → c * (1 + t) ^ s.re ≤ ‖((t : ℂ) + z) ^ s‖ := by
  obtain ⟨U, hU, _, C, hC, hbound⟩ :=
    exists_mem_nhds_norm_ofReal_add_cpow_le_mul_one_add_rpow hz (-s)
  have hzU : z ∈ U := mem_of_mem_nhds hU
  refine ⟨C⁻¹, inv_pos.mpr hC, fun t ht => ?_⟩
  have h1t : 0 < 1 + t := by linarith
  have hne : ((t : ℂ) + z) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero (slitPlane_ne_zero (ofReal_add_mem_slitPlane hz ht))]
    exact Complex.exp_ne_zero _
  -- Rewrite `C * ((1 + t) ^ s.re)⁻¹ = (C⁻¹ * (1 + t) ^ s.re)⁻¹` and invert.
  have h' : ‖((t : ℂ) + z) ^ s‖⁻¹ ≤ (C⁻¹ * (1 + t) ^ s.re)⁻¹ := by
    calc ‖((t : ℂ) + z) ^ s‖⁻¹
        ≤ C * (1 + t) ^ (-s).re := by
          simpa [Complex.cpow_neg, norm_inv] using hbound z hzU t ht
      _ = (C⁻¹ * (1 + t) ^ s.re)⁻¹ := by
          rw [Complex.neg_re, Real.rpow_neg h1t.le, mul_inv_rev, inv_inv, mul_comm]
  exact (inv_le_inv₀ (norm_pos_iff.mpr hne) (by positivity)).mp h'

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
if and only if `g` is strongly measurable on `(0, ∞)` and `t ↦ ‖g t‖ * (1 + t) ^ s.re` is
integrable on `(0, ∞)`. -/
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
