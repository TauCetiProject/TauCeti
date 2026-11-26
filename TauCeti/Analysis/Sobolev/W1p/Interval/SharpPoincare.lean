/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Spectrum.Interval
public import TauCeti.Analysis.Sobolev.W1p.Interval.OneEndpoint
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Gluing
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Reparam

/-!
# The sharp Poincaré–Friedrichs inequality on an interval

On a bounded interval `(a, b)`, a class `u ∈ W^{1,2}_0(a, b)` satisfies the sharp Poincaré
inequality `‖u‖_{L²(a,b)} ≤ (b - a) / π ‖u'‖_{L²(a,b)}`
(`TauCeti.W1p.norm_value_le_div_pi_mul_norm_gradient_of_mem_w1p0Submodule`), whose constant is
given by the first Dirichlet eigenvalue `(π / (b - a))²` of `-d²/dx²` on `(a, b)`. This file treats
a class `u ∈ W^{1,2}(a, b)` whose continuous representative vanishes at only one endpoint. It
satisfies the **sharp Poincaré–Friedrichs inequality**

`‖u‖_{L²(a,b)} ≤ 2 (b - a) / π ‖u'‖_{L²(a,b)}`

(`TauCeti.W1p.norm_value_le_two_mul_div_pi_mul_norm_gradient_of_intervalTraceL_fst_eq_zero` and its
version at `b`), and the constant `2 (b - a) / π` is optimal
(`TauCeti.W1p.isLeast_norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero`), attained by
`sin (π (t - a) / (2 (b - a)))`. Its inverse square `(π / (2 (b - a)))²` is a quarter of the first
Dirichlet eigenvalue. By the trace
characterization of `W^{1,2}_{{a}}(a, b)`
(`TauCeti.W1p.mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_fst_eq_zero`) these are
statements about the Sobolev functions vanishing on the boundary part `{a}`; on `(0, 1)` the optimal
Poincaré–Friedrichs constant is `2 / π`, compared with the constant `b - a = 1` of
`TauCeti.W1p.norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero`, valid for every `p`.

## The argument

The even reflection `t ↦ u(b - |t - b|)` of `u` in `b` vanishes at both endpoints of
`(a, 2b - a)`, an interval twice as long, and both its `L²` norm and the `L²` norm of its derivative
are `√2` times those of `u`. The sharp Poincaré inequality on `H¹₀(a, 2b - a)`, with constant
`2 (b - a) / π`, therefore gives the inequality for `u`. The reflection is built from the absolutely
continuous representative of `u`
(`TauCeti.W1p.absolutelyContinuousOnInterval_intervalRepresentativeL`), and an absolutely
continuous function vanishing at both endpoints with square integrable derivative is a class of
`H¹₀` (`AbsolutelyContinuousOnInterval.exists_mem_w1p0Submodule_value_gradient_ae_eq`).
For optimality, `S(t) = sin (π (t - a) / (2 (b - a)))` vanishes at `a` and
`∫_a^b S'² = (π / (2 (b - a)))² ∫_a^b S²`, since `cos²` and `sin²` have the same integral over
`[0, π / 2]`.

## Main declarations

* `TauCeti.W1p.norm_value_le_two_mul_div_pi_mul_norm_gradient_of_intervalTraceL_fst_eq_zero` and
  `TauCeti.W1p.norm_value_le_two_mul_div_pi_mul_norm_gradient_of_intervalTraceL_snd_eq_zero`: the
  sharp Poincaré–Friedrichs inequality for classes vanishing at `a`, respectively at `b`.
* `TauCeti.W1p.isLeast_norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero` and
  `TauCeti.W1p.isLeast_norm_value_le_mul_norm_gradient_of_intervalTraceL_snd_eq_zero`: the
  constant `2 (b - a) / π` is optimal.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Section 8.6
  (the Sturm–Liouville problem) and Section 9.8 (the first eigenvalue as the optimal Poincaré
  constant).
-/

public section

noncomputable section

open MeasureTheory Set Real TopologicalSpace
open scoped ENNReal

namespace TauCeti.W1p

variable {a b : ℝ}

/-- The squared `L²(a, b)` norm of a class with a representative `G` is `∫_a^b G²`. -/
private theorem norm_sq_eq_intervalIntegral_sq (hab : a ≤ b)
    {f : Lp ℝ 2 (volume.restrict (Ioo a b))} {G : ℝ → ℝ}
    (h : f =ᵐ[volume.restrict (Ioo a b)] G) : ‖f‖ ^ 2 = ∫ t in a..b, G t ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo]
  exact integral_congr_ae (h.mono fun t ht => by simp [ht, sq])

/-! ### One vanishing endpoint, by reflection -/

/-- The even reflection `t ↦ G (b - |t - b|)` of a function `G` in the point `b`. -/
private def reflect (G : ℝ → ℝ) (b t : ℝ) : ℝ := G (b - |t - b|)

private theorem reflect_of_le (G : ℝ → ℝ) {b t : ℝ} (ht : t ≤ b) : reflect G b t = G t := by
  rw [reflect, abs_of_nonpos (sub_nonpos.2 ht), sub_neg_eq_add, add_sub_cancel]

private theorem reflect_of_ge (G : ℝ → ℝ) {b t : ℝ} (ht : b ≤ t) :
    reflect G b t = G (2 * b - t) := by
  rw [reflect, abs_of_nonneg (sub_nonneg.2 ht)]
  congr 1
  ring

private theorem deriv_reflect_of_lt (G : ℝ → ℝ) {b t : ℝ} (ht : t < b) :
    deriv (reflect G b) t = deriv G t :=
  Filter.EventuallyEq.deriv_eq <|
    Filter.eventually_of_mem (Iio_mem_nhds ht) fun _ hs => reflect_of_le G (le_of_lt hs)

private theorem deriv_reflect_of_gt (G : ℝ → ℝ) {b t : ℝ} (ht : b < t) :
    deriv (reflect G b) t = -deriv G (2 * b - t) := by
  rw [Filter.EventuallyEq.deriv_eq (f := fun s => G (2 * b - s)) <|
    Filter.eventually_of_mem (Ioi_mem_nhds ht) fun _ hs => reflect_of_ge G (le_of_lt hs),
    deriv_comp_const_sub]

/-- The even reflection of an absolutely continuous function on `[a, b]` in `b` is absolutely
continuous on `[a, 2b - a]`. -/
private theorem absolutelyContinuousOnInterval_reflect (hab : a < b) {G : ℝ → ℝ}
    (hG : AbsolutelyContinuousOnInterval G a b) :
    AbsolutelyContinuousOnInterval (reflect G b) a (2 * b - a) := by
  have hbc : b ≤ 2 * b - a := by linarith
  have hmap : MapsTo (fun t : ℝ => -1 * t + 2 * b) (uIcc b (2 * b - a)) (uIcc a b) := by
    intro t ht
    rw [uIcc_of_le hbc] at ht
    rw [uIcc_of_le hab.le]
    constructor <;> linarith [ht.1, ht.2]
  refine (hG.congr fun t ht => ?_).trans ((hG.comp_affine (-1) (2 * b) hmap).congr fun t ht => ?_)
  · rw [uIcc_of_le hab.le] at ht
    exact (reflect_of_le G ht.2).symm
  · rw [uIcc_of_le hbc] at ht
    rw [Function.comp_apply, reflect_of_ge G ht.1]
    congr 1
    ring

/-- A function agreeing with `g` on `(a, b)` and with `t ↦ g (2b - t)` on `(b, 2b - a)` is
integrable on `[a, 2b - a]` if `g` is integrable on `[a, b]`, with twice its integral. -/
private theorem intervalIntegrable_and_integral_eq_two_mul (hab : a < b) {f g : ℝ → ℝ}
    (hg : IntervalIntegrable g volume a b) (h₁ : EqOn f g (Ioo a b))
    (h₂ : EqOn f (fun t => g (2 * b - t)) (Ioo b (2 * b - a))) :
    IntervalIntegrable f volume a (2 * b - a) ∧
      ∫ t in a..(2 * b - a), f t = 2 * ∫ t in a..b, g t := by
  have hbc : b ≤ 2 * b - a := by linarith
  have h2b : 2 * b - b = b := by ring
  rw [← uIoo_of_le hab.le] at h₁
  rw [← uIoo_of_le hbc] at h₂
  have hf₁ : IntervalIntegrable f volume a b := hg.congr_uIoo h₁.symm
  have hf₂ : IntervalIntegrable f volume b (2 * b - a) := by
    have := (hg.comp_sub_left (2 * b)).symm
    rw [h2b] at this
    exact this.congr_uIoo h₂.symm
  refine ⟨hf₁.trans hf₂, ?_⟩
  rw [← intervalIntegral.integral_add_adjacent_intervals hf₁ hf₂,
    intervalIntegral.integral_congr_uIoo h₁, intervalIntegral.integral_congr_uIoo h₂,
    intervalIntegral.integral_comp_sub_left g, sub_sub_cancel, h2b, two_mul]

/-- **The sharp Poincaré inequality at one endpoint, for absolutely continuous functions.** If `G`
is absolutely continuous on `[a, b]`, vanishes at `a` and has square integrable derivative, then
`(π / (2 (b - a)))² ∫_a^b G² ≤ ∫_a^b G'²`. The even reflection of `G` in `b` vanishes at both
endpoints of `(a, 2b - a)`, and the sharp Poincaré inequality on `H¹₀(a, 2b - a)` applies to it;
both of its integrals are twice those of `G`. -/
private theorem sq_mul_integral_sq_le_of_eq_zero (hab : a < b) {G : ℝ → ℝ}
    (hG : AbsolutelyContinuousOnInterval G a b)
    (hdG : IntervalIntegrable (fun t => deriv G t ^ 2) volume a b) (hGa : G a = 0) :
    (π / (2 * (b - a))) ^ 2 * ∫ t in a..b, G t ^ 2 ≤ ∫ t in a..b, deriv G t ^ 2 := by
  have hbc : b < 2 * b - a := by linarith
  have hac : a < 2 * b - a := hab.trans hbc
  have hF := absolutelyContinuousOnInterval_reflect hab hG
  obtain ⟨-, hFsq⟩ := intervalIntegrable_and_integral_eq_two_mul hab
    (f := fun t => reflect G b t ^ 2) (g := fun t => G t ^ 2)
    (hG.continuousOn.pow 2).intervalIntegrable
    (fun t ht => by simp only [reflect_of_le G ht.2.le])
    (fun t ht => by simp only [reflect_of_ge G ht.1.le])
  obtain ⟨hdFi, hdFsq⟩ := intervalIntegrable_and_integral_eq_two_mul hab
    (f := fun t => deriv (reflect G b) t ^ 2) hdG
    (fun t ht => by simp only [deriv_reflect_of_lt G ht.2])
    (fun t ht => by simp only [deriv_reflect_of_gt G ht.1, neg_sq])
  -- The reflection represents a class of `H¹₀(a, 2b - a)`.
  obtain ⟨w, hw, hwv, hwg⟩ := hF.exists_mem_w1p0Submodule_value_gradient_ae_eq
    ((memLp_two_iff_integrable_sq (measurable_deriv _).aestronglyMeasurable).2
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hac.le).1 hdFi)) (by norm_num)
    (by rw [reflect_of_le G hab.le, hGa]) (by rw [reflect_of_ge G hbc.le, sub_sub_cancel, hGa])
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_value_le_div_pi_mul_norm_gradient_of_mem_w1p0Submodule hac hw) 2
  rw [mul_pow, norm_sq_eq_intervalIntegral_sq hac.le hwv,
    norm_sq_eq_intervalIntegral_sq hac.le hwg, hFsq, hdFsq] at h
  have hk : (π / (2 * (b - a))) ^ 2 * ((2 * b - a - a) / π) ^ 2 = 1 := by
    field_simp [(sub_pos.2 hab).ne', pi_ne_zero]
    ring
  calc (π / (2 * (b - a))) ^ 2 * ∫ t in a..b, G t ^ 2
      ≤ (π / (2 * (b - a))) ^ 2 * (((2 * b - a - a) / π) ^ 2 * ∫ t in a..b, deriv G t ^ 2) := by
        gcongr
        linarith
    _ = ∫ t in a..b, deriv G t ^ 2 := by rw [← mul_assoc, hk, one_mul]

/-- Reversing `[a, b]` does not change integrals over it. -/
private theorem integral_comp_add_sub (f : ℝ → ℝ) :
    ∫ t in a..b, f (a + b - t) = ∫ t in a..b, f t := by
  rw [intervalIntegral.integral_comp_sub_left, add_sub_cancel_left, add_sub_cancel_right]

/-- The sharp Poincaré inequality at the right endpoint, for absolutely continuous functions,
from the one at the left endpoint applied to `t ↦ G (a + b - t)`. -/
private theorem sq_mul_integral_sq_le_of_eq_zero_right (hab : a < b) {G : ℝ → ℝ}
    (hG : AbsolutelyContinuousOnInterval G a b)
    (hdG : IntervalIntegrable (fun t => deriv G t ^ 2) volume a b) (hGb : G b = 0) :
    (π / (2 * (b - a))) ^ 2 * ∫ t in a..b, G t ^ 2 ≤ ∫ t in a..b, deriv G t ^ 2 := by
  have hdG' : IntervalIntegrable (fun t => deriv (fun s => G (a + b - s)) t ^ 2) volume a b := by
    simpa only [deriv_comp_const_sub, neg_sq, add_sub_cancel_left, add_sub_cancel_right] using
      (hdG.comp_sub_left (a + b)).symm
  have hG' : AbsolutelyContinuousOnInterval (fun s => G (a + b - s)) a b := by
    refine (hG.comp_affine (-1) (a + b) fun t ht => ?_).congr fun t _ => ?_
    · rw [uIcc_of_le hab.le] at ht ⊢
      constructor <;> linarith [ht.1, ht.2]
    · simp only [Function.comp_apply]
      congr 1
      ring
  have h := sq_mul_integral_sq_le_of_eq_zero hab hG' hdG' (by simpa using hGb)
  simpa only [deriv_comp_const_sub, neg_sq, integral_comp_add_sub (fun t => G t ^ 2),
    integral_comp_add_sub (fun t => deriv G t ^ 2)] using h

/-- From `(π / (2 (b - a)))² x² ≤ y²` for nonnegative `x, y`, the linear form
`x ≤ 2 (b - a) / π y`. -/
private theorem le_two_mul_div_pi_mul_of_sq (hab : a < b) {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (h : (π / (2 * (b - a))) ^ 2 * x ^ 2 ≤ y ^ 2) : x ≤ 2 * (b - a) / π * y := by
  rw [← mul_pow, pow_le_pow_iff_left₀ (by positivity) hy two_ne_zero] at h
  calc x = 2 * (b - a) / π * (π / (2 * (b - a)) * x) := by
        field_simp [(sub_pos.2 hab).ne']
    _ ≤ 2 * (b - a) / π * y := by gcongr

/-- The norms of a class of `W^{1,2}(a, b)` as integrals of its continuous representative. -/
private theorem norm_sq_value_gradient_eq (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    ‖value u‖ ^ 2 = ∫ t in a..b, intervalRepresentativeL hab u (projIcc a b hab.le t) ^ 2 ∧
      ‖gradient u‖ ^ 2 = ∫ t in a..b,
        deriv (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)) t ^ 2 := by
  refine ⟨norm_sq_eq_intervalIntegral_sq hab.le (value_ae_eq_intervalRepresentativeL hab u),
    norm_sq_eq_intervalIntegral_sq hab.le ((ae_restrict_iff' measurableSet_Ioo).2 ?_)⟩
  filter_upwards [ae_hasDerivAt_intervalRepresentativeL hab u] with t ht htI
  exact (ht (uIoc_of_le hab.le ▸ Ioo_subset_Ioc_self htI)).deriv.symm

/-- The derivative of the continuous representative of a class of `W^{1,2}(a, b)` is square
integrable on `(a, b)`. -/
private theorem intervalIntegrable_deriv_intervalRepresentativeL_sq (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    IntervalIntegrable
      (fun t => deriv (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)) t ^ 2)
      volume a b := by
  refine (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 ?_
  refine (Lp.memLp (gradient u)).integrable_sq.congr ((ae_restrict_iff' measurableSet_Ioo).2 ?_)
  filter_upwards [ae_hasDerivAt_intervalRepresentativeL hab u] with t ht htI
  rw [(ht (uIoc_of_le hab.le ▸ Ioo_subset_Ioc_self htI)).deriv]

/-- **The sharp Poincaré–Friedrichs inequality on an interval, vanishing at `a`.** If the
continuous representative of `u ∈ W^{1,2}(a, b)` vanishes at `a`, then
`‖u‖_{L²(a,b)} ≤ 2 (b - a) / π ‖u'‖_{L²(a,b)}`. The constant is optimal
(`TauCeti.W1p.isLeast_norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero`). -/
theorem norm_value_le_two_mul_div_pi_mul_norm_gradient_of_intervalTraceL_fst_eq_zero
    (hab : a < b) {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} (hu : (intervalTraceL hab u).1 = 0) :
    ‖value u‖ ≤ 2 * (b - a) / π * ‖gradient u‖ := by
  refine le_two_mul_div_pi_mul_of_sq hab (norm_nonneg _) (norm_nonneg _) ?_
  rw [(norm_sq_value_gradient_eq hab u).1, (norm_sq_value_gradient_eq hab u).2]
  refine sq_mul_integral_sq_le_of_eq_zero hab
    (absolutelyContinuousOnInterval_intervalRepresentativeL hab u)
    (intervalIntegrable_deriv_intervalRepresentativeL_sq hab u) ?_
  rw [intervalTraceL_apply] at hu
  simpa only [projIcc_left] using hu

/-- **The sharp Poincaré–Friedrichs inequality on an interval, vanishing at `b`.** If the
continuous representative of `u ∈ W^{1,2}(a, b)` vanishes at `b`, then
`‖u‖_{L²(a,b)} ≤ 2 (b - a) / π ‖u'‖_{L²(a,b)}`. The constant is optimal
(`TauCeti.W1p.isLeast_norm_value_le_mul_norm_gradient_of_intervalTraceL_snd_eq_zero`). -/
theorem norm_value_le_two_mul_div_pi_mul_norm_gradient_of_intervalTraceL_snd_eq_zero
    (hab : a < b) {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} (hu : (intervalTraceL hab u).2 = 0) :
    ‖value u‖ ≤ 2 * (b - a) / π * ‖gradient u‖ := by
  refine le_two_mul_div_pi_mul_of_sq hab (norm_nonneg _) (norm_nonneg _) ?_
  rw [(norm_sq_value_gradient_eq hab u).1, (norm_sq_value_gradient_eq hab u).2]
  refine sq_mul_integral_sq_le_of_eq_zero_right hab
    (absolutelyContinuousOnInterval_intervalRepresentativeL hab u)
    (intervalIntegrable_deriv_intervalRepresentativeL_sq hab u) ?_
  rw [intervalTraceL_apply] at hu
  simpa only [projIcc_right] using hu

/-! ### Optimality -/

/-- A `C¹` function defines a class of `W^{1,2}(a, b)` with its endpoint values as trace, whose
norms are the `L²(a, b)` norms of the function and its derivative. -/
private theorem exists_intervalTraceL_eq_and_norm_sq_eq (hab : a < b) {S : ℝ → ℝ}
    (hS : ContDiff ℝ 1 S) :
    ∃ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2, intervalTraceL hab u = (S a, S b) ∧
      ‖value u‖ ^ 2 = ∫ t in a..b, S t ^ 2 ∧ ‖gradient u‖ ^ 2 = ∫ t in a..b, deriv S t ^ 2 := by
  obtain ⟨u, hv, hg⟩ := hS.contDiffOn.absolutelyContinuousOnInterval.exists_w1p_value_gradient_ae_eq
    ((hS.continuous_deriv le_rfl).continuousOn.memLp_restrict_of_subset_isCompact isCompact_Icc
      measurableSet_Ioo Ioo_subset_Icc_self 2)
  have heq : intervalRepresentativeL hab u =
      ⟨fun t ↦ S t, hS.continuous.comp continuous_subtypeVal⟩ := by
    refine (intervalRepresentativeL_eq_iff hab u _).2 ?_
    filter_upwards [hv, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [ht, ContinuousMap.coe_mk, projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem)]
  refine ⟨u, ?_, norm_sq_eq_intervalIntegral_sq hab.le hv, norm_sq_eq_intervalIntegral_sq hab.le hg⟩
  rw [intervalTraceL_apply, heq]
  rfl

/-- The first mode `S t = sin (π (t - a) / (2 (b - a)))` vanishes at `a`, and
`∫_a^b S'² = (π / (2 (b - a)))² ∫_a^b S²` with `∫_a^b S² > 0`. -/
private theorem exists_contDiff_eq_zero_and_integral_deriv_sq_eq (hab : a < b) :
    ∃ S : ℝ → ℝ, ContDiff ℝ 1 S ∧ S a = 0 ∧ 0 < ∫ t in a..b, S t ^ 2 ∧
      ∫ t in a..b, deriv S t ^ 2 = (π / (2 * (b - a))) ^ 2 * ∫ t in a..b, S t ^ 2 := by
  set ω := π / (2 * (b - a)) with hω
  have hω0 : ω ≠ 0 := by positivity
  have hωb : ω * b - ω * a = π / 2 := by
    rw [hω]
    field_simp [(sub_pos.2 hab).ne']
  have hd : ∀ t, deriv (fun t => sin (ω * t - ω * a)) t = ω * cos (ω * t - ω * a) := fun t => by
    rw [(((hasDerivAt_id' t).const_mul ω).sub_const (ω * a)).sin.deriv]
    ring
  have hsin : ∫ t in a..b, sin (ω * t - ω * a) ^ 2 = ω⁻¹ * (π / 4) := by
    rw [intervalIntegral.integral_comp_mul_sub (fun x => sin x ^ 2) hω0, sub_self, hωb,
      integral_sin_sq, smul_eq_mul, sin_zero, cos_pi_div_two]
    ring
  have hcos : ∫ t in a..b, cos (ω * t - ω * a) ^ 2 = ω⁻¹ * (π / 4) := by
    rw [intervalIntegral.integral_comp_mul_sub (fun x => cos x ^ 2) hω0, sub_self, hωb,
      integral_cos_sq, smul_eq_mul, sin_zero, cos_pi_div_two]
    ring
  refine ⟨fun t => sin (ω * t - ω * a), by fun_prop, by simp, ?_, ?_⟩
  · rw [hsin]
    positivity
  · simp only [hd, mul_pow, intervalIntegral.integral_const_mul, hcos, hsin]

/-- The optimal constant in a Poincaré–Friedrichs inequality on a class of `W^{1,2}(a, b)` that
satisfies it with `2 (b - a) / π` and contains a nonzero function attaining it. -/
private theorem isLeast_of_exists (hab : a < b) {P : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2 → Prop}
    (hle : ∀ u, P u → ‖value u‖ ≤ 2 * (b - a) / π * ‖gradient u‖)
    (hex : ∃ u, P u ∧ ‖value u‖ ≠ 0 ∧
      ‖gradient u‖ ^ 2 = (π / (2 * (b - a))) ^ 2 * ‖value u‖ ^ 2) :
    IsLeast {C | ∀ u, P u → ‖value u‖ ≤ C * ‖gradient u‖} (2 * (b - a) / π) := by
  refine ⟨hle, fun C hC => ?_⟩
  obtain ⟨u, hu, hu0, hug⟩ := hex
  rw [← mul_pow, pow_left_inj₀ (norm_nonneg _) (by positivity) two_ne_zero] at hug
  have h := hC u hu
  rw [hug, ← mul_assoc] at h
  have h1 : 1 ≤ C * (π / (2 * (b - a))) := by
    simpa using le_of_mul_le_mul_right (by simpa using h) ((norm_nonneg _).lt_of_ne' hu0)
  have hpos : 0 < π / (2 * (b - a)) := by have := sub_pos.2 hab; positivity
  calc 2 * (b - a) / π = 1 / (π / (2 * (b - a))) := by field_simp
    _ ≤ C := by rwa [div_le_iff₀ hpos]

/-- **The sharp Poincaré–Friedrichs constant on an interval, vanishing at `a`.** The least `C` with
`‖u‖_{L²(a,b)} ≤ C ‖u'‖_{L²(a,b)}` for every `u ∈ W^{1,2}(a, b)` vanishing at `a` is
`2 (b - a) / π`, attained by `sin (π (t - a) / (2 (b - a)))`. By the trace characterization
(`TauCeti.W1p.mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_fst_eq_zero`) these are the
`u ∈ W^{1,2}_{{a}}(a, b)`. -/
theorem isLeast_norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero (hab : a < b) :
    IsLeast {C | ∀ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2, (intervalTraceL hab u).1 = 0 →
      ‖value u‖ ≤ C * ‖gradient u‖} (2 * (b - a) / π) := by
  refine isLeast_of_exists hab
    (fun _ => norm_value_le_two_mul_div_pi_mul_norm_gradient_of_intervalTraceL_fst_eq_zero hab) ?_
  obtain ⟨S, hS, hSa, hpos, hSd⟩ := exists_contDiff_eq_zero_and_integral_deriv_sq_eq hab
  obtain ⟨u, htr, hv, hg⟩ := exists_intervalTraceL_eq_and_norm_sq_eq hab hS
  refine ⟨u, by rw [htr, hSa], fun h => ?_, by rw [hg, hv, hSd]⟩
  rw [← hv, h] at hpos
  simp at hpos

/-- **The sharp Poincaré–Friedrichs constant on an interval, vanishing at `b`.** The least `C` with
`‖u‖_{L²(a,b)} ≤ C ‖u'‖_{L²(a,b)}` for every `u ∈ W^{1,2}(a, b)` vanishing at `b` is
`2 (b - a) / π`, attained by `sin (π (b - t) / (2 (b - a)))`. By the trace characterization
(`TauCeti.W1p.mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_snd_eq_zero`) these are the
`u ∈ W^{1,2}_{{b}}(a, b)`. -/
theorem isLeast_norm_value_le_mul_norm_gradient_of_intervalTraceL_snd_eq_zero (hab : a < b) :
    IsLeast {C | ∀ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2, (intervalTraceL hab u).2 = 0 →
      ‖value u‖ ≤ C * ‖gradient u‖} (2 * (b - a) / π) := by
  refine isLeast_of_exists hab
    (fun _ => norm_value_le_two_mul_div_pi_mul_norm_gradient_of_intervalTraceL_snd_eq_zero hab) ?_
  obtain ⟨S, hS, hSa, hpos, hSd⟩ := exists_contDiff_eq_zero_and_integral_deriv_sq_eq hab
  obtain ⟨u, htr, hv, hg⟩ := exists_intervalTraceL_eq_and_norm_sq_eq
    (S := fun t => S (a + b - t)) hab (hS.comp (contDiff_const.sub contDiff_id))
  have h₁ : ∫ t in a..b, S (a + b - t) ^ 2 = ∫ t in a..b, S t ^ 2 :=
    integral_comp_add_sub fun t => S t ^ 2
  have h₂ : ∫ t in a..b, deriv (fun t => S (a + b - t)) t ^ 2 = ∫ t in a..b, deriv S t ^ 2 := by
    simp only [deriv_comp_const_sub, neg_sq]
    exact integral_comp_add_sub fun t => deriv S t ^ 2
  rw [h₁] at hv
  rw [h₂] at hg
  refine ⟨u, by rw [htr, add_sub_cancel_right, hSa], fun h => ?_, by rw [hg, hv, hSd]⟩
  rw [← hv, h] at hpos
  simp at hpos

end TauCeti.W1p
