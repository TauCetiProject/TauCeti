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
import TauCeti.MeasureTheory.Function.Lp.Integral.L2NormSq
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Reflection

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

The even reflection `t ↦ u(b - |t - b|)` of `u` in `b`, absolutely continuous by
`AbsolutelyContinuousOnInterval.comp_sub_abs_sub`, vanishes at both endpoints of
`(a, 2b - a)`, an interval twice as long, and both its `L²` norm and the `L²` norm of its derivative
are `√2` times those of `u` (`TauCeti.intervalIntegral.integral_eq_two_smul_of_eqOn_reflect`).
The sharp Poincaré inequality on `H¹₀(a, 2b - a)`, with constant `2 (b - a) / π`, therefore gives
the inequality for `u`. The reflection is built from the absolutely
continuous representative of `u`
(`TauCeti.W1p.absolutelyContinuousOnInterval_intervalRepresentativeL`), and an absolutely
continuous function vanishing at both endpoints with square integrable derivative is a class of
`H¹₀` (`AbsolutelyContinuousOnInterval.exists_mem_w1p0Submodule_value_gradient_ae_eq`).
For optimality, `S(t) = sin (π (t - a) / (2 (b - a)))` vanishes at `a` and
`∫_a^b S'² = (π / (2 (b - a)))² ∫_a^b S²`, since `cos²` and `sin²` have the same integral over
`[0, π / 2]`.

## Main declarations

* `AbsolutelyContinuousOnInterval.sq_mul_integral_sq_le_of_left_eq_zero` and
  `AbsolutelyContinuousOnInterval.sq_mul_integral_sq_le_of_right_eq_zero`: the same inequality,
  `(π / (2 (b - a)))² ∫_a^b G² ≤ ∫_a^b G'²`, for an absolutely continuous function `G` vanishing
  at `a`, respectively at `b`, with square integrable derivative.
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

/-- **The sharp Poincaré inequality at one endpoint, for absolutely continuous functions.** If `G`
is absolutely continuous on `[a, b]`, vanishes at `a` and has square integrable derivative, then
`(π / (2 (b - a)))² ∫_a^b G² ≤ ∫_a^b G'²`. The even reflection of `G` in `b` vanishes at both
endpoints of `(a, 2b - a)`, and the sharp Poincaré inequality on `H¹₀(a, 2b - a)` applies to it;
both of its integrals are twice those of `G`. -/
theorem _root_.AbsolutelyContinuousOnInterval.sq_mul_integral_sq_le_of_left_eq_zero {G : ℝ → ℝ}
    (hG : AbsolutelyContinuousOnInterval G a b) (hab : a < b)
    (hdG : IntervalIntegrable (fun t => deriv G t ^ 2) volume a b) (hGa : G a = 0) :
    (π / (2 * (b - a))) ^ 2 * ∫ t in a..b, G t ^ 2 ≤ ∫ t in a..b, deriv G t ^ 2 := by
  have hbc : b < 2 * b - a := by linarith
  have hac : a < 2 * b - a := hab.trans hbc
  have hF : AbsolutelyContinuousOnInterval (reflect G b) a (2 * b - a) := hG.comp_sub_abs_sub hab.le
  have hFsq := intervalIntegral.integral_eq_two_smul_of_eqOn_reflect
    (f := fun t => reflect G b t ^ 2) (g := fun t => G t ^ 2)
    (hG.continuousOn.pow 2).intervalIntegrable
    (fun t ht => by simp only [reflect_of_le G (uIoo_of_le hab.le ▸ ht).2.le])
    (fun t ht => by simp only [reflect_of_ge G (uIoo_of_le hbc.le ▸ ht).1.le])
  have hdF₁ : EqOn (fun t => deriv (reflect G b) t ^ 2) (fun t => deriv G t ^ 2) (uIoo a b) :=
    fun t ht => by simp only [deriv_reflect_of_lt G (uIoo_of_le hab.le ▸ ht).2]
  have hdF₂ : EqOn (fun t => deriv (reflect G b) t ^ 2) (fun t => deriv G (2 * b - t) ^ 2)
      (uIoo b (2 * b - a)) :=
    fun t ht => by simp only [deriv_reflect_of_gt G (uIoo_of_le hbc.le ▸ ht).1, neg_sq]
  have hdFsq := intervalIntegral.integral_eq_two_smul_of_eqOn_reflect hdG hdF₁ hdF₂
  obtain ⟨hdFi₁, hdFi₂⟩ := hdG.of_eqOn_reflect hdF₁ hdF₂
  -- The reflection represents a class of `H¹₀(a, 2b - a)`.
  obtain ⟨w, hw, hwv, hwg⟩ := hF.exists_mem_w1p0Submodule_value_gradient_ae_eq
    ((memLp_two_iff_integrable_sq (measurable_deriv _).aestronglyMeasurable).2
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le hac.le).1 (hdFi₁.trans hdFi₂)))
    (by norm_num) (by rw [reflect_of_le G hab.le, hGa])
    (by rw [reflect_of_ge G hbc.le, sub_sub_cancel, hGa])
  have h := pow_le_pow_left₀ (norm_nonneg _)
    (norm_value_le_div_pi_mul_norm_gradient_of_mem_w1p0Submodule hac hw) 2
  rw [mul_pow, L2.norm_sq_eq_intervalIntegral_sq_of_ae_eq hac.le hwv,
    L2.norm_sq_eq_intervalIntegral_sq_of_ae_eq hac.le hwg, hFsq, hdFsq, smul_eq_mul,
    smul_eq_mul] at h
  have hk : (π / (2 * (b - a))) ^ 2 * ((2 * b - a - a) / π) ^ 2 = 1 := by
    field_simp [(sub_pos.2 hab).ne', pi_ne_zero]
    ring
  calc (π / (2 * (b - a))) ^ 2 * ∫ t in a..b, G t ^ 2
      ≤ (π / (2 * (b - a))) ^ 2 * (((2 * b - a - a) / π) ^ 2 * ∫ t in a..b, deriv G t ^ 2) := by
        gcongr
        linarith
    _ = ∫ t in a..b, deriv G t ^ 2 := by rw [← mul_assoc, hk, one_mul]

/-- **The sharp Poincaré inequality at the right endpoint, for absolutely continuous functions.**
If `G` is absolutely continuous on `[a, b]`, vanishes at `b` and has square integrable derivative,
then `(π / (2 (b - a)))² ∫_a^b G² ≤ ∫_a^b G'²`. This is
`AbsolutelyContinuousOnInterval.sq_mul_integral_sq_le_of_left_eq_zero` applied to
`t ↦ G (a + b - t)`. -/
theorem _root_.AbsolutelyContinuousOnInterval.sq_mul_integral_sq_le_of_right_eq_zero {G : ℝ → ℝ}
    (hG : AbsolutelyContinuousOnInterval G a b) (hab : a < b)
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
  have h := hG'.sq_mul_integral_sq_le_of_left_eq_zero hab hdG' (by simpa using hGb)
  simpa only [deriv_comp_const_sub, neg_sq,
    intervalIntegral.integral_comp_add_sub (fun t => G t ^ 2),
    intervalIntegral.integral_comp_add_sub (fun t => deriv G t ^ 2)] using h

/-- A class of `W^{1,2}(a, b)` whose continuous representative vanishes at `c ∈ [a, b]` satisfies
`‖u‖_{L²(a,b)} ≤ 2 (b - a) / π ‖u'‖_{L²(a,b)}`, provided that every absolutely continuous function
vanishing at `c` with square integrable derivative satisfies
`(π / (2 (b - a)))² ∫_a^b G² ≤ ∫_a^b G'²`. -/
private theorem norm_value_le_of_forall_sq_mul_integral_sq_le (hab : a < b) {c : ℝ}
    (hc : c ∈ Icc a b) (H : ∀ G : ℝ → ℝ, AbsolutelyContinuousOnInterval G a b →
      IntervalIntegrable (fun t => deriv G t ^ 2) volume a b → G c = 0 →
        (π / (2 * (b - a))) ^ 2 * ∫ t in a..b, G t ^ 2 ≤ ∫ t in a..b, deriv G t ^ 2)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} (hu : intervalRepresentativeL hab u ⟨c, hc⟩ = 0) :
    ‖value u‖ ≤ 2 * (b - a) / π * ‖gradient u‖ := by
  have := sub_pos.2 hab
  rw [← inv_div]
  refine (le_inv_mul_iff₀ (by positivity)).2 (le_of_sq_le_sq ?_ (norm_nonneg _))
  obtain ⟨hac, hdF⟩ := (mem_range_intervalRepresentativeL_iff hab _).1 ⟨u, rfl⟩
  rw [mul_pow, L2.norm_sq_eq_intervalIntegral_sq_of_ae_eq hab.le
      (value_ae_eq_intervalRepresentativeL hab u),
    L2.norm_sq_eq_intervalIntegral_sq_of_ae_eq hab.le
      (gradient_ae_eq_deriv_intervalRepresentativeL hab u)]
  exact H _ hac ((intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 hdF.integrable_sq)
    (by simpa only [projIcc_of_mem hab.le hc] using hu)

/-- **The sharp Poincaré–Friedrichs inequality on an interval, vanishing at `a`.** If the
continuous representative of `u ∈ W^{1,2}(a, b)` vanishes at `a`, then
`‖u‖_{L²(a,b)} ≤ 2 (b - a) / π ‖u'‖_{L²(a,b)}`. The constant is optimal
(`TauCeti.W1p.isLeast_norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero`). -/
theorem norm_value_le_two_mul_div_pi_mul_norm_gradient_of_intervalTraceL_fst_eq_zero
    (hab : a < b) {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} (hu : (intervalTraceL hab u).1 = 0) :
    ‖value u‖ ≤ 2 * (b - a) / π * ‖gradient u‖ := by
  rw [intervalTraceL_apply] at hu
  exact norm_value_le_of_forall_sq_mul_integral_sq_le hab _
    (fun _ hG => hG.sq_mul_integral_sq_le_of_left_eq_zero hab) hu

/-- **The sharp Poincaré–Friedrichs inequality on an interval, vanishing at `b`.** If the
continuous representative of `u ∈ W^{1,2}(a, b)` vanishes at `b`, then
`‖u‖_{L²(a,b)} ≤ 2 (b - a) / π ‖u'‖_{L²(a,b)}`. The constant is optimal
(`TauCeti.W1p.isLeast_norm_value_le_mul_norm_gradient_of_intervalTraceL_snd_eq_zero`). -/
theorem norm_value_le_two_mul_div_pi_mul_norm_gradient_of_intervalTraceL_snd_eq_zero
    (hab : a < b) {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} (hu : (intervalTraceL hab u).2 = 0) :
    ‖value u‖ ≤ 2 * (b - a) / π * ‖gradient u‖ := by
  rw [intervalTraceL_apply] at hu
  exact norm_value_le_of_forall_sq_mul_integral_sq_le hab _
    (fun _ hG => hG.sq_mul_integral_sq_le_of_right_eq_zero hab) hu

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
  exact ⟨u, intervalTraceL_eq_of_value_ae_eq hab hS.continuous.continuousOn hv,
    L2.norm_sq_eq_intervalIntegral_sq_of_ae_eq hab.le hv,
    L2.norm_sq_eq_intervalIntegral_sq_of_ae_eq hab.le hg⟩

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
  have h1 : 1 ≤ C * (π / (2 * (b - a))) :=
    (le_mul_iff_one_le_left ((norm_nonneg _).lt_of_ne' hu0)).1 h
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
    intervalIntegral.integral_comp_add_sub fun t => S t ^ 2
  have h₂ : ∫ t in a..b, deriv (fun t => S (a + b - t)) t ^ 2 = ∫ t in a..b, deriv S t ^ 2 := by
    simp only [deriv_comp_const_sub, neg_sq]
    exact intervalIntegral.integral_comp_add_sub fun t => deriv S t ^ 2
  rw [h₁] at hv
  rw [h₂] at hg
  refine ⟨u, by rw [htr, add_sub_cancel_right, hSa], fun h => ?_, by rw [hg, hv, hSd]⟩
  rw [← hv, h] at hpos
  simp at hpos

end TauCeti.W1p
