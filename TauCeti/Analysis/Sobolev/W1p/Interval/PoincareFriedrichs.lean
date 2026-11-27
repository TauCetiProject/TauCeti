/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.OneEndpoint
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Integrals.Trigonometric.Oscillation
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Analysis.Sobolev.Poincare.SharpConstant
import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Wirtinger

/-!
# The sharp Poincaré–Friedrichs constant of an interval with one Dirichlet endpoint

On a bounded interval `(a, b)` of length `L = b - a`, every `u ∈ H¹(a, b)` vanishing at `a`
satisfies

`(π / (2 L))² ‖u‖²_{L²(a,b)} ≤ ‖u'‖²_{L²(a,b)}`,

and the constant is attained by `u(t) = sin (π (t - a) / (2 L))`. So the optimal constant `C` in
the Poincaré–Friedrichs inequality `‖u‖_{L²} ≤ C ‖u'‖_{L²}` on `H¹_{{a}}(a, b)` is `2 L / π`, below
the constant `L` that holds for every exponent
(`TauCeti.W1p.norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero`). The same holds with
the roles of the endpoints exchanged, the extremal function being `cos (π (t - a) / (2 L))`. The
constant `(π / (2 L))²` is the first eigenvalue of `-u''` with `u(a) = 0`, `u'(b) = 0`; it lies
between the Neumann value `0` and the Dirichlet value `(π / L)²`
(`TauCeti.PDE.isGreatest_mul_norm_value_sq_le_energyFormH1_intervalDomain`).

The inequality is Wirtinger's inequality for the absolutely continuous representative
(`AbsolutelyContinuousOnInterval.mul_integral_sq_le_integral_deriv_sq_of_eq_zero_left`), whose
derivative is the weak gradient almost everywhere. Its optimality comes from the explicit
extremal functions, whose norms are computed from `∫ sin² = ∫ cos² = L / 2` over a quarter
period.

## Main declarations

* `TauCeti.W1p.mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_fst_eq_zero` and
  `TauCeti.W1p.mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_snd_eq_zero`: the
  inequality on `H¹(a, b)` for classes vanishing at `a`, respectively at `b`.
* `TauCeti.W1p.isGreatest_mul_norm_value_sq_le_norm_gradient_sq_singleton_left` and
  `TauCeti.W1p.isGreatest_mul_norm_value_sq_le_norm_gradient_sq_singleton_right`: `(π / (2 L))²`
  is the best constant in `C ‖u‖² ≤ ‖u'‖²` on `H¹_{{a}}(a, b)` and on `H¹_{{b}}(a, b)`.
* `TauCeti.W1p.isLeast_norm_value_le_mul_norm_gradient_singleton_left` and
  `TauCeti.W1p.isLeast_norm_value_le_mul_norm_gradient_singleton_right`: `2 L / π` is the optimal
  Poincaré–Friedrichs constant on these spaces.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, §8.4,
  Example 5 (a boundary condition at one endpoint only) and §8.6 (the Sturm–Liouville problem).
-/

public section

noncomputable section

open MeasureTheory Set TopologicalSpace
open scoped Real

namespace TauCeti.W1p

variable {a b : ℝ}

/-- **The sharp Poincaré–Friedrichs inequality on an interval, vanishing at `a`.** If the
continuous representative of `u ∈ H¹(a, b)` vanishes at `a`, then
`(π / (2 (b - a)))² ‖u‖²_{L²(a,b)} ≤ ‖u'‖²_{L²(a,b)}`. -/
theorem mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_fst_eq_zero (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} (hu : (intervalTraceL hab u).1 = 0) :
    (π / (2 * (b - a))) ^ 2 * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2 := by
  rw [norm_value_sq_eq_integral_intervalRepresentativeL hab,
    norm_gradient_sq_eq_integral_deriv_intervalRepresentativeL hab]
  refine (absolutelyContinuousOnInterval_intervalRepresentativeL hab u)
    |>.mul_integral_sq_le_integral_deriv_sq_of_eq_zero_left hab ?_
      (intervalIntegrable_deriv_intervalRepresentativeL_sq hab u)
  rw [projIcc_left]
  rwa [intervalTraceL_apply] at hu

/-- **The sharp Poincaré–Friedrichs inequality on an interval, vanishing at `b`.** If the
continuous representative of `u ∈ H¹(a, b)` vanishes at `b`, then
`(π / (2 (b - a)))² ‖u‖²_{L²(a,b)} ≤ ‖u'‖²_{L²(a,b)}`. -/
theorem mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_snd_eq_zero (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} (hu : (intervalTraceL hab u).2 = 0) :
    (π / (2 * (b - a))) ^ 2 * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2 := by
  rw [norm_value_sq_eq_integral_intervalRepresentativeL hab,
    norm_gradient_sq_eq_integral_deriv_intervalRepresentativeL hab]
  refine (absolutelyContinuousOnInterval_intervalRepresentativeL hab u)
    |>.mul_integral_sq_le_integral_deriv_sq_of_eq_zero_right hab ?_
      (intervalIntegrable_deriv_intervalRepresentativeL_sq hab u)
  rw [projIcc_right]
  rwa [intervalTraceL_apply] at hu

/-! ### Optimality of the constant -/

/-- The class of `sin (π (t - a) / (2 (b - a)))` lies in `H¹_{{a}}(a, b)`, is nonzero, and has
`‖u'‖² = (π / (2 (b - a)))² ‖u‖²`. -/
private theorem exists_mem_singleton_left_norm_gradient_sq_eq (hab : a < b) :
    ∃ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a},
      0 < ‖value u‖ ^ 2 ∧ ‖gradient u‖ ^ 2 = (π / (2 * (b - a))) ^ 2 * ‖value u‖ ^ 2 := by
  obtain ⟨hs, hc⟩ := integral_sin_sq_and_integral_cos_sq_quarter_period hab
  set k := π / (2 * (b - a))
  obtain ⟨u, hrep, hv, hg⟩ := exists_intervalRepresentativeL_eq_of_contDiff (p := 2) hab
    (f := fun t ↦ Real.sin (k * (t - a))) (by fun_prop)
  replace hv := norm_value_sq_eq_intervalIntegral_of_ae_eq hab hv
  replace hg := norm_gradient_sq_eq_intervalIntegral_of_ae_eq hab hg
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_fst_eq_zero (by simp) hab,
      intervalTraceL_apply, hrep ⟨a, left_mem_Icc.2 hab.le⟩]
    simp
  · rw [hv, hs]
    linarith
  · simp_rw [hg, hv, deriv_comp_sub_const (f := fun s ↦ Real.sin (k * s)), deriv_sin_mul,
      mul_pow]
    rw [intervalIntegral.integral_const_mul, hc, hs]

/-- The class of `cos (π (t - a) / (2 (b - a)))` lies in `H¹_{{b}}(a, b)`, is nonzero, and has
`‖u'‖² = (π / (2 (b - a)))² ‖u‖²`. -/
private theorem exists_mem_singleton_right_norm_gradient_sq_eq (hab : a < b) :
    ∃ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {b},
      0 < ‖value u‖ ^ 2 ∧ ‖gradient u‖ ^ 2 = (π / (2 * (b - a))) ^ 2 * ‖value u‖ ^ 2 := by
  obtain ⟨hs, hc⟩ := integral_sin_sq_and_integral_cos_sq_quarter_period hab
  have hkb : π / (2 * (b - a)) * (b - a) = π / 2 := by
    field_simp
  set k := π / (2 * (b - a))
  obtain ⟨u, hrep, hv, hg⟩ := exists_intervalRepresentativeL_eq_of_contDiff (p := 2) hab
    (f := fun t ↦ Real.cos (k * (t - a))) (by fun_prop)
  replace hv := norm_value_sq_eq_intervalIntegral_of_ae_eq hab hv
  replace hg := norm_gradient_sq_eq_intervalIntegral_of_ae_eq hab hg
  refine ⟨u, ?_, ?_, ?_⟩
  · rw [mem_w1pVanishingOnSubmodule_singleton_iff_intervalTraceL_snd_eq_zero (by simp) hab,
      intervalTraceL_apply, hrep ⟨b, right_mem_Icc.2 hab.le⟩]
    simp [hkb]
  · rw [hv, hc]
    linarith
  · simp_rw [hg, hv, deriv_comp_sub_const (f := fun s ↦ Real.cos (k * s)), deriv_cos_mul,
      neg_sq, mul_pow]
    rw [intervalIntegral.integral_const_mul, hc, hs]

/-- **The sharp Poincaré–Friedrichs inequality on `H¹_{{a}}(a, b)`, Rayleigh form.** The best
constant `C` with `C ‖u‖²_{L²} ≤ ‖u'‖²_{L²}` for every `u ∈ H¹(a, b)` vanishing at `a` is
`(π / (2 (b - a)))²`, attained by `sin (π (t - a) / (2 (b - a)))`. -/
theorem isGreatest_mul_norm_value_sq_le_norm_gradient_sq_singleton_left (hab : a < b) :
    IsGreatest {C : ℝ | ∀ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a},
      C * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2} ((π / (2 * (b - a))) ^ 2) := by
  obtain ⟨u, hu, hu0, hgu⟩ := exists_mem_singleton_left_norm_gradient_sq_eq hab
  exact isGreatest_mul_norm_value_sq_le_norm_gradient_sq_of_eq (fun v hv ↦
    mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_fst_eq_zero hab
      (intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab hv)) hu hu0 hgu

/-- **The sharp Poincaré–Friedrichs inequality on `H¹_{{b}}(a, b)`, Rayleigh form.** The best
constant `C` with `C ‖u‖²_{L²} ≤ ‖u'‖²_{L²}` for every `u ∈ H¹(a, b)` vanishing at `b` is
`(π / (2 (b - a)))²`, attained by `cos (π (t - a) / (2 (b - a)))`. -/
theorem isGreatest_mul_norm_value_sq_le_norm_gradient_sq_singleton_right (hab : a < b) :
    IsGreatest {C : ℝ | ∀ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {b},
      C * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2} ((π / (2 * (b - a))) ^ 2) := by
  obtain ⟨u, hu, hu0, hgu⟩ := exists_mem_singleton_right_norm_gradient_sq_eq hab
  exact isGreatest_mul_norm_value_sq_le_norm_gradient_sq_of_eq (fun v hv ↦
    mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_snd_eq_zero hab
      (intervalTraceL_snd_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab hv)) hu hu0 hgu

/-- **The optimal Poincaré–Friedrichs constant of `H¹_{{a}}(a, b)`.** The least `C ≥ 0` with
`‖u‖_{L²} ≤ C ‖u'‖_{L²}` for every `u ∈ H¹(a, b)` vanishing at `a` is `2 (b - a) / π`. -/
theorem isLeast_norm_value_le_mul_norm_gradient_singleton_left (hab : a < b) :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a},
      ‖value u‖ ≤ C * ‖gradient u‖} (2 * (b - a) / π) := by
  obtain ⟨u, hu, hu0, hgu⟩ := exists_mem_singleton_left_norm_gradient_sq_eq hab
  rw [← inv_div]
  exact isLeast_norm_value_le_mul_norm_gradient_of_eq (div_pos Real.pi_pos (by linarith))
    (fun v hv ↦ mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_fst_eq_zero hab
      (intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab hv)) hu hu0 hgu

/-- **The optimal Poincaré–Friedrichs constant of `H¹_{{b}}(a, b)`.** The least `C ≥ 0` with
`‖u‖_{L²} ≤ C ‖u'‖_{L²}` for every `u ∈ H¹(a, b)` vanishing at `b` is `2 (b - a) / π`. -/
theorem isLeast_norm_value_le_mul_norm_gradient_singleton_right (hab : a < b) :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {b},
      ‖value u‖ ≤ C * ‖gradient u‖} (2 * (b - a) / π) := by
  obtain ⟨u, hu, hu0, hgu⟩ := exists_mem_singleton_right_norm_gradient_sq_eq hab
  rw [← inv_div]
  exact isLeast_norm_value_le_mul_norm_gradient_of_eq (div_pos Real.pi_pos (by linarith))
    (fun v hv ↦ mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_snd_eq_zero hab
      (intervalTraceL_snd_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab hv)) hu hu0 hgu

end TauCeti.W1p
