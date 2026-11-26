/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.OneEndpoint
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Deriv
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

/-- If the value of `u ∈ H¹(a, b)` agrees almost everywhere on `(a, b)` with `g`, then its squared
`L²` norm is the integral of `g²` over `(a, b)`. -/
private theorem norm_value_sq_eq_intervalIntegral_of_ae_eq (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} {g : ℝ → ℝ}
    (hg : value u =ᵐ[volume.restrict (Ioo a b)] g) :
    ‖value u‖ ^ 2 = ∫ t in a..b, g t ^ 2 := by
  rw [← integral_value_sq_eq_norm_value_sq, intervalIntegral.integral_of_le hab.le,
    integral_Ioc_eq_integral_Ioo]
  refine integral_congr_ae ?_
  filter_upwards [hg] with t ht
  rw [ht]

/-- If the gradient of `u ∈ H¹(a, b)` agrees almost everywhere on `(a, b)` with `g`, then its
squared `L²` norm is the integral of `g²` over `(a, b)`. -/
private theorem norm_gradient_sq_eq_intervalIntegral_of_ae_eq (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} {g : ℝ → ℝ}
    (hg : gradient u =ᵐ[volume.restrict (Ioo a b)] g) :
    ‖gradient u‖ ^ 2 = ∫ t in a..b, g t ^ 2 := by
  rw [← integral_norm_gradient_sq_eq_norm_gradient_sq, intervalIntegral.integral_of_le hab.le,
    integral_Ioc_eq_integral_Ioo]
  refine integral_congr_ae ?_
  filter_upwards [hg] with t ht
  rw [ht, Real.norm_eq_abs, sq_abs]

/-- The squared `L²` norms of the value and of the gradient of `u ∈ H¹(a, b)` are the integrals of
the squares of its continuous representative and of the derivative of that representative, and
the latter is integrable. -/
private theorem norm_sq_eq_integral_intervalRepresentativeL (hab : a < b)
    (u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2) :
    ‖value u‖ ^ 2 = ∫ t in a..b, intervalRepresentativeL hab u (projIcc a b hab.le t) ^ 2 ∧
      ‖gradient u‖ ^ 2 =
        ∫ t in a..b, deriv (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)) t ^ 2 ∧
      IntervalIntegrable
        (fun t ↦ deriv (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)) t ^ 2)
        volume a b := by
  have hderiv : deriv (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t))
      =ᵐ[volume.restrict (Ioo a b)] gradient u := by
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [ae_hasDerivAt_intervalRepresentativeL hab u] with t ht hmem
    exact (ht (by rw [uIoc_of_le hab.le]; exact Ioo_subset_Ioc_self hmem)).deriv
  have hsq : (fun t ↦ deriv (fun t ↦ intervalRepresentativeL hab u (projIcc a b hab.le t)) t ^ 2)
      =ᵐ[volume.restrict (Ioo a b)] fun t ↦ ‖gradient u t‖ ^ 2 := by
    filter_upwards [hderiv] with t ht
    rw [ht, Real.norm_eq_abs, sq_abs]
  refine ⟨norm_value_sq_eq_intervalIntegral_of_ae_eq hab
    (value_ae_eq_intervalRepresentativeL hab u),
    norm_gradient_sq_eq_intervalIntegral_of_ae_eq hab hderiv.symm, ?_⟩
  refine (intervalIntegrable_iff_integrableOn_Ioo_of_le hab.le).2 ?_
  exact ((Lp.memLp (gradient u)).norm.integrable_sq).congr hsq.symm

/-- **The sharp Poincaré–Friedrichs inequality on an interval, vanishing at `a`.** If the
continuous representative of `u ∈ H¹(a, b)` vanishes at `a`, then
`(π / (2 (b - a)))² ‖u‖²_{L²(a,b)} ≤ ‖u'‖²_{L²(a,b)}`. -/
theorem mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_fst_eq_zero (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} (hu : (intervalTraceL hab u).1 = 0) :
    (π / (2 * (b - a))) ^ 2 * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2 := by
  obtain ⟨hv, hg, hint⟩ := norm_sq_eq_integral_intervalRepresentativeL hab u
  rw [hv, hg]
  refine (absolutelyContinuousOnInterval_intervalRepresentativeL hab u)
    |>.mul_integral_sq_le_integral_deriv_sq_of_eq_zero_left hab ?_ hint
  rw [projIcc_left]
  rwa [intervalTraceL_apply] at hu

/-- **The sharp Poincaré–Friedrichs inequality on an interval, vanishing at `b`.** If the
continuous representative of `u ∈ H¹(a, b)` vanishes at `b`, then
`(π / (2 (b - a)))² ‖u‖²_{L²(a,b)} ≤ ‖u'‖²_{L²(a,b)}`. -/
theorem mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_snd_eq_zero (hab : a < b)
    {u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2} (hu : (intervalTraceL hab u).2 = 0) :
    (π / (2 * (b - a))) ^ 2 * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2 := by
  obtain ⟨hv, hg, hint⟩ := norm_sq_eq_integral_intervalRepresentativeL hab u
  rw [hv, hg]
  refine (absolutelyContinuousOnInterval_intervalRepresentativeL hab u)
    |>.mul_integral_sq_le_integral_deriv_sq_of_eq_zero_right hab ?_ hint
  rw [projIcc_right]
  rwa [intervalTraceL_apply] at hu

/-! ### Optimality of the constant -/

/-- A `C¹` function on `ℝ` represents a class of `H¹(a, b)` with that continuous representative,
whose squared norms are the integrals of the squares of the function and of its derivative. -/
private theorem exists_intervalRepresentativeL_eq_of_contDiff (hab : a < b) {f : ℝ → ℝ}
    (hf : ContDiff ℝ 1 f) :
    ∃ u : W1p volume ⟨Ioo a b, isOpen_Ioo⟩ 2,
      (∀ t : Icc a b, intervalRepresentativeL hab u t = f t) ∧
      ‖value u‖ ^ 2 = ∫ t in a..b, f t ^ 2 ∧ ‖gradient u‖ ^ 2 = ∫ t in a..b, deriv f t ^ 2 := by
  have hdf : MemLp (deriv f) 2 (volume.restrict (Ioo a b)) :=
    (hf.continuous_deriv le_rfl).continuousOn.memLp_restrict_of_subset_isCompact isCompact_Icc
      measurableSet_Ioo Ioo_subset_Icc_self 2
  obtain ⟨u, hv, hg⟩ :=
    (hf.contDiffOn (s := uIcc a b)).absolutelyContinuousOnInterval.exists_w1p_value_gradient_ae_eq
      hdf
  refine ⟨u, fun t ↦ ?_, norm_value_sq_eq_intervalIntegral_of_ae_eq hab hv,
    norm_gradient_sq_eq_intervalIntegral_of_ae_eq hab hg⟩
  have hrep := (intervalRepresentativeL_eq_iff hab u ⟨fun t ↦ f t, by fun_prop⟩).2 (by
    filter_upwards [hv, ae_restrict_mem measurableSet_Ioo] with t ht hmem
    rw [ht, ContinuousMap.coe_mk, projIcc_of_mem hab.le (Ioo_subset_Icc_self hmem)])
  rw [hrep, ContinuousMap.coe_mk]

/-- The squares of `sin` and `cos` of `π (t - a) / (2 (b - a))` both integrate to `(b - a) / 2`
over `(a, b)`. -/
private theorem integral_sin_sq_and_integral_cos_sq (hab : a < b) :
    ∫ t in a..b, Real.sin (π / (2 * (b - a)) * (t - a)) ^ 2 = (b - a) / 2 ∧
      ∫ t in a..b, Real.cos (π / (2 * (b - a)) * (t - a)) ^ 2 = (b - a) / 2 := by
  set k := π / (2 * (b - a)) with hk
  have hk0 : k ≠ 0 := (div_pos Real.pi_pos (by linarith)).ne'
  have hkb : k * b - k * a = π / 2 := by
    rw [hk]
    field_simp
  simp_rw [mul_sub]
  rw [intervalIntegral.integral_comp_mul_sub (fun y ↦ Real.sin y ^ 2) hk0,
    intervalIntegral.integral_comp_mul_sub (fun y ↦ Real.cos y ^ 2) hk0, sub_self, hkb,
    integral_sin_sq, integral_cos_sq]
  constructor <;>
  · simp only [Real.sin_zero, Real.cos_zero, Real.sin_pi_div_two, Real.cos_pi_div_two,
      smul_eq_mul]
    field_simp
    linarith

/-- If `k² ‖u‖² ≤ ‖u'‖²` on a set `S` of Sobolev classes and some `u ∈ S` with `‖u‖ ≠ 0` has
`‖u'‖² = k² ‖u‖²`, then `k²` is the best constant. -/
private theorem isGreatest_of_mem_of_norm_gradient_sq_eq {Ω : Opens ℝ}
    {S : Set (W1p volume Ω 2)} {k : ℝ} (hS : ∀ u ∈ S, k ^ 2 * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2)
    {u : W1p volume Ω 2} (hu : u ∈ S) (hu0 : 0 < ‖value u‖ ^ 2)
    (hgu : ‖gradient u‖ ^ 2 = k ^ 2 * ‖value u‖ ^ 2) :
    IsGreatest {C : ℝ | ∀ u ∈ S, C * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2} (k ^ 2) :=
  ⟨hS, fun _ hC ↦ le_of_mul_le_mul_right ((hC u hu).trans hgu.le) hu0⟩

/-- If `k² ‖u‖² ≤ ‖u'‖²` on a set `S` of Sobolev classes, `k > 0`, and some `u ∈ S` with
`‖u‖ ≠ 0` has `‖u'‖² = k² ‖u‖²`, then `k⁻¹` is the least constant `C` with `‖u‖ ≤ C ‖u'‖` on `S`.
-/
private theorem isLeast_of_mem_of_norm_gradient_sq_eq {Ω : Opens ℝ}
    {S : Set (W1p volume Ω 2)} {k : ℝ} (hk : 0 < k)
    (hS : ∀ u ∈ S, k ^ 2 * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2)
    {u : W1p volume Ω 2} (hu : u ∈ S) (hu0 : 0 < ‖value u‖ ^ 2)
    (hgu : ‖gradient u‖ ^ 2 = k ^ 2 * ‖value u‖ ^ 2) :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ u ∈ S, ‖value u‖ ≤ C * ‖gradient u‖} k⁻¹ := by
  refine ⟨⟨inv_nonneg.2 hk.le, fun v hv ↦ ?_⟩, fun C hC ↦ ?_⟩
  · rw [inv_mul_eq_div, le_div_iff₀ hk]
    have := hS v hv
    nlinarith [norm_nonneg (value v), norm_nonneg (gradient v)]
  · have hg : ‖gradient u‖ = k * ‖value u‖ := by
      rw [← sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hk.le (norm_nonneg _)), hgu, mul_pow]
    have h1 := hC.2 u hu
    rw [hg] at h1
    have hpos : 0 < ‖value u‖ := by nlinarith [norm_nonneg (value u)]
    rw [inv_le_iff_one_le_mul₀ hk]
    nlinarith

/-- The class of `sin (π (t - a) / (2 (b - a)))` lies in `H¹_{{a}}(a, b)`, is nonzero, and has
`‖u'‖² = (π / (2 (b - a)))² ‖u‖²`. -/
private theorem exists_mem_singleton_left_norm_gradient_sq_eq (hab : a < b) :
    ∃ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a},
      0 < ‖value u‖ ^ 2 ∧ ‖gradient u‖ ^ 2 = (π / (2 * (b - a))) ^ 2 * ‖value u‖ ^ 2 := by
  obtain ⟨hs, hc⟩ := integral_sin_sq_and_integral_cos_sq hab
  set k := π / (2 * (b - a))
  obtain ⟨u, hrep, hv, hg⟩ := exists_intervalRepresentativeL_eq_of_contDiff hab
    (f := fun t ↦ Real.sin (k * (t - a))) (by fun_prop)
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
  obtain ⟨hs, hc⟩ := integral_sin_sq_and_integral_cos_sq hab
  have hkb : π / (2 * (b - a)) * (b - a) = π / 2 := by
    field_simp
  set k := π / (2 * (b - a))
  obtain ⟨u, hrep, hv, hg⟩ := exists_intervalRepresentativeL_eq_of_contDiff hab
    (f := fun t ↦ Real.cos (k * (t - a))) (by fun_prop)
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
  exact isGreatest_of_mem_of_norm_gradient_sq_eq (fun v hv ↦
    mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_fst_eq_zero hab
      (intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab hv)) hu hu0 hgu

/-- **The sharp Poincaré–Friedrichs inequality on `H¹_{{b}}(a, b)`, Rayleigh form.** The best
constant `C` with `C ‖u‖²_{L²} ≤ ‖u'‖²_{L²}` for every `u ∈ H¹(a, b)` vanishing at `b` is
`(π / (2 (b - a)))²`, attained by `cos (π (t - a) / (2 (b - a)))`. -/
theorem isGreatest_mul_norm_value_sq_le_norm_gradient_sq_singleton_right (hab : a < b) :
    IsGreatest {C : ℝ | ∀ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {b},
      C * ‖value u‖ ^ 2 ≤ ‖gradient u‖ ^ 2} ((π / (2 * (b - a))) ^ 2) := by
  obtain ⟨u, hu, hu0, hgu⟩ := exists_mem_singleton_right_norm_gradient_sq_eq hab
  exact isGreatest_of_mem_of_norm_gradient_sq_eq (fun v hv ↦
    mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_snd_eq_zero hab
      (intervalTraceL_snd_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab hv)) hu hu0 hgu

/-- **The optimal Poincaré–Friedrichs constant of `H¹_{{a}}(a, b)`.** The least `C ≥ 0` with
`‖u‖_{L²} ≤ C ‖u'‖_{L²}` for every `u ∈ H¹(a, b)` vanishing at `a` is `2 (b - a) / π`. -/
theorem isLeast_norm_value_le_mul_norm_gradient_singleton_left (hab : a < b) :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {a},
      ‖value u‖ ≤ C * ‖gradient u‖} (2 * (b - a) / π) := by
  obtain ⟨u, hu, hu0, hgu⟩ := exists_mem_singleton_left_norm_gradient_sq_eq hab
  rw [← inv_div]
  exact isLeast_of_mem_of_norm_gradient_sq_eq (div_pos Real.pi_pos (by linarith)) (fun v hv ↦
    mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_fst_eq_zero hab
      (intervalTraceL_fst_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab hv)) hu hu0 hgu

/-- **The optimal Poincaré–Friedrichs constant of `H¹_{{b}}(a, b)`.** The least `C ≥ 0` with
`‖u‖_{L²} ≤ C ‖u'‖_{L²}` for every `u ∈ H¹(a, b)` vanishing at `b` is `2 (b - a) / π`. -/
theorem isLeast_norm_value_le_mul_norm_gradient_singleton_right (hab : a < b) :
    IsLeast {C : ℝ | 0 ≤ C ∧ ∀ u ∈ w1pVanishingOnSubmodule volume ⟨Ioo a b, isOpen_Ioo⟩ 2 {b},
      ‖value u‖ ≤ C * ‖gradient u‖} (2 * (b - a) / π) := by
  obtain ⟨u, hu, hu0, hgu⟩ := exists_mem_singleton_right_norm_gradient_sq_eq hab
  rw [← inv_div]
  exact isLeast_of_mem_of_norm_gradient_sq_eq (div_pos Real.pi_pos (by linarith)) (fun v hv ↦
    mul_norm_value_sq_le_norm_gradient_sq_of_intervalTraceL_snd_eq_zero hab
      (intervalTraceL_snd_eq_zero_of_mem_w1pVanishingOnSubmodule_singleton hab hv)) hu hu0 hgu

end TauCeti.W1p
