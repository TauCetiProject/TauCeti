/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.W1p.Interval.AbsolutelyContinuous
public import TauCeti.Analysis.Sobolev.W1p.Interval.Trace
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The parabola `x (1 - x)` on `(0, 1)`: Poincaré and `W^{1,1}_0` constants

The parabola `u(x) = x (1 - x)` vanishes at both ends of `(0, 1)` and has derivative `1 - 2x`, so
for every `1 ≤ p < ∞` it lies in `W^{1,p}_0(0, 1)`
(`TauCeti.Examples.UnitIntervalParabola.exists_mem_w1p0Submodule`). It tests two constants of the
one-dimensional theory.

* **Poincaré.** In `L²`, `‖u‖² = ∫_0^1 x² (1 - x)² = 1/30` and `‖u'‖² = ∫_0^1 (1 - 2x)² = 1/3`, so
  `‖u‖ / ‖u'‖ = 1 / √10` (`TauCeti.Examples.UnitIntervalParabola.sqrt_ten_mul_norm_value_eq`).
  Since `π² < 10`, this ratio is below `1 / π`
  (`TauCeti.Examples.UnitIntervalParabola.pi_mul_norm_value_lt`), the optimal constant of the
  Poincaré inequality `‖v‖ ≤ C ‖v'‖` on `H¹₀(0, 1)`
  (`TauCeti.W1p.norm_value_le_div_pi_mul_norm_gradient_of_mem_w1p0Submodule`), whose extremal is
  `sin (π x)`. The width `1` of the interval, the constant of the one-endpoint Poincaré inequality
  `TauCeti.W1p.norm_value_le_mul_norm_gradient_of_intervalTraceL_fst_eq_zero` (left endpoint value
  zero), is finite but not sharp.
* **`W^{1,1}_0` in `L^∞`.** A class of `W^{1,1}_0(0, 1)` satisfies `|u(t)| ≤ ‖u'‖_{L¹} / 2`
  (`TauCeti.W1p.abs_intervalRepresentativeL_le_of_intervalTraceL_eq_zero`). For the parabola
  `‖u'‖_{L¹} = ∫_0^1 |1 - 2x| = 1/2` and `u(1/2) = 1/4`, so the bound is an equality at the
  midpoint, and `1/2` is the least constant
  (`isLeast_abs_intervalRepresentativeL_le_mul_norm_gradient`, in the namespace of this file).
  In particular `‖u‖_∞ = 1/4 ≤ ‖u'‖_{L¹} = 1/2`.

## References

* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*,
  Theorem 8.8 and Proposition 8.13.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.Examples.UnitIntervalParabola

open W1p

/-- The parabola has derivative `1 - 2x`. -/
private theorem hasDerivAt_parabola (x : ℝ) :
    HasDerivAt (fun x : ℝ => x * (1 - x)) (1 - 2 * x) x := by
  exact ((hasDerivAt_id' x).mul ((hasDerivAt_id' x).const_sub 1)).congr_deriv (by ring)

/-- `x (1 - x)` is the continuous representative of a class of `W^{1,p}(0, 1)`, whose value is
`x (1 - x)` and whose weak gradient is `1 - 2x` almost everywhere, for every `1 ≤ p ≤ ∞`. -/
theorem exists_intervalRepresentativeL_eq (p : ℝ≥0∞) [Fact (1 ≤ p)] :
    ∃ u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p,
      (∀ t : Icc (0 : ℝ) 1, intervalRepresentativeL zero_lt_one u t = t * (1 - t)) ∧
      value u =ᵐ[volume.restrict (Ioo 0 1)] (fun x => x * (1 - x)) ∧
      gradient u =ᵐ[volume.restrict (Ioo 0 1)] fun x => 1 - 2 * x := by
  obtain ⟨u, hrep, hv, hg⟩ := exists_intervalRepresentativeL_eq_of_contDiff (p := p) zero_lt_one
    (f := fun x : ℝ => x * (1 - x)) (by fun_prop)
  refine ⟨u, hrep, hv, hg.trans (Filter.Eventually.of_forall fun x => ?_)⟩
  exact (hasDerivAt_parabola x).deriv

/-- A class of `W^{1,p}(0, 1)` with value `x (1 - x)` has weak gradient `1 - 2x`. -/
private theorem gradient_ae_eq {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p}
    (hv : value u =ᵐ[volume.restrict (Ioo 0 1)] (fun x => x * (1 - x))) :
    gradient u =ᵐ[volume.restrict (Ioo 0 1)] fun x => 1 - 2 * x := by
  obtain ⟨w, -, hw, hg⟩ := exists_intervalRepresentativeL_eq p
  rwa [W1p.ext_value (Lp.ext (hv.trans hw.symm))]

/-- The endpoint values of a class represented by `x (1 - x)` vanish. -/
private theorem intervalTraceL_eq_zero {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p}
    (hrep : ∀ t : Icc (0 : ℝ) 1, intervalRepresentativeL zero_lt_one u t = t * (1 - t)) :
    intervalTraceL zero_lt_one u = 0 := by
  rw [intervalTraceL_apply, hrep, hrep]
  simp

/-- For `1 ≤ p < ∞`, the parabola `x (1 - x)` lies in `W^{1,p}_0(0, 1)`. -/
theorem exists_mem_w1p0Submodule {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ∃ u ∈ w1p0Submodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ p,
      value u =ᵐ[volume.restrict (Ioo 0 1)] (fun x => x * (1 - x)) ∧
      gradient u =ᵐ[volume.restrict (Ioo 0 1)] fun x => 1 - 2 * x := by
  obtain ⟨u, hrep, hv, hg⟩ := exists_intervalRepresentativeL_eq p
  exact ⟨u, (mem_w1p0Submodule_iff_intervalTraceL_eq_zero hp zero_lt_one u).2
    (intervalTraceL_eq_zero hrep), hv, hg⟩

/-! ### The Poincaré ratio -/

/-- `∫_0^1 x² (1 - x)² = 1/30`. -/
private theorem integral_parabola_sq : ∫ x in (0 : ℝ)..1, (x * (1 - x)) ^ 2 = 1 / 30 := by
  have h : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x ^ 3 / 3 - x ^ 4 / 2 + x ^ 5 / 5)
      ((x * (1 - x)) ^ 2) x := fun x _ => by
    refine ((((hasDerivAt_pow 3 x).div_const 3).sub ((hasDerivAt_pow 4 x).div_const 2)).add
      ((hasDerivAt_pow 5 x).div_const 5)).congr_deriv ?_
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num

/-- `∫_0^1 (1 - 2x)² = 1/3`. -/
private theorem integral_one_sub_two_mul_sq : ∫ x in (0 : ℝ)..1, (1 - 2 * x) ^ 2 = 1 / 3 := by
  have h : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun x : ℝ => x - 2 * x ^ 2 + 4 * x ^ 3 / 3)
      ((1 - 2 * x) ^ 2) x := fun x _ => by
    refine (((hasDerivAt_id' x).sub ((hasDerivAt_pow 2 x).const_mul 2)).add
      (((hasDerivAt_pow 3 x).const_mul 4).div_const 3)).congr_deriv ?_
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt h
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  norm_num

/-- In `H¹(0, 1)`, a class with value `x (1 - x)`, hence with weak gradient `1 - 2x`, has
`‖u‖² = 1/30` and `‖u'‖² = 1/3`. -/
theorem norm_value_sq_eq_and_norm_gradient_sq_eq
    {u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2}
    (hv : value u =ᵐ[volume.restrict (Ioo 0 1)] (fun x => x * (1 - x))) :
    ‖value u‖ ^ 2 = 1 / 30 ∧ ‖gradient u‖ ^ 2 = 1 / 3 :=
  ⟨(norm_value_sq_eq_intervalIntegral_of_ae_eq zero_lt_one hv).trans integral_parabola_sq,
    (norm_gradient_sq_eq_intervalIntegral_of_ae_eq zero_lt_one (gradient_ae_eq hv)).trans
      integral_one_sub_two_mul_sq⟩

/-- **The Poincaré ratio of the parabola.** In `H¹(0, 1)`, a class with value `x (1 - x)` has
`√10 ‖u‖ = ‖u'‖`. -/
theorem sqrt_ten_mul_norm_value_eq {u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2}
    (hv : value u =ᵐ[volume.restrict (Ioo 0 1)] (fun x => x * (1 - x))) :
    √10 * ‖value u‖ = ‖gradient u‖ := by
  obtain ⟨h₁, h₂⟩ := norm_value_sq_eq_and_norm_gradient_sq_eq hv
  rw [← Real.sqrt_sq (norm_nonneg (value u)), ← Real.sqrt_sq (norm_nonneg (gradient u)), h₁, h₂,
    ← Real.sqrt_mul (by norm_num)]
  norm_num

/-- **The parabola is not extremal for Poincaré.** In `H¹(0, 1)`, a class with value
`x (1 - x)` has `π ‖u‖ < ‖u'‖`: its ratio `1 / √10` is below the optimal constant `1 / π` of the
Poincaré inequality on `H¹₀(0, 1)`. -/
theorem pi_mul_norm_value_lt {u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 2}
    (hv : value u =ᵐ[volume.restrict (Ioo 0 1)] (fun x => x * (1 - x))) :
    Real.pi * ‖value u‖ < ‖gradient u‖ := by
  rw [← sqrt_ten_mul_norm_value_eq hv]
  have hu : 0 < ‖value u‖ := by
    have h := (norm_value_sq_eq_and_norm_gradient_sq_eq hv).1
    exact (norm_nonneg _).lt_of_ne fun h0 => by rw [← h0] at h; norm_num at h
  refine mul_lt_mul_of_pos_right ?_ hu
  rw [← Real.sqrt_sq Real.pi_pos.le]
  refine Real.sqrt_lt_sqrt (sq_nonneg _) ?_
  nlinarith [Real.pi_lt_d2, Real.pi_pos]

/-! ### The constant of `W^{1,1}_0` in `L^∞` -/

/-- `∫_0^1 |1 - 2x| = 1/2`. -/
private theorem integral_abs_one_sub_two_mul :
    ∫ x in Ioo (0 : ℝ) 1, |1 - 2 * x| = 1 / 2 := by
  have hc : Continuous fun x : ℝ => |1 - 2 * x| := by fun_prop
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => x - x ^ 2) (1 - 2 * x) x := fun x => by
    refine ((hasDerivAt_id' x).sub (hasDerivAt_pow 2 x)).congr_deriv ?_
    norm_num
  -- On `[0, 1/2]` the integrand is `1 - 2x`, on `[1/2, 1]` it is `2x - 1`.
  have h₁ : ∫ x in (0 : ℝ)..1 / 2, |1 - 2 * x| = 1 / 4 := by
    rw [intervalIntegral.integral_congr (g := fun x => 1 - 2 * x) fun x hx => by
        rw [uIcc_of_le (by norm_num)] at hx
        exact abs_of_nonneg (by linarith [hx.2]),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
        (Continuous.intervalIntegrable (by fun_prop) _ _)]
    norm_num
  have h₂ : ∫ x in (1 / 2 : ℝ)..1, |1 - 2 * x| = 1 / 4 := by
    rw [intervalIntegral.integral_congr (g := fun x => -(1 - 2 * x)) fun x hx => by
        rw [uIcc_of_le (by norm_num)] at hx
        exact abs_of_nonpos (by linarith [hx.1]),
      intervalIntegral.integral_neg, intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun x _ => hF x) (Continuous.intervalIntegrable (by fun_prop) _ _)]
    norm_num
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le zero_le_one,
    ← intervalIntegral.integral_add_adjacent_intervals (b := 1 / 2)
      (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), h₁, h₂]
  norm_num

/-- In `W^{1,1}(0, 1)` the norm of the weak gradient is the integral of its absolute value. -/
private theorem norm_gradient_eq_setIntegral_abs (u : W1p volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 1) :
    ‖gradient u‖ = ∫ s in Ioo (0 : ℝ) 1, |gradient u s| := by
  simp only [L1.norm_eq_integral_norm, Real.norm_eq_abs, TopologicalSpace.Opens.coe_mk]

/-- **The sharp constant of `W^{1,1}_0(0, 1)` in `L^∞`.** The least `C` with
`|u(t)| ≤ C ‖u'‖_{L¹(0,1)}` for every `u ∈ W^{1,1}_0(0, 1)` and every `t ∈ [0, 1]` is `1/2`. The
bound holds by `TauCeti.W1p.abs_intervalRepresentativeL_le_of_intervalTraceL_eq_zero`, and the
parabola `x (1 - x)`, with `u(1/2) = 1/4` and `‖u'‖_{L¹} = 1/2`, attains it. -/
theorem isLeast_abs_intervalRepresentativeL_le_mul_norm_gradient :
    IsLeast {C : ℝ | ∀ u ∈ w1p0Submodule volume ⟨Ioo (0 : ℝ) 1, isOpen_Ioo⟩ 1,
      ∀ t : Icc (0 : ℝ) 1, |intervalRepresentativeL zero_lt_one u t| ≤ C * ‖gradient u‖}
      (1 / 2) := by
  refine ⟨fun u hu t => ?_, fun C hC => ?_⟩
  · rw [norm_gradient_eq_setIntegral_abs, one_div_mul_eq_div]
    exact abs_intervalRepresentativeL_le_of_intervalTraceL_eq_zero zero_lt_one
      (intervalTraceL_eq_zero_of_mem_w1p0Submodule zero_lt_one hu) t
  · obtain ⟨u, hrep, -, hg⟩ := exists_intervalRepresentativeL_eq 1
    have hgrad : ‖gradient u‖ = 1 / 2 := by
      rw [norm_gradient_eq_setIntegral_abs, ← integral_abs_one_sub_two_mul]
      exact integral_congr_ae (hg.mono fun x hx => by simp only [hx])
    have h := hC u ((mem_w1p0Submodule_iff_intervalTraceL_eq_zero ENNReal.one_ne_top zero_lt_one
      u).2 (intervalTraceL_eq_zero hrep)) ⟨1 / 2, by norm_num, by norm_num⟩
    rw [hrep, hgrad] at h
    norm_num [abs_of_pos] at h
    linarith

end TauCeti.Examples.UnitIntervalParabola
