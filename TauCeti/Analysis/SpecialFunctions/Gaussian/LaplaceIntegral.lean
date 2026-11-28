/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.Analysis.RCLike.Basic
import TauCeti.Analysis.SpecialFunctions.Gaussian.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.Integral.Exp.Decay

/-!
# Half-line Gaussian–Laplace integrals

This file develops integrability, vertical-strip norm bounds, positive scaling, and complex
differentiation with respect to the Mellin exponent (see
`TauCeti.MeasureTheory.Integral.Exp.PowerDecay` for differentiation in the Laplace parameter) for
half-line integrals of the form

  `∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)`

with complex quadratic rate `b : ℂ` (`0 < b.re`), Mellin exponent `s : ℂ`, and linear Laplace
parameter `z : ℂ`, alongside real majorants for `b ≥ 0`. Completing the square on
`-b.re u² - z.re u` absorbs the linear term into half the Gaussian weight, so the integral
converges on `(0, ∞)` whenever `0 < b.re` and `0 < s.re` for every `z : ℂ`, and defines a
holomorphic function of `s` on the open right half-plane `{s : ℂ | 0 < s.re}` whose derivative
inserts `Complex.log u` into the integrand.

At `b = 1 / 2` and `s = a + 1 / 2`, this integral is the half-line Laplace kernel of Weber's
parabolic cylinder function `U(a, z)` (DLMF 12.5.1), providing the termwise shifted integrals,
vertical-strip bounds, and Mellin-parameter holomorphy of the Laplace–Hermite rotational series.

## Main results

* `TauCeti.integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_pos`,
  `TauCeti.integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_nonneg`: tail integrability on
  `(a, ∞)` (`0 < a`) for `0 < b` with arbitrary `(s, c)` and for `0 ≤ b` when `0 < c` or
  `0 ≤ c ∧ s < -1`.
* `TauCeti.integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_of_pos`: complex integrability on
  `(a, ∞)` (`0 < a`) for `0 < b.re` and any `s`.
* `TauCeti.norm_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_le_add`: vertical-strip norm bound
  on `σ₁ ≤ s.re ≤ σ₂` (`0 < σ₁`) by the sum of the two real endpoint integrals.
* `TauCeti.integral_cpow_mul_cexp_neg_mul_sq_mul_sq_sub_mul_Ioi_eq_cpow_mul_integral`: positive
  scaling `v = c u` (`0 < c`) pulls out `(c : ℂ) ^ (-s)` and replaces `(b c², z)` by `(b, z / c)`.
* `TauCeti.hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left`,
  `TauCeti.differentiableOn_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi`: derivative and
  holomorphy in `s` on `{s : ℂ | 0 < s.re}` for `0 < b.re` and any `z : ℂ`.

## References

* *NIST Digital Library of Mathematical Functions*, [§12.5(i)](https://dlmf.nist.gov/12.5.i).
-/

public section

open Complex Filter MeasureTheory Real Set
open scoped Topology

namespace TauCeti

/-- On `(0, ∞)`, `u ↦ u ^ s * exp (-b u² - c u)` is integrable whenever `0 < b` and `-1 < s`. -/
private theorem integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi {b s : ℝ} (hb : 0 < b)
    (hs : -1 < s) (c : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ s * rexp (-b * u ^ 2 - c * u)) (Ioi 0) := by
  refine (integrableOn_rpow_mul_exp_mul_sub_mul_pow (n := 2) (by norm_num) hs hb (-c)).congr_fun
    (fun u _ => ?_) measurableSet_Ioi
  dsimp only
  ring_nf

/-- For `0 < a` and `0 < b`, `u ↦ u ^ s * exp (-b u² - c u)` is integrable on `(a, ∞)` for every
real exponent `s` and linear parameter `c`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_pos {a b : ℝ} (ha : 0 < a)
    (hb : 0 < b) (s c : ℝ) :
    IntegrableOn (fun u : ℝ => u ^ s * rexp (-b * u ^ 2 - c * u)) (Ioi a) := by
  set m := max s 0
  have hm : -1 < m := lt_of_lt_of_le neg_one_lt_zero (le_max_right s 0)
  have hmaj : IntegrableOn
      (fun u : ℝ => a ^ (s - m) * (u ^ m * rexp (-b * u ^ 2 - c * u))) (Ioi a) :=
    ((integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi hb hm c).mono_set
      (Ioi_subset_Ioi ha.le)).const_mul _
  refine hmaj.mono'
    (by fun_prop : Measurable fun u : ℝ => u ^ s * rexp (-b * u ^ 2 - c * u)).aestronglyMeasurable
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : a < u)
  have hu0 : 0 < u := ha.trans hu
  rw [Real.norm_of_nonneg (by positivity)]
  calc u ^ s * rexp (-b * u ^ 2 - c * u)
      ≤ (a ^ (s - m) * u ^ m) * rexp (-b * u ^ 2 - c * u) :=
        mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_sub_mul_rpow hu0
            (Real.rpow_le_rpow_of_nonpos ha hu.le (sub_nonpos.2 (le_max_left s 0))))
          (Real.exp_pos _).le
    _ = a ^ (s - m) * (u ^ m * rexp (-b * u ^ 2 - c * u)) := by ring

/-- For `0 < a` and `0 ≤ b`, `u ↦ u ^ s * exp (-b u² - c u)` is integrable on `(a, ∞)` whenever
`0 < c`, or `0 ≤ c` and `s < -1`. -/
theorem integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_nonneg {a b s c : ℝ} (ha : 0 < a)
    (hb : 0 ≤ b) (hc : 0 < c ∨ (0 ≤ c ∧ s < -1)) :
    IntegrableOn (fun u : ℝ => u ^ s * rexp (-b * u ^ 2 - c * u)) (Ioi a) := by
  refine (integrableOn_rpow_mul_exp_neg_mul_Ioi_of_pos ha hc).mono'
    (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : a < u)
  have hu0 : 0 < u := ha.trans hu
  rw [Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by nlinarith [sq_nonneg u])) (by positivity)

/-- For `0 < u` and any `b s z : ℂ`, the norm of
`(u : ℂ) ^ s * cexp (-b * (u : ℂ) ^ 2 - z * u)` is
`u ^ s.re * exp (-b.re * u ^ 2 - z.re * u)`. -/
private theorem norm_cpow_mul_cexp_neg_mul_sq_sub_mul (b s z : ℂ) {u : ℝ} (hu : 0 < u) :
    ‖(u : ℂ) ^ s * cexp (-b * (u : ℂ) ^ 2 - z * u)‖ =
      u ^ s.re * rexp (-b.re * u ^ 2 - z.re * u) := by
  have hnorm := Nat.norm_cpow_mul_cexp_mul_sub_mul_pow 2 b s (-z) hu
  have h1 : -b * (u : ℂ) ^ 2 - z * u = -z * u - b * (u : ℂ) ^ 2 := by ring
  have h2 : (-z).re * u - b.re * u ^ 2 = -b.re * u ^ 2 - z.re * u := by
    rw [Complex.neg_re]; ring
  rw [h1, hnorm, h2]

/-- For `0 < a` and `0 < b.re`, `u ↦ (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)` is
integrable on `(a, ∞)` for every `s z : ℂ`. -/
theorem integrableOn_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_of_pos {a : ℝ} {b : ℂ} (ha : 0 < a)
    (hb : 0 < b.re) (s z : ℂ) :
    IntegrableOn (fun u : ℝ => (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u))
      (Ioi a) := by
  have hmaj := integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi_of_pos ha hb (s.re - 1) z.re
  refine hmaj.mono' (Measurable.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : a < u)
  rw [norm_cpow_mul_cexp_neg_mul_sq_sub_mul b (s - 1) z (ha.trans hu)]
  simp

/-- On any vertical strip `σ₁ ≤ s.re ≤ σ₂` (`0 < σ₁`, `0 < b.re`), the norm of the complex
Gaussian–Laplace integral is bounded by the sum of the two real endpoint integrals at `σ₁` and
`σ₂`. -/
theorem norm_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_le_add {b s : ℂ} {σ₁ σ₂ : ℝ}
    (hb : 0 < b.re) (hσ₁ : 0 < σ₁) (hlo : σ₁ ≤ s.re) (hhi : s.re ≤ σ₂) (z : ℂ) :
    ‖∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)‖ ≤
      (∫ u in Ioi (0 : ℝ), u ^ (σ₁ - 1) * rexp (-b.re * u ^ 2 - z.re * u)) +
        ∫ u in Ioi (0 : ℝ), u ^ (σ₂ - 1) * rexp (-b.re * u ^ 2 - z.re * u) := by
  have hint₁ := integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi hb (by linarith : -1 < σ₁ - 1) z.re
  have hint₂ := integrableOn_rpow_mul_exp_neg_mul_sq_sub_mul_Ioi hb
    (by linarith : -1 < σ₂ - 1) z.re
  rw [← integral_add hint₁ hint₂]
  refine norm_integral_le_of_norm_le (hint₁.add hint₂) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u (hu : 0 < u)
  rw [norm_cpow_mul_cexp_neg_mul_sq_sub_mul b (s - 1) z hu, Complex.sub_re, Complex.one_re,
    ← add_mul]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow_add_rpow_of_mem_Icc hu ⟨by linarith, by linarith⟩) (Real.exp_pos _).le

/-- Positive rescaling `v = c * u` (`0 < c`) in the half-line Gaussian–Laplace integral: for every
`b s z : ℂ`, `∫_{u > 0} u^{s - 1} exp (-(b c²) u² - z u) du` equals
`c^{-s} ∫_{v > 0} v^{s - 1} exp (-b v² - (z / c) v) dv`. -/
theorem integral_cpow_mul_cexp_neg_mul_sq_mul_sq_sub_mul_Ioi_eq_cpow_mul_integral {c : ℝ}
    (hc : 0 < c) (b s z : ℂ) :
    (∫ u in Ioi (0 : ℝ),
        (u : ℂ) ^ (s - 1) * cexp (-(b * (c : ℂ) ^ 2) * (u : ℂ) ^ 2 - z * u)) =
      (c : ℂ) ^ (-s) * ∫ v in Ioi (0 : ℝ),
        (v : ℂ) ^ (s - 1) * cexp (-b * (v : ℂ) ^ 2 - (z / c) * v) := by
  have hc0 : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hm := mellin_comp_mul_left
    (fun v : ℝ => cexp (-b * (v : ℂ) ^ 2 - (z / c) * v)) s hc
  simp only [mellin, smul_eq_mul] at hm
  rw [← hm]
  refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
  congr 2
  push_cast
  field_simp

/-- For `0 < b.re`, `0 < s₀.re`, and any `z : ℂ`, differentiating the Gaussian–Laplace integral
with respect to the Mellin exponent `s` at `s₀` inserts a factor `Complex.log u` into the
integrand. -/
theorem hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left {b s₀ : ℂ} (hb : 0 < b.re)
    (hs₀ : 0 < s₀.re) (z : ℂ) :
    HasDerivAt
      (fun s : ℂ =>
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u))
      (∫ u in Ioi (0 : ℝ),
        Complex.log u * (u : ℂ) ^ (s₀ - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)) s₀ := by
  let f : ℝ → ℂ := fun u => cexp (-b * (u : ℂ) ^ 2 - z * u)
  have hf_cont : Continuous f := by fun_prop
  have hf_loc : LocallyIntegrableOn f (Ioi 0) :=
    hf_cont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hf_top : f =O[atTop] fun u : ℝ => rexp (-(b.re / 2) * u) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨rexp (z.re ^ 2 / (2 * b.re)), ?_⟩
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with u (hu : 1 ≤ u)
    have hu_sq : u ≤ u ^ 2 := by nlinarith
    have hnorm := norm_cpow_mul_cexp_neg_mul_sq_sub_mul b 0 z (zero_lt_one.trans_le hu)
    simp only [Complex.cpow_zero, one_mul, Complex.zero_re, Real.rpow_zero] at hnorm
    dsimp only [f]
    rw [hnorm, Real.norm_of_nonneg (Real.exp_pos _).le]
    refine (exp_neg_mul_sq_sub_mul_le hb z.re u).trans ?_
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith)) (Real.exp_pos _).le
  have hf_rpow : f =O[atTop] fun u : ℝ => u ^ (-(s₀.re + 1)) :=
    hf_top.trans (isLittleO_exp_neg_mul_rpow_atTop (half_pos hb) _).isBigO
  have hf_bot : f =O[𝓝[>] 0] fun u : ℝ => u ^ (-(0 : ℝ)) := by
    simp_rw [neg_zero, Real.rpow_zero]
    exact Asymptotics.isBigO_const_of_tendsto hf_cont.continuousWithinAt one_ne_zero
  have hm := (mellin_hasDerivAt_of_isBigO_rpow hf_loc hf_rpow (lt_add_one s₀.re) hf_bot hs₀).2
  simp only [mellin, smul_eq_mul] at hm
  refine hm.congr_deriv (setIntegral_congr_fun measurableSet_Ioi fun u (hu : 0 < u) => ?_)
  rw [Complex.real_smul, Complex.ofReal_log hu.le]
  ring

/-- For `0 < b.re` and any `z : ℂ`, the Mellin parameter map
`s ↦ ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u)` is holomorphic
on the open right half-plane `{s : ℂ | 0 < s.re}`. -/
theorem differentiableOn_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi {b : ℂ} (hb : 0 < b.re)
    (z : ℂ) :
    DifferentiableOn ℂ
      (fun s : ℂ =>
        ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (s - 1) * cexp (-b * (u : ℂ) ^ 2 - z * u))
      {s : ℂ | 0 < s.re} :=
  fun _ hs =>
    (hasDerivAt_integral_cpow_mul_cexp_neg_mul_sq_sub_mul_Ioi_left hb hs z).differentiableAt
      |>.differentiableWithinAt

end TauCeti
