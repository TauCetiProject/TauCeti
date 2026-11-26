/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
public import TauCeti.RingTheory.Polynomial.SecondOrderEulerian

import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.RingTheory.Polynomial.Tower
import Mathlib.Topology.Algebra.Polynomial
import TauCeti.Analysis.SpecialFunctions.Gamma.Stirling.Remainder
import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.OfReal
import TauCeti.Analysis.SpecialFunctions.Integrability.Cpow
import TauCeti.Analysis.SpecialFunctions.Pow.Sector

/-!
# Fixed-ratio large-parameter asymptotics of the lower incomplete Gamma function

For a fixed ratio `0 < r < 1` and large shape parameter `a` in a closed sector
`|arg a| ≤ π / 2 - δ` (`δ > 0`), the lower incomplete Gamma function `γ(a, r a)` satisfies the
asymptotic expansion (DLMF 8.11.6)
`(a - r a) (r a)^{-a} e^{r a} γ(a, r a) ~ ∑_{k ≥ 0} (-1)^k b_k(r) / ((1 - r)^{2k} a^k)`,
where `b_k = TauCeti.secondOrderEulerianPolynomial k` is the second-order Eulerian polynomial
sequence of DLMF 8.11.8–8.11.9 (`TauCeti/RingTheory/Polynomial/SecondOrderEulerian.lean`).

This module provides:

* exact `n`-term expansions with explicit integral remainder on the open right half-plane
  `0 < Re a` for `r < 1`, `r ≠ 0`;
* explicit right-half-plane and sectorial remainder bounds for `0 < r < 1`, giving the `O(‖a‖^{-n})`
  asymptotic expansion (DLMF 8.11.6) in both standard normalizations and leading sectorial
  asymptotic equivalences for `γ(a, r a)` and `P(a, r a)`;
* positive real-axis enveloping bounds (the `n`-th remainder multiplied by `(-1)^n` is nonnegative
  and at most the first neglected term), two-sided `γ(a, r a)` bounds, real asymptotic expansions
  and equivalences, and tail decay `P(a, r a) → 0` for every `r < 1`.

## Main results

* `Complex.mul_lowerIncompleteGamma_mul_eq_integral`,
  `Complex.mul_lowerIncompleteGamma_mul_eq_sum_add_integral`: exact integral representation and
  `n`-term expansion with integral remainder for `(r a)^{-a} e^{r a} γ(a, r a)` on `0 < Re a`.
* `Complex.norm_mul_lowerIncompleteGamma_fixedRatio_sub_sum_le`,
  `Complex.norm_mul_lowerIncompleteGamma_fixedRatio_sub_sum_le_of_abs_arg_le`: explicit remainder
  bounds on `0 < Re a` and on the closed sector `|arg a| ≤ π / 2 - δ`.
* `Complex.isBigO_sub_mul_lowerIncompleteGamma_fixedRatio`,
  `Complex.isBigO_cpow_one_sub_mul_lowerIncompleteGamma_fixedRatio`: DLMF 8.11.6 to arbitrary
  order `n` in the scale `(‖a‖ ^ n)⁻¹` along
  `Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ π / 2 - δ}`.
* `Complex.lowerIncompleteGamma_fixedRatio_isEquivalent`,
  `Complex.regularizedGamma_fixedRatio_isEquivalent`: leading sectorial asymptotic equivalences
  for `γ(a, r a)` and `P(a, r a)`.
* `TauCeti.neg_one_pow_mul_mul_lowerIncompleteGamma_fixedRatio_sub_sum_nonneg`,
  `TauCeti.neg_one_pow_mul_mul_lowerIncompleteGamma_fixedRatio_sub_sum_le`,
  `TauCeti.lowerIncompleteGamma_fixedRatio_bounds`,
  `TauCeti.isBigO_sub_mul_lowerIncompleteGamma_fixedRatio`,
  `TauCeti.lowerIncompleteGamma_fixedRatio_isEquivalent`,
  `TauCeti.regularizedGamma_fixedRatio_isEquivalent`,
  `TauCeti.tendsto_regularizedGamma_fixedRatio_atTop`: enveloping inequalities, two-sided bounds,
  asymptotic expansions, and tail decay along the positive real axis.

## References

* *NIST Digital Library of Mathematical Functions*, [§8.11(ii)](https://dlmf.nist.gov/8.11#ii),
  Eqs. 8.11.6, 8.11.8, and 8.11.9.
* F. G. Tricomi, *Asymptotische Eigenschaften der unvollständigen Gammafunktion*,
  Math. Z. **53** (1950), 136–148.
* N. M. Temme, *Special Functions: An Introduction to the Classical Functions of Mathematical
  Physics*, Wiley, 1996, §11.2.1.
-/

public section

noncomputable section

open Asymptotics Bornology Filter Finset MeasureTheory Polynomial Set
open scoped Interval Nat Topology

namespace TauCeti

/-! ### Differential recurrence of the rational fixed-ratio amplitudes -/

/-- Differentiating `(-1)^k b_k(t) / (1 - t)^{2k + 1}` away from `t = 1`. -/
theorem hasDerivAt_secondOrderEulerianPolynomial_div (k : ℕ) {t : ℝ} (ht : t ≠ 1) :
    HasDerivAt
      (fun y : ℝ =>
        (-1 : ℝ) ^ k * aeval y (secondOrderEulerianPolynomial k) / (1 - y) ^ (2 * k + 1))
      ((-1 : ℝ) ^ k *
        ((1 - t) * aeval t (secondOrderEulerianPolynomial k).derivative +
          (2 * (k : ℝ) + 1) * aeval t (secondOrderEulerianPolynomial k)) /
        (1 - t) ^ (2 * k + 2)) t := by
  have h1t : 1 - t ≠ 0 := sub_ne_zero.mpr ht.symm
  have hd := (((secondOrderEulerianPolynomial k).hasDerivAt_aeval t).const_mul ((-1 : ℝ) ^ k)).div
    (((hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)).pow (2 * k + 1))
    (pow_ne_zero _ h1t)
  refine hd.congr_deriv ?_
  dsimp only [id_eq, Pi.sub_apply, Pi.pow_apply]
  have hpow : ((1 - t) ^ (2 * k + 1)) ^ 2 = (1 - t) ^ (2 * k) * (1 - t) ^ (2 * k + 2) := by
    rw [← pow_mul, ← pow_add]
    congr 1
    omega
  rw [Nat.add_sub_cancel, hpow]
  push_cast
  field_simp [h1t]
  ring

/-- Applying `-t d/dt` to `(-1)^k b_k(t) / (1 - t)^{2k + 1}` produces
`(-1)^{k+1} b_{k+1}(t) / (1 - t)^{2k + 2}`. -/
theorem neg_mul_deriv_secondOrderEulerianPolynomial_div (k : ℕ) (t : ℝ) :
    -t * ((-1 : ℝ) ^ k *
        ((1 - t) * aeval t (secondOrderEulerianPolynomial k).derivative +
          (2 * (k : ℝ) + 1) * aeval t (secondOrderEulerianPolynomial k)) /
        (1 - t) ^ (2 * k + 2)) =
      (-1 : ℝ) ^ (k + 1) * aeval t (secondOrderEulerianPolynomial (k + 1)) /
        (1 - t) ^ (2 * k + 2) := by
  have hpoly : aeval t (secondOrderEulerianPolynomial (k + 1)) =
      t * ((1 - t) * aeval t (secondOrderEulerianPolynomial k).derivative +
        (2 * (k : ℝ) + 1) * aeval t (secondOrderEulerianPolynomial k)) := by
    rw [secondOrderEulerianPolynomial_succ]
    simp only [map_add, map_mul, map_sub, map_one, map_ofNat, map_natCast, aeval_X]
    ring
  rw [hpoly, pow_succ (-1 : ℝ)]
  ring

end TauCeti

namespace Complex

/-! ### Exact integration-by-parts expansion on the open right half-plane -/

private theorem one_sub_mul_pos {r x : ℝ} (hr1 : r < 1) (hx : x ∈ Icc (0 : ℝ) 1) :
    0 < 1 - r * (1 - x) := by
  rcases eq_or_lt_of_le hx.2 with rfl | hxlt
  · norm_num
  · linarith [hx.1, mul_pos (sub_pos.mpr hr1) (sub_pos.mpr hxlt)]

private theorem one_sub_ofReal_ne_zero {r : ℝ} (hr1 : r < 1) : 1 - (r : ℂ) ≠ 0 :=
  sub_ne_zero.mpr (ofReal_inj.not.mpr hr1.ne')

private theorem ofReal_aeval (p : ℤ[X]) (r : ℝ) :
    (aeval r p : ℂ) = aeval (r : ℂ) p := by
  rw [← coe_algebraMap, Polynomial.aeval_algebraMap_apply, coe_algebraMap]

private theorem ofReal_sum_secondOrderEulerianPolynomial_div (r a : ℝ) (n : ℕ)
    (e₁ e₂ : ℕ → ℕ) :
    ((∑ k ∈ Finset.range n,
        (-1 : ℝ) ^ k * aeval r (TauCeti.secondOrderEulerianPolynomial k) /
          ((1 - r) ^ e₁ k * a ^ e₂ k) : ℝ) : ℂ) =
      ∑ k ∈ Finset.range n,
        (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.secondOrderEulerianPolynomial k) /
          ((1 - (r : ℂ)) ^ e₁ k * (a : ℂ) ^ e₂ k) := by
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ofReal_aeval]

private theorem ofReal_cpow_eq_cpow_sub_one_mul {x : ℝ} (hx : 0 < x) (a : ℂ) :
    (x : ℂ) ^ a = (x : ℂ) ^ (a - 1) * (x : ℂ) := by
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr hx.ne'
  rw [cpow_sub _ _ hx0, cpow_one, div_mul_cancel₀ _ hx0]

/-- Auxiliary `k`-th remainder integral `∫₀¹ f_k(r, x) (1 - x)^{a - 1} e^{a r x} dx` on `[0, 1]`. -/
private def fixedRatioRemIntegral (a : ℂ) (r : ℝ) (k : ℕ) : ℂ :=
  ∫ x in (0 : ℝ)..1,
    (((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) /
        (1 - r * (1 - x)) ^ (2 * k) : ℝ) : ℂ) *
      ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x)

private theorem fixedRatioRemIntegral_eq (a : ℂ) (r : ℝ) (k : ℕ) :
    fixedRatioRemIntegral a r k =
      ∫ x in (0 : ℝ)..1,
        (((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) /
            (1 - r * (1 - x)) ^ (2 * k) : ℝ) : ℂ) *
          ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x) :=
  rfl

private theorem continuousOn_ratio_div {r : ℝ} (hr1 : r < 1) (p : ℤ[X]) (m : ℕ) :
    ContinuousOn
      (fun x : ℝ => aeval (r * (1 - x)) p / (1 - r * (1 - x)) ^ m) [[0, 1]] := by
  rw [Set.uIcc_of_le zero_le_one]
  refine ContinuousOn.div ?_ ?_ fun x hx => pow_ne_zero _ (one_sub_mul_pos hr1 hx).ne'
  · exact (p.continuous_aeval.comp
      (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
  · exact ((continuous_const.sub
      (continuous_const.mul (continuous_const.sub continuous_id))).pow m).continuousOn

private theorem hasDerivAt_one_sub_cpow_mul_cexp {a : ℂ} (ha0 : a ≠ 0) (r : ℝ)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y : ℝ => ((1 - y : ℝ) : ℂ) ^ a * cexp (a * r * y))
      (-a * ((1 - r * (1 - x) : ℝ) : ℂ) * ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x)) x := by
  have hx1 : 0 < 1 - x := sub_pos.mpr hx.2
  have hpow1 : HasDerivAt (fun y : ℝ => ((1 - y : ℝ) : ℂ) ^ a)
      (-a * ((1 - x : ℝ) : ℂ) ^ (a - 1)) x := by
    have hout := _root_.hasDerivAt_ofReal_cpow_const hx1.ne' ha0
    have hin := (hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)
    exact (hout.scomp x hin).congr_deriv (by simp)
  have hexp1 : HasDerivAt (fun y : ℝ => cexp (a * r * y))
      (a * r * cexp (a * r * x)) x := by
    have hlin : HasDerivAt (fun z : ℂ => a * r * z) (a * r * 1) (x : ℂ) :=
      (hasDerivAt_id (x : ℂ)).const_mul (a * r)
    have hc := ((Complex.hasDerivAt_exp (a * r * (x : ℂ))).comp (x : ℂ) hlin).comp_ofReal
    exact hc.congr_deriv (by ring)
  refine (hpow1.mul hexp1).congr_deriv ?_
  rw [ofReal_cpow_eq_cpow_sub_one_mul hx1 a]
  push_cast
  ring

/-- Derivative of the real rational kernel `g_k(r, x) = (-1)^k b_k(t) / (1 - t)^{2k + 1}` along
`t = r (1 - x)`. -/
private def ratioKernelDeriv (r : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  -r * ((-1 : ℝ) ^ k *
    ((1 - r * (1 - x)) * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k).derivative +
      (2 * (k : ℝ) + 1) * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k)) /
    (1 - r * (1 - x)) ^ (2 * k + 2))

private theorem continuousOn_ratioKernelDeriv {r : ℝ} (hr1 : r < 1) (k : ℕ) :
    ContinuousOn (fun x : ℝ => (ratioKernelDeriv r k x : ℂ)) [[0, 1]] := by
  rw [Set.uIcc_of_le zero_le_one]
  refine continuous_ofReal.comp_continuousOn (continuousOn_const.mul (ContinuousOn.div ?_ ?_
    fun x hx => pow_ne_zero _ (one_sub_mul_pos hr1 hx).ne'))
  · refine continuousOn_const.mul (ContinuousOn.add ?_ ?_)
    · exact ((continuous_const.sub (continuous_const.mul
        (continuous_const.sub continuous_id))).mul
        ((TauCeti.secondOrderEulerianPolynomial k).derivative.continuous_aeval.comp
          (continuous_const.mul (continuous_const.sub continuous_id)))).continuousOn
    · exact (continuous_const.mul
        ((TauCeti.secondOrderEulerianPolynomial k).continuous_aeval.comp
          (continuous_const.mul (continuous_const.sub continuous_id)))).continuousOn
  · exact ((continuous_const.sub
      (continuous_const.mul (continuous_const.sub continuous_id))).pow _).continuousOn

private theorem integral_ratioKernel_mul_deriv (a : ℂ) {r : ℝ} (hr1 : r < 1) (k : ℕ) :
    (∫ x in (0 : ℝ)..1,
      (((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) /
          (1 - r * (1 - x)) ^ (2 * k + 1) : ℝ) : ℂ) *
        (-a * ((1 - r * (1 - x) : ℝ) : ℂ) * ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x))) =
      -a * fixedRatioRemIntegral a r k := by
  rw [fixedRatioRemIntegral_eq, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with x hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  have hden : 1 - r * (1 - x) ≠ 0 := (one_sub_mul_pos hr1 (Ioc_subset_Icc_self hx)).ne'
  have hreal : ((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) /
        (1 - r * (1 - x)) ^ (2 * k + 1)) * (1 - r * (1 - x)) =
      (-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) /
        (1 - r * (1 - x)) ^ (2 * k) := by
    rw [pow_succ (1 - r * (1 - x)) (2 * k)]
    field_simp [hden]
  calc _
    _ = -a * (((((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) /
          (1 - r * (1 - x)) ^ (2 * k + 1)) * (1 - r * (1 - x)) : ℝ) : ℂ) *
          ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x)) := by
      push_cast; ring
    _ = _ := by rw [hreal]

private theorem integral_ratioKernelDeriv_mul (a : ℂ) (r : ℝ) (k : ℕ) :
    (∫ x in (0 : ℝ)..1,
      (ratioKernelDeriv r k x : ℂ) * (((1 - x : ℝ) : ℂ) ^ a * cexp (a * r * x))) =
      fixedRatioRemIntegral a r (k + 1) := by
  rw [fixedRatioRemIntegral_eq]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [volume.ae_ne (1 : ℝ)] with x hxne hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  have hxpos : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_ne hx.2 hxne)
  have hreal : ratioKernelDeriv r k x * (1 - x) =
      (-1 : ℝ) ^ (k + 1) * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial (k + 1)) /
        (1 - r * (1 - x)) ^ (2 * (k + 1)) := by
    calc ratioKernelDeriv r k x * (1 - x)
      _ = -(r * (1 - x)) * ((-1 : ℝ) ^ k *
          ((1 - r * (1 - x)) *
            aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k).derivative +
            (2 * (k : ℝ) + 1) * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k)) /
          (1 - r * (1 - x)) ^ (2 * k + 2)) := by
        dsimp [ratioKernelDeriv]; ring
      _ = _ := TauCeti.neg_mul_deriv_secondOrderEulerianPolynomial_div k (r * (1 - x))
  calc _
    _ = ((ratioKernelDeriv r k x * (1 - x) : ℝ) : ℂ) *
        ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x) := by
      rw [ofReal_cpow_eq_cpow_sub_one_mul hxpos a]; push_cast; ring
    _ = _ := by rw [hreal]

private theorem hasDerivAt_ratioKernel {r : ℝ} (hr1 : r < 1) (k : ℕ) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun y : ℝ =>
        (((-1 : ℝ) ^ k * aeval (r * (1 - y)) (TauCeti.secondOrderEulerianPolynomial k) /
          (1 - r * (1 - y)) ^ (2 * k + 1) : ℝ) : ℂ))
      (ratioKernelDeriv r k x : ℂ) x := by
  have hrx : r * (1 - x) ≠ 1 := by linarith [one_sub_mul_pos hr1 (Ioo_subset_Icc_self hx)]
  have hin := ((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).const_mul r
  refine (((TauCeti.hasDerivAt_secondOrderEulerianPolynomial_div k hrx).comp x hin).ofReal_comp)
    |>.congr_deriv ?_
  dsimp [ratioKernelDeriv]; push_cast; ring

private theorem intervalIntegrable_deriv_one_sub_cpow_mul_cexp {a : ℂ} (ha : 0 < a.re) (r : ℝ) :
    IntervalIntegrable
      (fun x : ℝ =>
        -a * ((1 - r * (1 - x) : ℝ) : ℂ) * ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x))
      volume 0 1 := by
  have h1 : IntervalIntegrable (fun x : ℝ => ((1 - x : ℝ) : ℂ) ^ (a - 1)) volume 0 1 := by
    simpa only [ofReal_sub, ofReal_one] using
      TauCeti.intervalIntegrable_one_sub_ofReal_cpow (s := a - 1) (by simp [ha]) 0
  have hc1 : ContinuousOn (fun x : ℝ => -a * ((1 - r * (1 - x) : ℝ) : ℂ)) [[0, 1]] :=
    (continuous_const.mul (continuous_ofReal.comp
      (continuous_const.sub (continuous_const.mul (continuous_const.sub continuous_id)))))
      |>.continuousOn
  have hc2 : ContinuousOn (fun x : ℝ => cexp (a * r * x)) [[0, 1]] :=
    (Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal)).continuousOn
  simpa [mul_assoc] using (h1.continuousOn_mul hc1).mul_continuousOn hc2

/-- One integration-by-parts step on `fixedRatioRemIntegral`. -/
private theorem fixedRatioRemIntegral_step {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr1 : r < 1)
    (k : ℕ) :
    fixedRatioRemIntegral a r k =
      (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.secondOrderEulerianPolynomial k) /
          ((1 - (r : ℂ)) ^ (2 * k + 1) * a) +
        a⁻¹ * fixedRatioRemIntegral a r (k + 1) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  let u : ℝ → ℂ := fun x =>
    (((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) /
      (1 - r * (1 - x)) ^ (2 * k + 1) : ℝ) : ℂ)
  let v : ℝ → ℂ := fun x => ((1 - x : ℝ) : ℂ) ^ a * cexp (a * r * x)
  have hu_cont : ContinuousOn u [[0, 1]] := by
    have hc : ContinuousOn
        (fun x : ℝ => (-1 : ℝ) ^ k *
          (aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) /
            (1 - r * (1 - x)) ^ (2 * k + 1))) [[0, 1]] :=
      continuousOn_const.mul
        (continuousOn_ratio_div hr1 (TauCeti.secondOrderEulerianPolynomial k) (2 * k + 1))
    exact continuous_ofReal.comp_continuousOn (hc.congr fun x _ => by simp [mul_div_assoc])
  have hv_cont : ContinuousOn v [[0, 1]] :=
    (((Complex.continuous_ofReal_cpow_const ha).comp
      (continuous_const.sub continuous_id)).mul
        (Complex.continuous_exp.comp (continuous_const.mul continuous_ofReal))).continuousOn
  have hu_deriv : ∀ x ∈ Ioo (min (0 : ℝ) 1) (max 0 1),
      HasDerivAt u (ratioKernelDeriv r k x : ℂ) x := by
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one]
    exact fun x hx => hasDerivAt_ratioKernel hr1 k hx
  have hv_deriv : ∀ x ∈ Ioo (min (0 : ℝ) 1) (max 0 1),
      HasDerivAt v
        (-a * ((1 - r * (1 - x) : ℝ) : ℂ) * ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x)) x := by
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one]
    exact fun x hx => hasDerivAt_one_sub_cpow_mul_cexp ha0 r hx
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    hu_cont hv_cont hu_deriv hv_deriv (continuousOn_ratioKernelDeriv hr1 k).intervalIntegrable
    (intervalIntegrable_deriv_one_sub_cpow_mul_cexp ha r)
  have hv1 : v 1 = 0 := by simp [v, zero_cpow ha0]
  have hv0 : v 0 = 1 := by simp [v]
  have hu0 : u 0 = (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.secondOrderEulerianPolynomial k) /
      (1 - (r : ℂ)) ^ (2 * k + 1) := by
    dsimp only [u]
    rw [sub_zero, mul_one, ← ofReal_aeval]
    push_cast
    rfl
  rw [integral_ratioKernel_mul_deriv a hr1 k, hv1, hv0, mul_zero, mul_one, zero_sub,
    integral_ratioKernelDeriv_mul a r k, hu0] at hibp
  have heq := congr_arg (fun z : ℂ => (-a)⁻¹ * z) hibp
  have h1r : (1 - (r : ℂ)) ^ (2 * k + 1) ≠ 0 := pow_ne_zero _ (one_sub_ofReal_ne_zero hr1)
  rw [← mul_assoc, inv_mul_cancel₀ (neg_ne_zero.mpr ha0), one_mul] at heq
  rw [heq]
  field_simp [ha0, h1r]
  ring

/-- On `0 < Re a` and `r ≠ 0`, scaling `γ(a, r a)` by `(r a)^{-a} e^{r a}` gives the Euler
integral `∫₀¹ (1 - x)^{a - 1} e^{a r x} dx`. -/
theorem mul_lowerIncompleteGamma_mul_eq_integral {a : ℂ} (ha : 0 < a.re) {r : ℝ} (hr : r ≠ 0) :
    (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) =
      ∫ x in (0 : ℝ)..1, ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x) := by
  have ha0 : a ≠ 0 := by intro h; simp [h] at ha
  have hra0 : (r : ℂ) * a ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr) ha0
  have hcpow : ((r : ℂ) * a) ^ (-a) * ((r : ℂ) * a) ^ a = 1 := by
    rw [cpow_neg, inv_mul_cancel₀ (cpow_ne_zero_iff.mpr (.inl hra0))]
  rw [lowerIncompleteGamma_eq_integral ha (r * a), ← mul_assoc,
    mul_right_comm (((r : ℂ) * a) ^ (-a)) (cexp (r * a)) (((r : ℂ) * a) ^ a),
    hcpow, one_mul, ← intervalIntegral.integral_const_mul]
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun s : ℝ => cexp (r * a) * ((s : ℂ) ^ (a - 1) * cexp (-(r * a * s)))) (1 : ℝ)
    (a := (0 : ℝ)) (b := 1)
  rw [sub_self, sub_zero] at hsub
  rw [← hsub]
  refine intervalIntegral.integral_congr fun x _ => ?_
  rw [← mul_assoc, mul_comm (cexp (r * a)), mul_assoc, ← Complex.exp_add]
  congr 1
  congr 1
  push_cast
  ring

/-- **Exact `n`-term fixed-ratio expansion of `γ(a, r a)`** on the open right half-plane
`0 < Re a`, for `r < 1` and `r ≠ 0`: `n` integrations by parts peel off the first `n` terms of
DLMF 8.11.6 with an explicit integral remainder. -/
theorem mul_lowerIncompleteGamma_mul_eq_sum_add_integral {a : ℂ} (ha : 0 < a.re)
    {r : ℝ} (hr0 : r ≠ 0) (hr1 : r < 1) (n : ℕ) :
    (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) =
      (∑ k ∈ Finset.range n,
        (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.secondOrderEulerianPolynomial k) /
          ((1 - (r : ℂ)) ^ (2 * k + 1) * a ^ (k + 1))) +
      (a ^ n)⁻¹ * ∫ x in (0 : ℝ)..1,
        (((-1 : ℝ) ^ n * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial n) /
            (1 - r * (1 - x)) ^ (2 * n) : ℝ) : ℂ) *
          ((1 - x : ℝ) : ℂ) ^ (a - 1) * cexp (a * r * x) := by
  rw [← fixedRatioRemIntegral_eq]
  induction n with
  | zero =>
    rw [Finset.range_zero, Finset.sum_empty, zero_add, pow_zero, inv_one, one_mul,
      mul_lowerIncompleteGamma_mul_eq_integral ha hr0, fixedRatioRemIntegral_eq]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp
  | succ n ih =>
    have ha0 : a ≠ 0 := by intro h; simp [h] at ha
    rw [ih, fixedRatioRemIntegral_step ha hr1 n, Finset.sum_range_succ, mul_add, add_assoc]
    congr 2
    · field_simp [ha0]
      ring
    · rw [pow_succ, mul_inv, ← mul_assoc]

/-! ### Remainder bounds on the right half-plane and sectorial asymptotics (DLMF 8.11.6) -/

/-- For real parameter `s` and `r : ℝ`, `(-1)^k * fixedRatioRemIntegral s r k` equals the real
integral of the unsigned amplitude. -/
private theorem neg_one_pow_mul_fixedRatioRemIntegral_ofReal (s r : ℝ) (k : ℕ) :
    (-1 : ℂ) ^ k * fixedRatioRemIntegral s r k =
      ((∫ x in (0 : ℝ)..1,
        (aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) /
          (1 - r * (1 - x)) ^ (2 * k)) *
          (1 - x) ^ (s - 1) * Real.exp (s * r * x) : ℝ) : ℂ) := by
  rw [fixedRatioRemIntegral_eq, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_ofReal]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [volume.ae_ne (1 : ℝ)] with x hxne hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  have hxpos : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_ne hx.2 hxne)
  have hcpow : ((1 - x : ℝ) : ℂ) ^ ((s : ℂ) - 1) = (((1 - x) ^ (s - 1) : ℝ) : ℂ) := by
    rw [Complex.ofReal_cpow hxpos.le, ofReal_sub, ofReal_sub, ofReal_one]
  have hexp : cexp ((s : ℂ) * r * x) = (Real.exp (s * r * x) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [hcpow, hexp]
  have hreal : (-1 : ℂ) ^ k *
      ((((-1 : ℝ) ^ k * aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) /
          (1 - r * (1 - x)) ^ (2 * k) : ℝ) : ℂ) *
        (((1 - x) ^ (s - 1) : ℝ) : ℂ) * (Real.exp (s * r * x) : ℂ)) =
      ((((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
        ((aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) /
          (1 - r * (1 - x)) ^ (2 * k)) *
          (1 - x) ^ (s - 1) * Real.exp (s * r * x)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [hreal]
  simp [← mul_pow]

private theorem neg_one_pow_mul_fixedRatioRemIntegral_ofReal_re_nonneg (s : ℝ)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    0 ≤ ((-1 : ℂ) ^ k * fixedRatioRemIntegral s r k).re ∧
      ((-1 : ℂ) ^ k * fixedRatioRemIntegral s r k).im = 0 := by
  rw [neg_one_pow_mul_fixedRatioRemIntegral_ofReal s r k, ofReal_re, ofReal_im]
  refine ⟨intervalIntegral.integral_nonneg zero_le_one fun x hx => ?_, rfl⟩
  have hx1 : 0 ≤ 1 - x := sub_nonneg.mpr hx.2
  have hpoly : 0 ≤ aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) :=
    TauCeti.aeval_secondOrderEulerianPolynomial_nonneg (mul_nonneg hr0 hx1) k
  have hden : 0 ≤ (1 - r * (1 - x)) ^ (2 * k) := pow_nonneg (one_sub_mul_pos hr1 hx).le _
  exact mul_nonneg (mul_nonneg (div_nonneg hpoly hden) (Real.rpow_nonneg hx1 _))
    (Real.exp_pos _).le

private theorem norm_fixedRatioRemIntegral_le_re (a : ℂ) {r : ℝ} (hr0 : 0 ≤ r)
    (hr1 : r < 1) (k : ℕ) :
    ‖fixedRatioRemIntegral a r k‖ ≤
      ((-1 : ℂ) ^ k * fixedRatioRemIntegral a.re r k).re := by
  rw [neg_one_pow_mul_fixedRatioRemIntegral_ofReal a.re r k, ofReal_re, fixedRatioRemIntegral_eq]
  refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans_eq ?_
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [volume.ae_ne (1 : ℝ)] with x hxne hx
  rw [Set.uIoc_of_le zero_le_one] at hx
  have hxpos : 0 < 1 - x := sub_pos.mpr (lt_of_le_of_ne hx.2 hxne)
  have hpoly : 0 ≤ aeval (r * (1 - x)) (TauCeti.secondOrderEulerianPolynomial k) :=
    TauCeti.aeval_secondOrderEulerianPolynomial_nonneg (mul_nonneg hr0 hxpos.le) k
  have hden : 0 < 1 - r * (1 - x) := one_sub_mul_pos hr1 (Ioc_subset_Icc_self hx)
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_cpow_eq_rpow_re_of_pos hxpos,
    Complex.norm_exp]
  simp [abs_of_nonneg hpoly, abs_of_pos hden, mul_assoc]

/-- Pointwise norm bound on `fixedRatioRemIntegral` on the open right half-plane `0 < Re a`. -/
private theorem norm_fixedRatioRemIntegral_le {a : ℂ} (ha : 0 < a.re) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (k : ℕ) :
    ‖fixedRatioRemIntegral a r k‖ ≤
      aeval r (TauCeti.secondOrderEulerianPolynomial k) /
        ((1 - r) ^ (2 * k + 1) * a.re) := by
  refine (norm_fixedRatioRemIntegral_le_re a hr0 hr1 k).trans ?_
  have hstep := congr_arg (fun z : ℂ => ((-1 : ℂ) ^ k * z).re)
    (fixedRatioRemIntegral_step (a := (a.re : ℂ)) (by simpa using ha) hr1 k)
  have hnext := (neg_one_pow_mul_fixedRatioRemIntegral_ofReal_re_nonneg a.re hr0 hr1 (k + 1)).1
  have hterm : ((-1 : ℂ) ^ k *
      ((-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.secondOrderEulerianPolynomial k) /
        ((1 - (r : ℂ)) ^ (2 * k + 1) * (a.re : ℂ)))).re =
      aeval r (TauCeti.secondOrderEulerianPolynomial k) / ((1 - r) ^ (2 * k + 1) * a.re) := by
    rw [← ofReal_aeval]
    have hcast : (-1 : ℂ) ^ k *
        ((-1 : ℂ) ^ k * (aeval r (TauCeti.secondOrderEulerianPolynomial k) : ℂ) /
          ((1 - (r : ℂ)) ^ (2 * k + 1) * (a.re : ℂ))) =
        ((((-1 : ℝ) ^ k * (-1 : ℝ) ^ k) *
          (aeval r (TauCeti.secondOrderEulerianPolynomial k) /
            ((1 - r) ^ (2 * k + 1) * a.re)) : ℝ) : ℂ) := by
      push_cast; ring
    rw [hcast, ofReal_re]
    simp [← mul_pow]
  have htail : ((-1 : ℂ) ^ k * ((a.re : ℂ)⁻¹ * fixedRatioRemIntegral a.re r (k + 1))).re =
      -(a.re⁻¹ * ((-1 : ℂ) ^ (k + 1) * fixedRatioRemIntegral a.re r (k + 1)).re) := by
    have him := (neg_one_pow_mul_fixedRatioRemIntegral_ofReal_re_nonneg a.re hr0 hr1 (k + 1)).2
    have hrew_tail : (-1 : ℂ) ^ k * ((a.re : ℂ)⁻¹ * fixedRatioRemIntegral a.re r (k + 1)) =
        -((a.re⁻¹ : ℝ) : ℂ) * ((-1 : ℂ) ^ (k + 1) * fixedRatioRemIntegral a.re r (k + 1)) := by
      rw [pow_succ, ofReal_inv]; ring
    rw [hrew_tail, neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, him, zero_mul, sub_zero]
  rw [mul_add, add_re, hterm, htail] at hstep
  have hnn : 0 ≤ a.re⁻¹ * ((-1 : ℂ) ^ (k + 1) * fixedRatioRemIntegral a.re r (k + 1)).re :=
    mul_nonneg (inv_nonneg.mpr ha.le) hnext
  linarith

/-- **Explicit remainder bound for `(r a)^{-a} e^{r a} γ(a, r a)` on the open right half-plane
`0 < Re a`**: for `0 < r < 1` and every `n : ℕ`, the `n`-th remainder has norm at most
`b_n(r) / ((1 - r)^{2n + 1} ‖a‖^n Re a)`. -/
theorem norm_mul_lowerIncompleteGamma_fixedRatio_sub_sum_le {a : ℂ} (ha : 0 < a.re)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    ‖(r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.secondOrderEulerianPolynomial k) /
            ((1 - (r : ℂ)) ^ (2 * k + 1) * a ^ (k + 1))‖ ≤
      aeval r (TauCeti.secondOrderEulerianPolynomial n) /
        ((1 - r) ^ (2 * n + 1) * ‖a‖ ^ n * a.re) := by
  rw [mul_lowerIncompleteGamma_mul_eq_sum_add_integral ha hr0.ne' hr1 n, add_sub_cancel_left,
    ← fixedRatioRemIntegral_eq, norm_mul, norm_inv, norm_pow]
  refine (mul_le_mul_of_nonneg_left (norm_fixedRatioRemIntegral_le ha hr0.le hr1 n)
    (by positivity)).trans_eq ?_
  rw [inv_mul_eq_div, div_div]
  ring

/-- **Explicit sectorial remainder bound for `(r a)^{-a} e^{r a} γ(a, r a)`**: for `0 < δ`,
nonzero `a` with `|arg a| ≤ π / 2 - δ`, and `0 < r < 1`, the `n`-th remainder is bounded in norm
by `b_n(r) / ((1 - r)^{2n + 1} sin δ · ‖a‖^{n + 1})`. -/
theorem norm_mul_lowerIncompleteGamma_fixedRatio_sub_sum_le_of_abs_arg_le {a : ℂ} {δ : ℝ}
    (hδ : 0 < δ) (ha : |a.arg| ≤ Real.pi / 2 - δ) (ha0 : a ≠ 0) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (n : ℕ) :
    ‖(r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.secondOrderEulerianPolynomial k) /
            ((1 - (r : ℂ)) ^ (2 * k + 1) * a ^ (k + 1))‖ ≤
      aeval r (TauCeti.secondOrderEulerianPolynomial n) /
        ((1 - r) ^ (2 * n + 1) * Real.sin δ * ‖a‖ ^ (n + 1)) := by
  have hδ2 : δ ≤ Real.pi / 2 := by linarith [abs_nonneg a.arg]
  have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
  have hre_ge := TauCeti.norm_mul_sin_le_re_of_abs_arg_le (by linarith [Real.pi_pos]) ha
  have hre : 0 < a.re := (abs_arg_lt_pi_div_two_iff.mp (by linarith)).resolve_right ha0
  refine (norm_mul_lowerIncompleteGamma_fixedRatio_sub_sum_le hre hr0 hr1 n).trans ?_
  have hnum : 0 ≤ aeval r (TauCeti.secondOrderEulerianPolynomial n) :=
    TauCeti.aeval_secondOrderEulerianPolynomial_nonneg hr0.le n
  have _ : 0 < (1 - r) ^ (2 * n + 1) := pow_pos (sub_pos.mpr hr1) _
  refine div_le_div_of_nonneg_left hnum (by positivity) ?_
  calc (1 - r) ^ (2 * n + 1) * Real.sin δ * ‖a‖ ^ (n + 1)
    _ = (1 - r) ^ (2 * n + 1) * ‖a‖ ^ n * (‖a‖ * Real.sin δ) := by rw [pow_succ]; ring
    _ ≤ (1 - r) ^ (2 * n + 1) * ‖a‖ ^ n * a.re :=
      mul_le_mul_of_nonneg_left hre_ge (by positivity)

/-- **DLMF 8.11.6 (normalized form)**: for fixed `0 < r < 1`, every truncation order `n : ℕ`, and
every `δ > 0`,
`(a - r a) (r a)^{-a} e^{r a} γ(a, r a) - ∑_{k < n} (-1)^k b_k(r) / ((1 - r)^{2k} a^k)
= O((‖a‖ ^ n)⁻¹)` as `a → ∞` in `|arg a| ≤ π / 2 - δ`. -/
theorem isBigO_sub_mul_lowerIncompleteGamma_fixedRatio {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (fun a : ℂ =>
        (a - r * a) * (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
          ∑ k ∈ Finset.range n,
            (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.secondOrderEulerianPolynomial k) /
              ((1 - (r : ℂ)) ^ (2 * k) * a ^ k))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}]
        fun a : ℂ => (‖a‖ ^ n)⁻¹ := by
  rcases lt_or_ge (Real.pi / 2) δ with hδbig | hδ2
  · have hempty : {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ} = ∅ := by
      ext a; simp only [mem_ofPred, mem_empty_iff_false, iff_false, not_le]
      linarith [abs_nonneg a.arg]
    simp [hempty]
  · have hsin : 0 < Real.sin δ := Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos])
    refine IsBigO.of_bound
      (aeval r (TauCeti.secondOrderEulerianPolynomial n) / ((1 - r) ^ (2 * n) * Real.sin δ)) ?_
    rw [eventually_inf_principal]
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with a ha_norm ha_arg
    have ha0 : a ≠ 0 := norm_pos_iff.mp ha_norm
    have h1r : 0 < 1 - r := sub_pos.mpr hr1
    have hfactor :
        (a - r * a) * (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
          (∑ k ∈ Finset.range n,
            (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.secondOrderEulerianPolynomial k) /
              ((1 - (r : ℂ)) ^ (2 * k) * a ^ k)) =
        (1 - (r : ℂ)) * a *
          ((r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
            ∑ k ∈ Finset.range n,
              (-1 : ℂ) ^ k * aeval (r : ℂ) (TauCeti.secondOrderEulerianPolynomial k) /
                ((1 - (r : ℂ)) ^ (2 * k + 1) * a ^ (k + 1))) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      · ring
      · refine Finset.sum_congr rfl fun k _ => ?_
        rw [pow_succ (1 - (r : ℂ)) (2 * k), pow_succ a k]
        field_simp [one_sub_ofReal_ne_zero hr1, ha0]
    have hnorm1r : ‖(1 - (r : ℂ))‖ = 1 - r := by
      rw [← ofReal_one, ← ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1r]
    rw [hfactor, norm_mul, norm_mul, hnorm1r, norm_inv, norm_pow, norm_norm]
    have hbd := norm_mul_lowerIncompleteGamma_fixedRatio_sub_sum_le_of_abs_arg_le
      hδ ha_arg ha0 hr0 hr1 n
    refine (mul_le_mul_of_nonneg_left hbd (mul_nonneg h1r.le (norm_nonneg a))).trans_eq ?_
    rw [pow_succ (1 - r) (2 * n), pow_succ ‖a‖ n]
    field_simp [h1r.ne', hsin.ne', ha_norm.ne']

/-- **DLMF 8.11.6 (`z^{1 - a} e^z γ(a, z)` form)**: for fixed `0 < r < 1`, every `n : ℕ`, and
every `δ > 0`,
`(r a)^{1 - a} e^{r a} γ(a, r a) - ∑_{k < n} (-1)^k r b_k(r) / ((1 - r)^{2k + 1} a^k)
= O((‖a‖ ^ n)⁻¹)` as `a → ∞` in `|arg a| ≤ π / 2 - δ`. -/
theorem isBigO_cpow_one_sub_mul_lowerIncompleteGamma_fixedRatio {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    (fun a : ℂ =>
        (r * a) ^ (1 - a) * cexp (r * a) * lowerIncompleteGamma a (r * a) -
          ∑ k ∈ Finset.range n,
            (-1 : ℂ) ^ k * r * aeval (r : ℂ) (TauCeti.secondOrderEulerianPolynomial k) /
              ((1 - (r : ℂ)) ^ (2 * k + 1) * a ^ k))
      =O[Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}]
        fun a : ℂ => (‖a‖ ^ n)⁻¹ := by
  have hmain := (isBigO_sub_mul_lowerIncompleteGamma_fixedRatio hr0 hr1 n hδ).const_mul_left
    ((r : ℂ) / (1 - (r : ℂ)))
  refine hmain.congr' ?_ EventuallyEq.rfl
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).filter_mono
    inf_le_left] with a ha_norm
  have ha0 : a ≠ 0 := norm_pos_iff.mp ha_norm
  have hra0 : (r : ℂ) * a ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr0.ne') ha0
  have h1rc : 1 - (r : ℂ) ≠ 0 := one_sub_ofReal_ne_zero hr1
  have hcpow : ((r : ℂ) * a) ^ (1 - a) = (r : ℂ) * a * ((r : ℂ) * a) ^ (-a) := by
    rw [sub_eq_add_neg, cpow_add _ _ hra0, cpow_one]
  rw [hcpow, mul_sub, Finset.mul_sum]
  congr 1
  · field_simp [h1rc]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_succ (1 - (r : ℂ)) (2 * k)]
    field_simp [h1rc]

/-- **Leading sectorial asymptotic of `γ(a, r a)`** (DLMF 8.11.6, `n = 1`): for `0 < r < 1` and
`δ > 0`, `γ(a, r a) ~ (r a)^a e^{-r a} / ((1 - r) a)` as `a → ∞` in `|arg a| ≤ π / 2 - δ`. -/
theorem lowerIncompleteGamma_fixedRatio_isEquivalent {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    (fun a : ℂ => lowerIncompleteGamma a (r * a))
      ~[Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}]
        fun a : ℂ => (r * a) ^ a * cexp (-(r * a)) / ((1 - r) * a) := by
  have hbig := isBigO_sub_mul_lowerIncompleteGamma_fixedRatio hr0 hr1 1 hδ
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, mul_zero, one_mul,
    TauCeti.secondOrderEulerianPolynomial_zero, map_one, div_one, pow_one] at hbig
  have hlim0 : Tendsto (fun a : ℂ => ‖a‖⁻¹)
      (Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}) (𝓝 0) :=
    (tendsto_inv_atTop_zero.comp tendsto_norm_cobounded_atTop).mono_left inf_le_left
  have hsub0 : Tendsto
      (fun a : ℂ =>
        (a - r * a) * (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a) - 1)
      (Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}) (𝓝 0) :=
    hbig.trans_tendsto hlim0
  refine isEquivalent_of_tendsto_one ?_
  have hquot : Tendsto
      (fun a : ℂ =>
        (a - r * a) * (r * a) ^ (-a) * cexp (r * a) * lowerIncompleteGamma a (r * a))
      (Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}) (𝓝 1) := by
    simpa using hsub0.add_const (1 : ℂ)
  refine hquot.congr' ?_
  filter_upwards [(tendsto_norm_cobounded_atTop.eventually_gt_atTop 0).filter_mono
    inf_le_left] with a ha_norm
  have ha0 : a ≠ 0 := norm_pos_iff.mp ha_norm
  have hra0 : (r : ℂ) * a ≠ 0 := mul_ne_zero (ofReal_ne_zero.mpr hr0.ne') ha0
  have hc1 : ((r : ℂ) * a) ^ a ≠ 0 := cpow_ne_zero_iff.mpr (.inl hra0)
  dsimp [Pi.div_apply]
  rw [cpow_neg, Complex.exp_neg]
  field_simp [ha0, one_sub_ofReal_ne_zero hr1, hc1, Complex.exp_ne_zero ((r : ℂ) * a)]

/-- **Leading sectorial asymptotic of `P(a, r a)`**: combining DLMF 8.11.6 with sectorial
Stirling's formula gives
`P(a, r a) ~ r^a e^{(1 - r) a} / (√(2π) (1 - r) a^{1/2})` as `a → ∞` in `|arg a| ≤ π / 2 - δ`,
for fixed `0 < r < 1` and `δ > 0`. -/
theorem regularizedGamma_fixedRatio_isEquivalent {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    {δ : ℝ} (hδ : 0 < δ) :
    (fun a : ℂ => regularizedGamma a (r * a))
      ~[Bornology.cobounded ℂ ⊓ 𝓟 {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ}]
        fun a : ℂ =>
          (r : ℂ) ^ a * cexp ((1 - r) * a) /
            ((Real.sqrt (2 * Real.pi) : ℂ) * (1 - r) * a ^ (1 / 2 : ℂ)) := by
  have hsub_sec : {a : ℂ | |a.arg| ≤ Real.pi / 2 - δ} ⊆ {a : ℂ | |a.arg| ≤ Real.pi - δ} :=
    fun a ha => le_trans (mem_ofPred.mp ha) (by linarith [Real.pi_pos])
  have hstir := (TauCeti.Gamma_isEquivalent_stirling_sector hδ).mono
    (inf_le_inf_left (Bornology.cobounded ℂ) (principal_mono.mpr hsub_sec))
  have hdiv := (lowerIncompleteGamma_fixedRatio_isEquivalent hr0 hr1 hδ).div hstir
  refine (IsEquivalent.congr_left hdiv ?_).congr_right ?_
  · rw [EventuallyEq, eventually_inf_principal]
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with a ha_norm ha_arg
    have hre : 0 < a.re :=
      (abs_arg_lt_pi_div_two_iff.mp (by linarith)).resolve_right (norm_pos_iff.mp ha_norm)
    dsimp [Pi.div_apply]
    rw [lowerIncompleteGamma_def, mul_div_cancel_left₀ _ (Gamma_ne_zero_of_re_pos hre)]
  · rw [EventuallyEq, eventually_inf_principal]
    filter_upwards [tendsto_norm_cobounded_atTop.eventually_gt_atTop 0] with a ha_norm _
    have ha0 : a ≠ 0 := norm_pos_iff.mp ha_norm
    have ha_split : a ^ a = a * a ^ (a - 1 / 2) / a ^ (1 / 2 : ℂ) := by
      calc a ^ a
        _ = a ^ (1 + (a - 1 / 2) - 1 / 2) := by congr 1; ring
        _ = a * a ^ (a - 1 / 2) / a ^ (1 / 2 : ℂ) := by
          rw [cpow_sub _ _ ha0, cpow_add _ _ ha0, cpow_one]
    have hexp : cexp ((1 - (r : ℂ)) * a) = cexp (-((r : ℂ) * a)) / cexp (-a) := by
      rw [← Complex.exp_sub]
      congr 1
      ring
    have ha_sub0 : a ^ (a - 1 / 2) ≠ 0 := cpow_ne_zero_iff.mpr (.inl ha0)
    have ha_half0 : a ^ (1 / 2 : ℂ) ≠ 0 := cpow_ne_zero_iff.mpr (.inl ha0)
    have hsq0 : (Real.sqrt (2 * Real.pi) : ℂ) ≠ 0 :=
      ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by positivity))
    dsimp [Pi.div_apply]
    rw [ofReal_mul_cpow hr0.le, ha_split, hexp]
    field_simp [ha0, ha_sub0, ha_half0, one_sub_ofReal_ne_zero hr1, hsq0, Complex.exp_ne_zero _]

end Complex

namespace TauCeti

/-! ### Enveloping inequalities and asymptotics on the positive real axis -/

/-- **Enveloping lower bound on the `n`-th remainder** of `(r a)^{-a} e^{r a} γ(a, r a)` for real
`a > 0` and `0 < r < 1`: multiplying the `n`-th remainder by `(-1)^n` gives a nonnegative number. -/
theorem neg_one_pow_mul_mul_lowerIncompleteGamma_fixedRatio_sub_sum_nonneg {a r : ℝ} (ha : 0 < a)
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n *
      ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℝ) ^ k * aeval r (secondOrderEulerianPolynomial k) /
            ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))) := by
  have hare : 0 < (a : ℂ).re := by simpa using ha
  have hcast : (((-1 : ℝ) ^ n *
      ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℝ) ^ k * aeval r (secondOrderEulerianPolynomial k) /
            ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))) : ℝ) : ℂ) =
      ((a ^ n)⁻¹ : ℝ) * ((-1 : ℂ) ^ n * Complex.fixedRatioRemIntegral a r n) := by
    have hmain := Complex.mul_lowerIncompleteGamma_mul_eq_sum_add_integral hare hr0.ne' hr1 n
    have hra : 0 < r * a := mul_pos hr0 ha
    have hsum := Complex.ofReal_sum_secondOrderEulerianPolynomial_div r a n
      (fun k => 2 * k + 1) (fun k => k + 1)
    rw [Complex.ofReal_mul, Complex.ofReal_sub, hsum]
    push_cast
    rw [Complex.ofReal_cpow hra.le, ← Complex.lowerIncompleteGamma_ofReal ha hra.le]
    push_cast
    rw [hmain, add_sub_cancel_left, ← Complex.fixedRatioRemIntegral_eq]
    ring
  have hre := congr_arg Complex.re hcast
  rw [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hre
  rw [hre]
  exact mul_nonneg (by positivity)
    (Complex.neg_one_pow_mul_fixedRatioRemIntegral_ofReal_re_nonneg a hr0.le hr1 n).1

/-- **Enveloping upper bound on the `n`-th remainder** of `(r a)^{-a} e^{r a} γ(a, r a)` for real
`a > 0` and `0 < r < 1`: the remainder multiplied by `(-1)^n` is at most the first neglected term
`b_n(r) / ((1 - r)^{2n + 1} a^{n + 1})`. -/
theorem neg_one_pow_mul_mul_lowerIncompleteGamma_fixedRatio_sub_sum_le {a r : ℝ} (ha : 0 < a)
    (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    (-1 : ℝ) ^ n *
      ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℝ) ^ k * aeval r (secondOrderEulerianPolynomial k) /
            ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))) ≤
      aeval r (secondOrderEulerianPolynomial n) / ((1 - r) ^ (2 * n + 1) * a ^ (n + 1)) := by
  have hnext :=
    neg_one_pow_mul_mul_lowerIncompleteGamma_fixedRatio_sub_sum_nonneg ha hr0 hr1 (n + 1)
  rw [Finset.sum_range_succ, sub_add_eq_sub_sub, pow_succ (-1 : ℝ)] at hnext
  have hrew : ((-1 : ℝ) ^ n * (-1 : ℝ)) *
      (((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
        ∑ k ∈ Finset.range n,
          (-1 : ℝ) ^ k * aeval r (secondOrderEulerianPolynomial k) /
            ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))) -
        (-1 : ℝ) ^ n * aeval r (secondOrderEulerianPolynomial n) /
          ((1 - r) ^ (2 * n + 1) * a ^ (n + 1))) =
      ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
        (aeval r (secondOrderEulerianPolynomial n) / ((1 - r) ^ (2 * n + 1) * a ^ (n + 1))) -
      (-1 : ℝ) ^ n *
        ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
          ∑ k ∈ Finset.range n,
            (-1 : ℝ) ^ k * aeval r (secondOrderEulerianPolynomial k) /
              ((1 - r) ^ (2 * k + 1) * a ^ (k + 1))) := by ring
  rw [hrew] at hnext
  simp only [← mul_pow, neg_mul, one_mul, neg_neg, one_pow] at hnext
  linarith

/-- Two-sided bounds on `γ(a, r a)` from the `n = 0` and `n = 1` enveloping bounds:
for `a > 0` and `0 < r < 1`,
`(r a)^a e^{-r a} / ((1 - r) a) * (1 - r / ((1 - r)^2 a)) ≤ γ(a, r a) ≤
(r a)^a e^{-r a} / ((1 - r) a)`. -/
theorem lowerIncompleteGamma_fixedRatio_bounds {a r : ℝ} (ha : 0 < a) (hr0 : 0 < r)
    (hr1 : r < 1) :
    (r * a) ^ a * Real.exp (-(r * a)) / ((1 - r) * a) * (1 - r / ((1 - r) ^ 2 * a)) ≤
        lowerIncompleteGamma a (r * a) ∧
      lowerIncompleteGamma a (r * a) ≤
        (r * a) ^ a * Real.exp (-(r * a)) / ((1 - r) * a) := by
  have hra : 0 < r * a := mul_pos hr0 ha
  have h1r : 0 < 1 - r := sub_pos.mpr hr1
  have hpow_pos : 0 < (r * a) ^ a * Real.exp (-(r * a)) :=
    mul_pos (Real.rpow_pos_of_pos hra a) (Real.exp_pos _)
  have hcancel : (r * a) ^ a * Real.exp (-(r * a)) * ((r * a) ^ (-a) * Real.exp (r * a)) = 1 := by
    rw [mul_mul_mul_comm, ← Real.rpow_add hra, add_neg_cancel, Real.rpow_zero,
      ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  have h0 := neg_one_pow_mul_mul_lowerIncompleteGamma_fixedRatio_sub_sum_le ha hr0 hr1 0
  simp only [pow_zero, one_mul, Finset.range_zero, Finset.sum_empty, sub_zero,
    secondOrderEulerianPolynomial_zero, map_one, mul_zero, zero_add, pow_one] at h0
  have h1' := neg_one_pow_mul_mul_lowerIncompleteGamma_fixedRatio_sub_sum_le ha hr0 hr1 1
  simp only [pow_one, Finset.range_one, Finset.sum_singleton, pow_zero, one_mul,
    secondOrderEulerianPolynomial_zero, map_one, secondOrderEulerianPolynomial_one, aeval_X,
    neg_one_mul] at h1'
  constructor
  · have hlow : 1 / ((1 - r) * a) - r / ((1 - r) ^ 3 * a ^ 2) ≤
        (r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) := by
      have h1'' : -((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
            1 / ((1 - r) * a)) ≤ r / ((1 - r) ^ 3 * a ^ 2) := by
        simpa using h1'
      linarith
    have hm := mul_le_mul_of_nonneg_left hlow hpow_pos.le
    have hl : (r * a) ^ a * Real.exp (-(r * a)) / ((1 - r) * a) * (1 - r / ((1 - r) ^ 2 * a)) =
        (r * a) ^ a * Real.exp (-(r * a)) *
          (1 / ((1 - r) * a) - r / ((1 - r) ^ 3 * a ^ 2)) := by
      field_simp [h1r.ne', ha.ne']
    have hr : (r * a) ^ a * Real.exp (-(r * a)) *
        ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a)) =
        lowerIncompleteGamma a (r * a) := by
      rw [← mul_assoc, hcancel, one_mul]
    linarith
  · have hm := mul_le_mul_of_nonneg_left h0 hpow_pos.le
    have hl : lowerIncompleteGamma a (r * a) =
        (r * a) ^ a * Real.exp (-(r * a)) *
          ((r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a)) := by
      rw [← mul_assoc, hcancel, one_mul]
    have hr : (r * a) ^ a * Real.exp (-(r * a)) * (1 / ((1 - r) * a)) =
        (r * a) ^ a * Real.exp (-(r * a)) / ((1 - r) * a) := by ring
    linarith

private theorem tendsto_ofReal_cobounded_sector :
    Tendsto (fun a : ℝ => (a : ℂ)) atTop
      (Bornology.cobounded ℂ ⊓ 𝓟 {z : ℂ | |z.arg| ≤ Real.pi / 2 - Real.pi / 4}) := by
  rw [tendsto_inf, tendsto_principal]
  refine ⟨tendsto_norm_atTop_iff_cobounded.mp ?_, ?_⟩
  · simpa [Complex.norm_real] using tendsto_abs_atTop_atTop
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with a ha
    rw [Complex.arg_ofReal_of_nonneg ha, abs_zero]
    linarith [Real.pi_pos]

/-- **Real fixed-ratio asymptotic expansion of `γ(a, r a)`** (DLMF 8.11.6 on `(0, ∞)`):
for fixed `0 < r < 1` and every `n : ℕ`,
`(a - r a) (r a)^{-a} e^{r a} γ(a, r a) - ∑_{k < n} (-1)^k b_k(r) / ((1 - r)^{2k} a^k)
= O((a ^ n)⁻¹)` as `a → +∞`. -/
theorem isBigO_sub_mul_lowerIncompleteGamma_fixedRatio {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (n : ℕ) :
    (fun a : ℝ =>
        (a - r * a) * (r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
          ∑ k ∈ Finset.range n,
            (-1 : ℝ) ^ k * aeval r (secondOrderEulerianPolynomial k) /
              ((1 - r) ^ (2 * k) * a ^ k))
      =O[atTop] fun a : ℝ => (a ^ n)⁻¹ := by
  have hce := (Complex.isBigO_sub_mul_lowerIncompleteGamma_fixedRatio hr0 hr1 n
    (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4)).comp_tendsto
      tendsto_ofReal_cobounded_sector
  have hcast :
      (fun a : ℝ =>
          (((a - r * a) * (r * a) ^ (-a) * Real.exp (r * a) * lowerIncompleteGamma a (r * a) -
            ∑ k ∈ Finset.range n,
              (-1 : ℝ) ^ k * aeval r (secondOrderEulerianPolynomial k) /
                ((1 - r) ^ (2 * k) * a ^ k) : ℝ) : ℂ))
        =O[atTop] fun a : ℝ => (a ^ n)⁻¹ := by
    refine hce.congr' ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      have hra : 0 < r * a := mul_pos hr0 ha
      have hsum := Complex.ofReal_sum_secondOrderEulerianPolynomial_div r a n
        (fun k => 2 * k) (fun k => k)
      dsimp only [Function.comp_def]
      rw [Complex.ofReal_sub, hsum]
      push_cast
      rw [Complex.ofReal_cpow hra.le, ← Complex.lowerIncompleteGamma_ofReal ha hra.le]
      push_cast
      rfl
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      simp only [Function.comp_def, Complex.norm_real, Real.norm_of_nonneg ha.le]
  rw [← isBigO_norm_left] at hcast ⊢
  simpa only [Complex.norm_real] using hcast

/-- **Real leading asymptotic of `γ(a, r a)`**: for `0 < r < 1`,
`γ(a, r a) ~ (r a)^a e^{-r a} / ((1 - r) a)` as `a → +∞`. -/
theorem lowerIncompleteGamma_fixedRatio_isEquivalent {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (fun a : ℝ => lowerIncompleteGamma a (r * a)) ~[atTop]
      fun a : ℝ => (r * a) ^ a * Real.exp (-(r * a)) / ((1 - r) * a) := by
  have hce := (Complex.lowerIncompleteGamma_fixedRatio_isEquivalent hr0 hr1
    (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4)).comp_tendsto
      tendsto_ofReal_cobounded_sector
  have hcast :
      (fun a : ℝ => (lowerIncompleteGamma a (r * a) : ℂ)) ~[atTop]
        fun a : ℝ => (((r * a) ^ a * Real.exp (-(r * a)) / ((1 - r) * a) : ℝ) : ℂ) := by
    refine (hce.congr_left ?_).congr_right ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      dsimp only [Function.comp_def]
      rw [← Complex.ofReal_mul, Complex.lowerIncompleteGamma_ofReal ha (mul_pos hr0 ha).le]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      dsimp only [Function.comp_def]
      push_cast
      rw [Complex.ofReal_cpow (mul_pos hr0 ha).le, Complex.ofReal_mul]
  rw [IsEquivalent, ← isLittleO_norm_norm] at hcast ⊢
  simpa only [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hcast

/-- **Real leading asymptotic of `P(a, r a)`**: for `0 < r < 1`,
`P(a, r a) ~ r^a e^{(1 - r) a} / (√(2π) (1 - r) √a)` as `a → +∞`. -/
theorem regularizedGamma_fixedRatio_isEquivalent {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    (fun a : ℝ => regularizedGamma a (r * a)) ~[atTop]
      fun a : ℝ =>
        r ^ a * Real.exp ((1 - r) * a) /
          (Real.sqrt (2 * Real.pi) * (1 - r) * Real.sqrt a) := by
  have hce := (Complex.regularizedGamma_fixedRatio_isEquivalent hr0 hr1
    (by linarith [Real.pi_pos] : (0 : ℝ) < Real.pi / 4)).comp_tendsto
      tendsto_ofReal_cobounded_sector
  have hcast :
      (fun a : ℝ => (regularizedGamma a (r * a) : ℂ)) ~[atTop]
        fun a : ℝ => ((r ^ a * Real.exp ((1 - r) * a) /
          (Real.sqrt (2 * Real.pi) * (1 - r) * Real.sqrt a) : ℝ) : ℂ) := by
    refine (hce.congr_left ?_).congr_right ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      dsimp only [Function.comp_def]
      rw [← Complex.ofReal_mul, Complex.regularizedGamma_ofReal ha (mul_pos hr0 ha).le]
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
      dsimp only [Function.comp_def]
      rw [Real.sqrt_eq_rpow a]
      push_cast
      rw [Complex.ofReal_cpow hr0.le, Complex.ofReal_cpow ha.le]
      push_cast
      rfl
  rw [IsEquivalent, ← isLittleO_norm_norm] at hcast ⊢
  simpa only [Pi.sub_apply, ← Complex.ofReal_sub, Complex.norm_real] using hcast

/-- For every fixed ratio `r < 1`, the lower tail `P(a, r a)` of the Gamma law tends to `0` as
`a → +∞`. -/
theorem tendsto_regularizedGamma_fixedRatio_atTop {r : ℝ} (hr1 : r < 1) :
    Tendsto (fun a : ℝ => regularizedGamma a (r * a)) atTop (𝓝 0) := by
  rcases le_or_gt r 0 with hr0 | hr0
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    exact (regularizedGamma_eq_zero_of_nonpos_right a (mul_nonpos_of_nonpos_of_nonneg hr0 ha.le))
      |>.symm
  · refine (regularizedGamma_fixedRatio_isEquivalent hr0 hr1).symm.tendsto_nhds ?_
    have hrate : Real.log r + (1 - r) < 0 := by
      have hexp : Real.exp (Real.log r) < Real.exp (r - 1) := by
        rw [Real.exp_log hr0]
        linarith [Real.add_one_lt_exp (sub_ne_zero.mpr hr1.ne)]
      linarith [Real.exp_lt_exp.mp hexp]
    have hnum0 : Tendsto (fun a : ℝ => Real.exp ((Real.log r + (1 - r)) * a)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hrate)
    have hden_top : Tendsto
        (fun a : ℝ => Real.sqrt (2 * Real.pi) * (1 - r) * Real.sqrt a) atTop atTop :=
      Real.tendsto_sqrt_atTop.const_mul_atTop
        (mul_pos (Real.sqrt_pos.mpr (by positivity)) (sub_pos.mpr hr1))
    have hquot0 := hnum0.div_atTop hden_top
    refine hquot0.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with a _
    rw [Real.rpow_def_of_pos hr0, ← Real.exp_add]
    congr 2
    ring

end TauCeti

end
