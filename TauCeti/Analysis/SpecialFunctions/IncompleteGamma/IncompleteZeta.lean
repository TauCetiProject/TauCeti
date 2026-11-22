/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
public import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import TauCeti.Analysis.SpecialFunctions.Exp.LatticeSum
import TauCeti.Analysis.SpecialFunctions.Gamma.IntegralComplexRate
import TauCeti.Analysis.SpecialFunctions.Pow.Summable

/-!
# The incomplete Riemann zeta function

For `1 < Re s` and `0 ≤ x`, expanding `1/(e^t − 1) = ∑_{k ≥ 1} e^{−kt}` under the integral gives
the incomplete Riemann zeta function as a series of regularized incomplete Gamma functions,
`Γ(s)⁻¹ ∫₀ˣ t^{s−1}/(e^t − 1) dt = ∑_{k ≥ 1} k^{−s} P(s, kx)` (DLMF 8.22.2). As `x → ∞` the
left side tends to `Γ(s)⁻¹ ∫₀^∞ t^{s−1}/(e^t − 1) dt = ζ(s)` (DLMF 8.22.3, 25.5.1).

## Main results

* `TauCeti.hasSum_setIntegral_cpow_mul_exp_neg_mul`: termwise integration of
  `t^{s−1} e^{(1−c)t}/(e^t − 1) = ∑_{k ≥ 0} t^{s−1} e^{−(k+c)t}` over any subset of `(0, ∞)` for
  `1 < Re s` and `0 < Re c`;
* `TauCeti.integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta`: DLMF 25.5.1,
  `∫₀^∞ t^{s−1}/(e^t − 1) dt = Γ(s) ζ(s)` for `1 < Re s`;
* `TauCeti.hasSum_cpow_neg_mul_regularizedGamma` and
  `TauCeti.inv_Gamma_mul_intervalIntegral_cpow_div_exp_sub_one_eq_tsum`: DLMF 8.22.2;
* `TauCeti.tendsto_tsum_cpow_neg_mul_regularizedGamma_atTop`: DLMF 8.22.3, the limit
  `∑_{k ≥ 1} k^{−s} P(s, kx) → ζ(s)` as `x → ∞`;
* `TauCeti.integral_Ioi_div_exp_sub_one_eq_pi_sq_div_six`: `∫₀^∞ t/(e^t − 1) dt = π²/6`.

## Implementation notes

The series are indexed by `k : ℕ`. In the statements of DLMF 8.22.2–8.22.3 the term `k = 0`
vanishes because `0^{−s} = 0` for `s ≠ 0`, so they match `zeta_eq_tsum_one_div_nat_cpow`.
Each finite integral is rescaled to a lower incomplete Gamma function by
`TauCeti.intervalIntegral_cpow_mul_exp_neg_mul`.

## References

* NIST Digital Library of Mathematical Functions, §8.22 and §25.5,
  <https://dlmf.nist.gov/8.22>, <https://dlmf.nist.gov/25.5>.

The proofs are new. For DLMF 25.5.1, the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/Zeta/IntegralReps/ElementaryKernels.lean`,
was consulted for orientation; no proof is copied from it.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped Real Topology

namespace TauCeti

open Complex

/-- Expansion of `exp ((1 - c) * t) / (exp t - 1)` under the integral: for `1 < Re s`,
`0 < Re c`, and every set `A ⊆ (0, ∞)`,
`∫_A t^{s−1} e^{(1−c)t}/(e^t − 1) dt = ∑_{k ≥ 0} ∫_A t^{s−1} e^{−(k+c)t} dt`. -/
theorem hasSum_setIntegral_cpow_mul_exp_neg_mul {s c : ℂ} (hs : 1 < s.re) (hc : 0 < c.re)
    {A : Set ℝ} (hA0 : A ⊆ Ioi 0) :
    HasSum (fun k : ℕ => ∫ t in A, (t : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + c) * t)))
      (∫ t in A, (t : ℂ) ^ (s - 1) * (cexp ((1 - c) * t) / (cexp t - 1))) := by
  have hs0 : 0 < s.re := by linarith
  have hk (k : ℕ) : 0 < ((k : ℂ) + c).re := by
    rw [add_re, natCast_re]
    positivity
  have hF (k : ℕ) : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + c) * t)))
      (Ioi 0) := integrableOn_cpow_mul_exp_neg_mul_Ioi hs0 (hk k)
  have hsum :
      Summable fun k : ℕ => ∫ t in A, ‖(t : ℂ) ^ (s - 1) * cexp (-(((k : ℂ) + c) * t))‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun t => norm_nonneg _)
      (fun k => setIntegral_mono_set (hF k).norm (ae_of_all _ fun t => norm_nonneg _)
        (ae_of_all _ hA0)) ?_
    have h := (summable_norm_natCast_add_cpow_neg hs (c.re : ℂ)).mul_left (Real.Gamma s.re)
    refine h.congr fun k => ?_
    have hre_pos : 0 < (k : ℝ) + c.re := by positivity
    rw [integral_norm_cpow_mul_exp_neg_mul_Ioi hs0 (hk k)]
    have hcpow : ‖((k : ℂ) + (c.re : ℂ)) ^ (-s)‖ = (((k : ℂ) + c).re⁻¹) ^ s.re := by
      have hsum_eq : (k : ℂ) + (c.re : ℂ) = (((k : ℝ) + c.re : ℝ) : ℂ) := by push_cast; ring
      rw [hsum_eq, norm_cpow_eq_rpow_re_of_pos hre_pos, neg_re, Real.rpow_neg hre_pos.le,
        ← Real.inv_rpow hre_pos.le, add_re, natCast_re]
    simp only [hcpow, ← one_div, mul_comm (Real.Gamma s.re)]
  convert hasSum_integral_of_summable_integral_norm (fun k => (hF k).mono_set hA0) hsum using 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hA0 (ae_restrict_mem measurableSet_Ioi)]
    with t ht0
  have htsum := ((hasSum_exp_neg_natCast_add_one_mul (z := t) (by simpa using ht0)).mul_left
    ((t : ℂ) ^ (s - 1) * cexp ((1 - c) * t))).tsum_eq
  rw [mul_one_div, ← mul_div_assoc'] at htsum
  rw [← htsum]
  refine tsum_congr fun k => ?_
  rw [mul_assoc, ← exp_add]
  congr 2
  ring

/-- For `1 < Re s`, `t ↦ t^{s−1}/(e^t − 1)` is integrable on `(0, ∞)`. -/
theorem integrableOn_cpow_div_exp_sub_one {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (s - 1) / (cexp t - 1)) (Ioi 0) := by
  refine ((Real.GammaIntegral_convergent (s := s.re - 1) (by linarith)).add
    (Real.GammaIntegral_convergent (s := s.re) (by linarith))).mono'
    (by fun_prop : Measurable fun t : ℝ => (t : ℂ) ^ (s - 1) / (cexp t - 1)).aestronglyMeasurable
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : (0 : ℝ) < t := ht
  have hE : 0 < Real.exp t - 1 := by linarith [Real.add_one_lt_exp ht0.ne']
  have hP : 0 < t ^ (s.re - 1 - 1) := Real.rpow_pos_of_pos ht0 _
  -- `(1 + t) e^{−t} ≤ 1` is the inequality that makes the bound work
  have key : (1 + t) * Real.exp (-t) ≤ 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos t)]
    linarith [Real.add_one_le_exp t]
  have hee : Real.exp (-t) * Real.exp t = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have hpow : t ^ (s.re - 1) = t ^ (s.re - 1 - 1) * t := by
    rw [← Real.rpow_add_one ht0.ne']
    ring_nf
  have hn : ‖cexp t - 1‖ = Real.exp t - 1 := by
    rw [← ofReal_exp, ← ofReal_one, ← ofReal_sub, norm_real, Real.norm_of_nonneg hE.le]
  rw [norm_div, norm_cpow_eq_rpow_re_of_pos ht0, hn, sub_re, one_re, div_le_iff₀ hE, Pi.add_apply,
    hpow]
  have hexp : (Real.exp (-t) * t ^ (s.re - 1 - 1) + Real.exp (-t) * (t ^ (s.re - 1 - 1) * t)) *
      (Real.exp t - 1) = t ^ (s.re - 1 - 1) * (1 + t) - t ^ (s.re - 1 - 1) *
        ((1 + t) * Real.exp (-t)) := by
    linear_combination t ^ (s.re - 1 - 1) * (1 + t) * hee
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_left key hP.le]

/-- **DLMF 25.5.1**: `∫₀^∞ t^{s−1}/(e^t − 1) dt = Γ(s) ζ(s)` for `1 < Re s`. -/
theorem integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (s - 1) / (cexp t - 1) = Gamma s * riemannZeta s := by
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs, ← tsum_mul_left]
  have hsum := hasSum_setIntegral_cpow_mul_exp_neg_mul hs (c := 1) one_pos subset_rfl
  simp only [sub_self, zero_mul, exp_zero, one_div, ← div_eq_mul_inv] at hsum
  refine hsum.tsum_eq.symm.trans (tsum_congr fun k => ?_)
  have hk : 0 < ((k : ℂ) + 1).re := by
    rw [add_re, natCast_re, one_re]
    positivity
  rw [integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos (by linarith) hk, cpow_neg, one_div]

/-- **DLMF 8.22.2**, as a `HasSum`: for `1 < Re s` and `0 ≤ x`, the series
`∑_{k ≥ 1} k^{−s} P(s, kx)` converges to `Γ(s)⁻¹ ∫₀ˣ t^{s−1}/(e^t − 1) dt`. -/
theorem hasSum_cpow_neg_mul_regularizedGamma {s : ℂ} (hs : 1 < s.re) {x : ℝ} (hx : 0 ≤ x) :
    HasSum (fun k : ℕ => (k : ℂ) ^ (-s) * regularizedGamma s (k * x))
      ((Gamma s)⁻¹ * ∫ t in (0 : ℝ)..x, (t : ℂ) ^ (s - 1) / (cexp t - 1)) := by
  have hs0 : 0 < s.re := by linarith
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos hs0
  have hs1 : -s ≠ 0 := neg_ne_zero.mpr fun h => by simp [h] at hs0
  refine (hasSum_nat_add_iff' 1).mp ?_
  rw [Finset.sum_range_one, Nat.cast_zero, zero_cpow hs1, zero_mul, sub_zero,
    intervalIntegral.integral_of_le hx]
  have hsum := (hasSum_setIntegral_cpow_mul_exp_neg_mul hs (c := 1) one_pos
    (A := Ioc 0 x) Ioc_subset_Ioi_self).mul_left (Gamma s)⁻¹
  simp only [sub_self, zero_mul, exp_zero, one_div, ← div_eq_mul_inv] at hsum
  convert hsum using 1
  funext k
  have h := intervalIntegral_cpow_mul_exp_neg_mul hs0 (Nat.cast_add_one_ne_zero k) hx
  rw [intervalIntegral.integral_of_le hx] at h
  push_cast at h ⊢
  rw [h, lowerIncompleteGamma_def]
  field_simp

/-- **DLMF 8.22.2**: for `1 < Re s` and `0 ≤ x`,
`Γ(s)⁻¹ ∫₀ˣ t^{s−1}/(e^t − 1) dt = ∑_{k ≥ 1} k^{−s} P(s, kx)`. -/
theorem inv_Gamma_mul_intervalIntegral_cpow_div_exp_sub_one_eq_tsum {s : ℂ} (hs : 1 < s.re)
    {x : ℝ} (hx : 0 ≤ x) :
    (Gamma s)⁻¹ * ∫ t in (0 : ℝ)..x, (t : ℂ) ^ (s - 1) / (cexp t - 1) =
      ∑' k : ℕ, (k : ℂ) ^ (-s) * regularizedGamma s (k * x) :=
  (hasSum_cpow_neg_mul_regularizedGamma hs hx).tsum_eq.symm

/-- **DLMF 8.22.3**: for `1 < Re s`, `∑_{k ≥ 1} k^{−s} P(s, kx) → ζ(s)` as `x → ∞`. -/
theorem tendsto_tsum_cpow_neg_mul_regularizedGamma_atTop {s : ℂ} (hs : 1 < s.re) :
    Tendsto (fun x : ℝ => ∑' k : ℕ, (k : ℂ) ^ (-s) * regularizedGamma s (k * x)) atTop
      (𝓝 (riemannZeta s)) := by
  have hG : Gamma s ≠ 0 := Gamma_ne_zero_of_re_pos (by linarith)
  have h := (intervalIntegral_tendsto_integral_Ioi 0 (integrableOn_cpow_div_exp_sub_one hs)
    tendsto_id).const_mul (Gamma s)⁻¹
  rw [integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta hs, inv_mul_cancel_left₀ hG] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with x hx
  exact inv_Gamma_mul_intervalIntegral_cpow_div_exp_sub_one_eq_tsum hs hx

/-- DLMF 8.22.3 at `s = 2`: `∫₀^∞ t/(e^t − 1) dt = π²/6`. -/
theorem integral_Ioi_div_exp_sub_one_eq_pi_sq_div_six :
    ∫ t in Ioi (0 : ℝ), t / (Real.exp t - 1) = π ^ 2 / 6 := by
  have h := integral_cpow_div_exp_sub_one_eq_Gamma_mul_riemannZeta (s := 2) (by norm_num)
  rw [Complex.Gamma_ofNat_eq_factorial, riemannZeta_two, Nat.factorial_one,
    Nat.cast_one, one_mul] at h
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  push_cast
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  norm_num

end TauCeti
