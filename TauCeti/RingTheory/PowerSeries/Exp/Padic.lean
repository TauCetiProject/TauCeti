/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Exp.Basic
public import TauCeti.RingTheory.PowerSeries.GaussNorm
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers
import TauCeti.NumberTheory.Padics.Basic
import TauCeti.NumberTheory.Padics.Factorial
import TauCeti.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quantitative bounds for rescaled p-adic exponential series

Over any normed field extending `ℚ_[p]` isometrically, the coefficients of `exp(xX)` satisfy

`‖[Xⁿ] exp(xX)‖ cⁿ ≤ (p ^ (1 / (p - 1)) * ‖x‖ * c)ⁿ`.

This series is restricted at a nonnegative radius `c` if and only if
`‖x‖ * c < p ^ (-1 / (p - 1))`. Its Gauss norm is `1` on that disc, and the Gauss norm of
`exp(xX) - 1` is at most `p ^ (1 / (p - 1)) * ‖x‖ * c`. The strict radius condition includes
the dyadic case: there it reads `‖x‖ * c < 1 / 2`. At the critical radius the weighted
coefficients in degrees `p ^ k` have constant positive norm, proving failure of restrictedness.

For `x = log u`, these estimates give discs of radius greater than one for normal series
interpolating powers of sufficiently deep units. A quantitative Gauss norm, rather than just
convergence at integral arguments, is needed in interpolation estimates for these series.
Neither completeness nor finite dimension over `ℚ_[p]` is needed for the coefficient bounds.

## References

* K. Yu, *Linear forms in p-adic logarithms. II*, Compositio Math. 74 (1990), 15–113, §1.
* J.-P. Serre, *Local Fields*, Chapter II, §5.
-/

public section

namespace PowerSeries

open Filter Topology
open TauCeti.PowerSeries

variable {p : ℕ} [hp : Fact p.Prime] {K : Type*}
  [NormedField K] [Algebra ℚ K] [NormedAlgebra ℚ_[p] K]

/-- A geometric majorant for the weighted coefficients of a rescaled p-adic exponential.
The norm on the coefficient field restricts to the usual norm on `ℚ_[p]`. -/
theorem norm_coeff_rescale_exp_mul_pow_le (x : K) {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    ‖coeff n (rescale x (exp K))‖ * c ^ n ≤
      ((p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖x‖ * c) ^ n := by
  have hfac := inv_anti₀
    (Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos : (0 : ℝ) < p) _)
    (Padic.rpow_neg_div_le_norm_factorial (p := p) n)
  have hbound : ‖(n.factorial : K)‖⁻¹ ≤ ((p : ℝ) ^ ((p - 1 : ℝ)⁻¹)) ^ n := by
    rw [TauCeti.norm_natCast_eq_norm_padic (p := p)]
    simpa only [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p), inv_inv, div_eq_mul_inv,
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ p), mul_comm] using hfac
  simp only [coeff_rescale, coeff_exp, one_div, map_inv₀, map_natCast, norm_mul,
    norm_pow, norm_inv, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left hbound (mul_nonneg (pow_nonneg (norm_nonneg x) n)
    (pow_nonneg hc n))]

/-- The rescaled exponential is restricted on every closed disc strictly inside the p-adic
exponential disc. In particular the condition is strict also for `p = 2`. -/
theorem isRestricted_rescale_exp {x : K} {c : ℝ} (hc : 0 ≤ c)
    (hxc : ‖x‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    (rescale x (exp K)).IsRestricted c := by
  have hpos : 0 < (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  have hlt : (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖x‖ * c < 1 := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p)] at hxc
    simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne'] using
      mul_lt_mul_of_pos_left hxc hpos
  rw [isRestricted_iff']
  exact squeeze_zero (fun n ↦ mul_nonneg (norm_nonneg _) (pow_nonneg hc n))
    (norm_coeff_rescale_exp_mul_pow_le x hc)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) hlt)

/-- Along the degrees `p ^ k`, the weighted coefficients of the exponential at its critical
radius have constant positive norm. This is the obstruction to convergence at the boundary. -/
theorem norm_coeff_exp_mul_pow_prime_pow (k : ℕ) :
    ‖coeff (p ^ k) (exp K)‖ *
        ((p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) ^ (p ^ k) =
      (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hv := congrArg (Nat.cast : ℕ → ℝ)
    (TauCeti.sub_one_mul_padicValNat_factorial_pow p k)
  rw [Nat.cast_mul, Nat.cast_sub hp.out.one_le,
    Nat.cast_sub (Nat.one_le_pow _ _ hp.out.pos), Nat.cast_pow, Nat.cast_one] at hv
  rw [coeff_exp, one_div, map_inv₀, map_natCast, norm_inv,
    TauCeti.norm_natCast_eq_norm_padic (p := p),
    Padic.norm_natCast_eq_zpow (Nat.factorial_ne_zero _), ← Real.rpow_intCast,
    ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_neg hp0.le,
    ← Real.rpow_add hp0]
  congr 1
  push_cast
  field_simp
  nlinarith

/-- The exact criterion for a rescaled p-adic exponential to be restricted at a real radius.
The boundary is excluded for every prime, including `2`. The case `x = 0` is included. -/
theorem isRestricted_rescale_exp_iff {x : K} {c : ℝ} (hc : 0 ≤ c) :
    (rescale x (exp K)).IsRestricted c ↔
      ‖x‖ * c < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) := by
  refine ⟨fun hf ↦ ?_, isRestricted_rescale_exp hc⟩
  by_contra hlt
  have hle := not_lt.mp hlt
  have hρ : 0 < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  have hbound (k : ℕ) : (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹) ≤
      ‖coeff (p ^ k) (rescale x (exp K))‖ * c ^ (p ^ k) := by
    calc
      _ = ‖coeff (p ^ k) (exp K)‖ *
          ((p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) ^ (p ^ k) :=
        (norm_coeff_exp_mul_pow_prime_pow (K := K) k).symm
      _ ≤ ‖coeff (p ^ k) (exp K)‖ * (‖x‖ * c) ^ (p ^ k) := by gcongr
      _ = _ := by simp [coeff_rescale, norm_mul, norm_pow, mul_pow, mul_comm, mul_assoc]
  have hlim := ((isRestricted_iff' c _).mp hf).comp
    (tendsto_pow_atTop_atTop_of_one_lt hp.out.one_lt)
  obtain ⟨k, hk⟩ := (hlim.eventually (gt_mem_nhds hρ)).exists
  exact (not_lt_of_ge (hbound k)) hk

/-- The Gauss norm of `exp(xX)` is exactly one as long as the coefficient majorant has ratio
at most one. This bound also applies at the boundary, without asserting restrictedness there. -/
theorem gaussNorm_rescale_exp {x : K} {c : ℝ} (hc : 0 ≤ c)
    (hxc : ‖x‖ * c ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    (rescale x (exp K)).gaussNorm norm c = 1 := by
  have hpos : 0 < (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  have hle : (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖x‖ * c ≤ 1 := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p)] at hxc
    simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne'] using
      mul_le_mul_of_nonneg_left hxc hpos.le
  have h := gaussNorm_eq_of_forall_le (s := 0) (a := rescale x (exp K)) (c := c)
    (v := norm) fun n ↦ (norm_coeff_rescale_exp_mul_pow_le x hc n).trans
      (by simpa using pow_le_one₀ (by positivity) hle (n := n))
  simpa using h

/-- On a disc in the p-adic exponential range, subtracting the constant term leaves Gauss norm
at most the geometric ratio. This is a uniform estimate for the distance from `exp(xX)` to `1`.
-/
theorem gaussNorm_rescale_exp_sub_one_le {x : K} {c : ℝ} (hc : 0 ≤ c)
    (hxc : ‖x‖ * c ≤ (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    (rescale x (exp K) - 1).gaussNorm norm c ≤
      (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖x‖ * c := by
  have hpos : 0 < (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  have hle : (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖x‖ * c ≤ 1 := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p)] at hxc
    simpa only [← mul_assoc, mul_inv_cancel₀ hpos.ne'] using
      mul_le_mul_of_nonneg_left hxc hpos.le
  rw [gaussNorm_eq]
  refine ciSup_le fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [coeff_zero_eq_constantCoeff, map_sub, constantCoeff_rescale, constantCoeff_exp,
      constantCoeff_one, sub_self, norm_zero, pow_zero, mul_one]
    positivity
  · simpa [coeff_one, hn] using (norm_coeff_rescale_exp_mul_pow_le x hc n).trans
      (pow_le_pow_of_le_one (by positivity) hle (Nat.one_le_iff_ne_zero.mpr hn))

end PowerSeries
