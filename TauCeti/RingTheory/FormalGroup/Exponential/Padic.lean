/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.Exponential.Norm
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.NumberTheory.Padics.PadicIntegers
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence of integral formal exponentials

The formal exponential of a formal group over `ℤ_p`, after extension to `ℚ_p`, converges
absolutely for `‖t‖ < p ^ (-1 / (p - 1))`. The factorial denominator estimate for its
coefficients and Legendre's bound give a geometric majorant on this disc. This is the disc
on which the exponential can be used to invert an evaluated formal logarithm; the
exponential need not converge throughout the open unit disc.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4–6.
-/

public section

namespace FormalGroup

variable {p : ℕ} [hp : Fact p.Prime] (F : FormalGroup ℤ_[p])

/-- A geometric bound for the coefficients of an integral formal exponential. -/
theorem norm_coeff_exp_le (n : ℕ) :
    ‖PowerSeries.coeff n (F.map (algebraMap ℤ_[p] ℚ_[p])).exp‖ ≤
      ((p : ℝ) ^ ((p - 1 : ℝ)⁻¹)) ^ n := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hpm : (0 : ℝ) < p - 1 := sub_pos.mpr hp1
  have hv : (padicValNat p n.factorial : ℝ) ≤ (p - 1 : ℝ)⁻¹ * n := by
    have h : (p - 1) * padicValNat p n.factorial ≤ n := by
      by_cases hn : n = 0
      · simp [hn]
      · exact (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p hn).le
    have h' : ((p - 1 : ℕ) : ℝ) * padicValNat p n.factorial ≤ n := by
      exact_mod_cast h
    rw [Nat.cast_sub hp.out.one_le, Nat.cast_one] at h'
    exact (le_inv_mul_iff₀ hpm).mpr h'
  refine (F.norm_coeff_exp_le_inv_norm_factorial (algebraMap ℤ_[p] ℚ_[p])
    (fun a ↦ PadicInt.norm_le_one a) n).trans ?_
  rw [Padic.norm_natCast_eq_zpow n.factorial_ne_zero, zpow_neg, inv_inv, zpow_natCast,
    ← Real.rpow_natCast (p : ℝ) (padicValNat p n.factorial),
    ← Real.rpow_mul_natCast (by positivity : (0 : ℝ) ≤ p)]
  exact Real.rpow_le_rpow_of_exponent_le hp1.le hv

/-- The formal exponential of an integral formal group converges absolutely on the standard
p-adic exponential disc, including for `p = 2`. -/
theorem summable_norm_coeff_exp_mul_pow {t : ℚ_[p]}
    (ht : ‖t‖ < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    Summable fun n : ℕ ↦
      ‖PowerSeries.coeff n (F.map (algebraMap ℤ_[p] ℚ_[p])).exp * t ^ n‖ := by
  have hpos : 0 < (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hp.out.pos) _
  have ht' : (p : ℝ) ^ ((p - 1 : ℝ)⁻¹) * ‖t‖ < 1 := by
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ p)] at ht
    have h := mul_lt_mul_of_pos_left ht hpos
    simpa [hpos.ne'] using h
  refine (summable_geometric_of_lt_one (mul_nonneg hpos.le (norm_nonneg t)) ht').of_nonneg_of_le
    (fun n ↦ norm_nonneg _) fun n ↦ ?_
  rw [norm_mul, norm_pow, mul_pow]
  exact mul_le_mul_of_nonneg_right (F.norm_coeff_exp_le n) (by positivity)

/-- The exponential series of an integral formal group is summable on its p-adic convergence
disc. -/
theorem summable_coeff_exp_mul_pow {t : ℚ_[p]}
    (ht : ‖t‖ < (p : ℝ) ^ (-(p - 1 : ℝ)⁻¹)) :
    Summable fun n : ℕ ↦
      PowerSeries.coeff n (F.map (algebraMap ℤ_[p] ℚ_[p])).exp * t ^ n :=
  (F.summable_norm_coeff_exp_mul_pow ht).of_norm

end FormalGroup
