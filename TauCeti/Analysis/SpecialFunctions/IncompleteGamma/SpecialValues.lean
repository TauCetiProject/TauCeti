/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Lower
public import TauCeti.Analysis.SpecialFunctions.IncompleteGamma.Upper

/-!
# Special values of the complex incomplete Gamma functions

At a positive integer parameter `n + 1` the incomplete Gamma functions are elementary: with the
truncated exponential series `e_n(z) = ∑_{k=0}^n zᵏ / k!` (DLMF 8.4.11), for every complex `z`,

* `γ(n + 1, z) = n! (1 − e^{−z} e_n(z))` (DLMF 8.4.7),
* `Γ(n + 1, z) = n! e^{−z} e_n(z)` (DLMF 8.4.8),
* `P(n + 1, z) = 1 − e^{−z} e_n(z)` (DLMF 8.4.9),
* `Q(n + 1, z) = e^{−z} e_n(z)` (DLMF 8.4.10).

The case `n = 0` of the upper function, `Γ(1, z) = e^{−z}` (DLMF 8.4.5), is
`Complex.upperIncompleteGamma_one_left`.

## Main results

* `Complex.regularizedGamma_natCast_add_one`, `Complex.regularizedGammaQ_natCast_add_one`,
  `Complex.lowerIncompleteGamma_natCast_add_one`: DLMF 8.4.9, 8.4.10 and 8.4.7;
* `Complex.upperIncompleteGamma_natCast_add_one`: DLMF 8.4.8;
* `Complex.upperIncompleteGamma_three_left`: `Γ(3, z) = (z² + 2z + 2) e^{−z}`;
* `Complex.upperIncompleteGamma_natCast_add_one_zero_right`: `Γ(n + 1, 0) = n!`.

## Implementation notes

The formulas hold for every `z`, including the branch cut and `z = 0`, so no hypothesis on `z`
is needed. To evaluate an incomplete Gamma function at a positive integer parameter, write the
parameter as `(n : ℂ) + 1` and rewrite with the theorem for that function: the result is
expressed through the finite exponential sum `e^{−z} ∑_{k=0}^n zᵏ / k!`, which
`norm_num [Finset.sum_range_succ]` expands for a concrete `n`, as in
`Complex.upperIncompleteGamma_three_left`.

## References

* NIST Digital Library of Mathematical Functions, §8.4, <https://dlmf.nist.gov/8.4>.
-/

public section

noncomputable section

open Finset MeasureTheory Set
open scoped Nat

namespace Complex

/-- **DLMF 8.4.9**: `P(n + 1, z) = 1 − e^{−z} ∑_{k=0}^n zᵏ / k!` for every `z`. -/
theorem regularizedGamma_natCast_add_one (n : ℕ) (z : ℂ) :
    regularizedGamma (n + 1) z = 1 - cexp (-z) * ∑ k ∈ range (n + 1), z ^ k / k ! := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h := tricomiIncompleteGamma_eq_mul_tricomiIncompleteGamma_add_one ((n : ℂ) + 1) z
    rw [← Nat.cast_add_one, Gamma_nat_eq_factorial, Nat.cast_add_one] at h
    rw [regularizedGamma_def, ← Nat.cast_add_one, cpow_natCast, Nat.cast_add_one] at ih ⊢
    rw [sum_range_succ, mul_add, ← sub_sub, ← ih, h, Nat.cast_add_one n]
    ring

/-- **DLMF 8.4.10**: `Q(n + 1, z) = e^{−z} ∑_{k=0}^n zᵏ / k!` for every `z`. -/
theorem regularizedGammaQ_natCast_add_one (n : ℕ) (z : ℂ) :
    regularizedGammaQ (n + 1) z = cexp (-z) * ∑ k ∈ range (n + 1), z ^ k / k ! := by
  rw [regularizedGammaQ_def, regularizedGamma_natCast_add_one, sub_sub_cancel]

/-- **DLMF 8.4.7**: `γ(n + 1, z) = n! (1 − e^{−z} ∑_{k=0}^n zᵏ / k!)` for every `z`. -/
theorem lowerIncompleteGamma_natCast_add_one (n : ℕ) (z : ℂ) :
    lowerIncompleteGamma (n + 1) z =
      n ! * (1 - cexp (-z) * ∑ k ∈ range (n + 1), z ^ k / k !) := by
  rw [lowerIncompleteGamma_def, regularizedGamma_natCast_add_one, Gamma_nat_eq_factorial]

/-- `Γ(n + 1, 0) = n!`. -/
@[simp]
theorem upperIncompleteGamma_natCast_add_one_zero_right (n : ℕ) :
    upperIncompleteGamma (n + 1) 0 = n ! := by
  rw [upperIncompleteGamma_zero_right (by simp only [add_re, natCast_re, one_re]; positivity),
    Gamma_nat_eq_factorial]

/-- **DLMF 8.4.8**: `Γ(n + 1, z) = n! e^{−z} ∑_{k=0}^n zᵏ / k!` for every `z`, including the
branch cut. -/
theorem upperIncompleteGamma_natCast_add_one (n : ℕ) (z : ℂ) :
    upperIncompleteGamma (n + 1) z = n ! * cexp (-z) * ∑ k ∈ range (n + 1), z ^ k / k ! := by
  have hint (m : ℕ) : IntegrableOn (fun t : ℝ => (t : ℂ) ^ m * cexp (-(t : ℂ))) (Ioi 0) := by
    refine (GammaIntegral_convergent (s := (m : ℂ) + 1)
      (by simp only [add_re, natCast_re, one_re]; positivity)).congr_fun (fun t _ => ?_)
      measurableSet_Ioi
    simp [cpow_natCast, ofReal_exp, mul_comm]
  have hval (m : ℕ) : ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ m * cexp (-(t : ℂ)) = m ! := by
    simpa [upperIncompleteGamma_def, cpow_natCast] using
      upperIncompleteGamma_natCast_add_one_zero_right m
  rw [upperIncompleteGamma_def, add_sub_cancel_right]
  simp_rw [cpow_natCast, add_pow, sum_mul]
  have hterm (k : ℕ) :
      (fun t : ℝ => z ^ k * (t : ℂ) ^ (n - k) * (n.choose k) * cexp (-(t : ℂ))) =
        fun t : ℝ => z ^ k * (n.choose k) * ((t : ℂ) ^ (n - k) * cexp (-(t : ℂ))) := by
    ext t
    ring
  rw [integral_finsetSum _ fun k _ => hterm k ▸ (hint (n - k)).const_mul _, mul_sum, mul_sum]
  refine sum_congr rfl fun k hk => ?_
  rw [hterm k, integral_const_mul, hval]
  have hc := Nat.choose_mul_factorial_mul_factorial (mem_range_succ_iff.mp hk)
  have hfac : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [← hc]
  push_cast
  field_simp

/-- `Γ(3, z) = (z² + 2z + 2) e^{−z}` for every `z`. -/
theorem upperIncompleteGamma_three_left (z : ℂ) :
    upperIncompleteGamma 3 z = (z ^ 2 + 2 * z + 2) * cexp (-z) := by
  have h := upperIncompleteGamma_natCast_add_one 2 z
  norm_num [sum_range_succ] at h
  rw [h]
  ring

end Complex
