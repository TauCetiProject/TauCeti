/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Choose.Basic

/-!
# Taylor coefficients of reciprocal powers

The normalized iterated derivatives of a shifted reciprocal power are binomial coefficients
scaled by powers of the displacement from the singularity. The normalization uses the variable
`t = z - s` for a Taylor expansion about `z`.
-/

public section

namespace TauCeti

/-- The degree-`k` coefficient of `t ↦ c / (z - t - ρ) ^ (j + 1)` at `0`, expressed as
an iterated derivative at `z`. The identity also holds at `z = ρ` by the conventions for
inversion and differentiation at zero. -/
theorem neg_one_pow_mul_iteratedDeriv_div_factorial_const_div_sub_pow
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
    (j k : ℕ) (c z ρ : 𝕜) :
    (-1 : 𝕜) ^ k * (iteratedDeriv k (fun s ↦ c / (s - ρ) ^ (j + 1)) z / (k.factorial : 𝕜)) =
      (↑((k + j).choose j) : 𝕜) * c / (z - ρ) ^ (k + j + 1) := by
  have hf : (fun s : 𝕜 ↦ c / (s - ρ) ^ (j + 1)) =
      fun s ↦ c * (s - ρ) ^ (-(↑(j + 1) : ℤ)) := by
    simp only [zpow_neg, zpow_natCast, div_eq_mul_inv]
  have hshift := congrFun (iteratedDeriv_comp_sub_const (n := k)
    (f := fun x : 𝕜 ↦ x ^ (-(↑(j + 1) : ℤ))) (s := ρ)) z
  rw [hf, iteratedDeriv_const_mul_field, hshift, iteratedDeriv_eq_iterate, iter_deriv_zpow]
  have hexp : -(↑(j + 1) : ℤ) - ↑k = -(↑(k + j + 1) : ℤ) := by omega
  have hprod : (∏ i ∈ Finset.range k, ((↑(-(↑(j + 1) : ℤ)) : 𝕜) - ↑i)) =
      (-1 : 𝕜) ^ k * ↑(k.factorial * (k + j).choose j) := by
    rw [← Nat.choose_symm_add, Nat.add_comm k j, ← Nat.ascFactorial_eq_factorial_mul_choose,
      Nat.ascFactorial_eq_prod_range, Nat.cast_prod]
    simpa only [Finset.prod_neg, Finset.card_range] using
      (Finset.prod_congr (rfl : Finset.range k = Finset.range k) (fun i _ ↦ by
        push_cast
        ring) : (∏ i ∈ Finset.range k, ((↑(-(↑(j + 1) : ℤ)) : 𝕜) - ↑i)) =
          ∏ i ∈ Finset.range k, -(↑(j + 1 + i) : 𝕜))
  rw [hexp, hprod, zpow_neg, zpow_natCast, Nat.cast_mul]
  have hk : (k.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    (-1 : 𝕜) ^ k * (c * (((-1) ^ k * (↑k.factorial * ↑((k + j).choose j))) *
        ((z - ρ) ^ (k + j + 1))⁻¹) * (↑k.factorial)⁻¹) =
        ((-1 : 𝕜) ^ k * (-1) ^ k) * (↑k.factorial * (↑k.factorial)⁻¹) *
          (↑((k + j).choose j) * c * ((z - ρ) ^ (k + j + 1))⁻¹) := by ring
    _ = _ := by simp [← mul_pow, hk]

end TauCeti
