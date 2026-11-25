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

/-- The rising product `(j + 1) (j + 2) ⋯ (j + k)` is `k ! * (k + j).choose j`. -/
private theorem prod_range_add_add_one_eq (j k : ℕ) :
    ∏ i ∈ Finset.range k, (j + 1 + i) = k.factorial * (k + j).choose j := by
  rw [← Nat.ascFactorial_eq_prod_range, Nat.ascFactorial_eq_factorial_mul_choose, Nat.add_comm j k,
    Nat.choose_symm_add]

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
  have hneg (i : ℕ) : ((↑(-(↑(j + 1) : ℤ)) : 𝕜) - ↑i) = -((j + 1 + i : ℕ) : 𝕜) := by
    push_cast
    ring
  have hprod : (∏ i ∈ Finset.range k, ((↑(-(↑(j + 1) : ℤ)) : 𝕜) - ↑i)) =
      (-1 : 𝕜) ^ k * ↑(k.factorial * (k + j).choose j) := by
    simp only [hneg, Finset.prod_neg, Finset.card_range, ← prod_range_add_add_one_eq, Nat.cast_prod]
  rw [hexp, hprod, zpow_neg, zpow_natCast, Nat.cast_mul]
  have hk : (k.factorial : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hsq : (-1 : 𝕜) ^ k * (-1) ^ k = 1 := by rw [← mul_pow]; norm_num
  linear_combination (↑((k + j).choose j) * c / (z - ρ) ^ (k + j + 1) : 𝕜) *
    ((k.factorial : 𝕜) * (k.factorial : 𝕜)⁻¹ * hsq + mul_inv_cancel₀ hk)

end TauCeti
