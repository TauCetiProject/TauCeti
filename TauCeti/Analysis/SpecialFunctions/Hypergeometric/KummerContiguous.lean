/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric

/-!
# Contiguous relations of the regularized Kummer function

For the regularized Kummer function `𝐌(α, β, z) = ∑ (α)ₙ zⁿ / (n! Γ(β + n))`, which is Mathlib's
`Complex.regularizedHGFun {α} {β}`, this file proves two contiguous relations:

* `𝐌(α, β, z) = β 𝐌(α, β + 1, z) + α z 𝐌(α + 1, β + 2, z)`;
* `𝐌(α, β, z) = β 𝐌(α + 1, β + 1, z) − (β − α) z 𝐌(α + 1, β + 2, z)`.

Both hold for all complex `α`, `β` and `z`: since Mathlib's `1 / Γ` is entire, the poles of `Γ(β)`
need no exclusion. They are the relations that carry the Kummer functions `𝐌(k, a + n, z)` along
the three-term recurrence of the continued fraction of the lower incomplete Gamma function.

## Main results

* `Complex.regularizedHGFun_singleton_singleton_eq_mul_add_mul` — the first relation;
* `Complex.regularizedHGFun_singleton_singleton_eq_mul_sub_mul` — the second relation.

## References

* *NIST Digital Library of Mathematical Functions*, [§13.2](https://dlmf.nist.gov/13.2) and
  [§13.3(i)](https://dlmf.nist.gov/13.3.i).
-/

public section

open Polynomial
open scoped Nat

namespace Complex

/-- The three coefficients in the contiguous relations, written over the common factor
`g = 1 / Γ(β + n + 2)`. -/
private theorem regularizedHGFunCoeff_succ_eq_mul_inv_Gamma (α₁ α₂ α₃ β : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {α₁} {β} (n + 1) = (β + (n + 1)) *
        ((ascPochhammer ℂ (n + 1)).eval α₁ / (n + 1)!) * (Gamma (β + (n + 1) + 1))⁻¹ ∧
      regularizedHGFunCoeff {α₂} {β + 1} (n + 1) =
        (ascPochhammer ℂ (n + 1)).eval α₂ / (n + 1)! * (Gamma (β + (n + 1) + 1))⁻¹ ∧
      regularizedHGFunCoeff {α₃} {β + 2} n =
        (ascPochhammer ℂ n).eval α₃ / n ! * (Gamma (β + (n + 1) + 1))⁻¹ := by
  simp only [regularizedHGFunCoeff_singleton_singleton, div_eq_mul_inv, mul_inv]
  refine ⟨?_, ?_, ?_⟩
  · rw [Nat.cast_succ, one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (β + (n + 1))]
    ring
  · rw [Nat.cast_succ, show β + 1 + (n + 1) = β + (n + 1) + 1 by ring]
    ring
  · rw [show β + 2 + n = β + (n + 1) + 1 by ring]
    ring

/-- The coefficient identity behind `regularizedHGFun_singleton_singleton_eq_mul_add_mul`. -/
private theorem regularizedHGFunCoeff_singleton_singleton_succ_eq_mul_add_mul (α β : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {α} {β} (n + 1) =
      β * regularizedHGFunCoeff {α} {β + 1} (n + 1) +
        α * regularizedHGFunCoeff {α + 1} {β + 2} n := by
  obtain ⟨h₁, h₂, h₃⟩ := regularizedHGFunCoeff_succ_eq_mul_inv_Gamma α α (α + 1) β n
  rw [h₁, h₂, h₃, ascPochhammer_succ_left, Nat.factorial_succ]
  simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
  push_cast
  field_simp

/-- The coefficient identity behind `regularizedHGFun_singleton_singleton_eq_mul_sub_mul`. -/
private theorem regularizedHGFunCoeff_singleton_singleton_succ_eq_mul_sub_mul (α β : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {α} {β} (n + 1) =
      β * regularizedHGFunCoeff {α + 1} {β + 1} (n + 1) -
        (β - α) * regularizedHGFunCoeff {α + 1} {β + 2} n := by
  obtain ⟨h₁, h₂, h₃⟩ := regularizedHGFunCoeff_succ_eq_mul_inv_Gamma α (α + 1) (α + 1) β n
  rw [h₁, h₂, h₃, ascPochhammer_succ_eval n (α + 1), ascPochhammer_succ_left, Nat.factorial_succ]
  simp only [eval_mul, eval_X, eval_comp, eval_add, eval_one]
  push_cast
  field_simp
  ring

/-- `β / Γ(β + 1) = 1 / Γ(β)` gives the constant terms of both contiguous relations. -/
private theorem regularizedHGFunCoeff_zero_eq_mul (α α' β : ℂ) :
    regularizedHGFunCoeff {α} {β} 0 = β * regularizedHGFunCoeff {α'} {β + 1} 0 := by
  simp [regularizedHGFunCoeff_singleton_singleton,
    one_div_Gamma_eq_self_mul_one_div_Gamma_add_one β]

/-- The Kummer function is identified by the tail of its series after the constant term. -/
private theorem regularizedHGFun_singleton_eq_of_hasSum_succ {α β z S : ℂ}
    (h : HasSum (fun n => regularizedHGFunCoeff {α} {β} (n + 1) * z ^ (n + 1))
      (S - regularizedHGFunCoeff {α} {β} 0)) :
    regularizedHGFun {α} {β} z = S :=
  (hasSum_regularizedHGFun (a := {α}) (b := {β}) (by simp) z).unique
    ((hasSum_nat_add_iff' 1).mp (by simpa using h))

/-- A contiguous relation of the regularized Kummer function, for all complex `α`, `β` and `z`:
`𝐌(α, β, z) = β 𝐌(α, β + 1, z) + α z 𝐌(α + 1, β + 2, z)`. -/
theorem regularizedHGFun_singleton_singleton_eq_mul_add_mul (α β z : ℂ) :
    regularizedHGFun {α} {β} z =
      β * regularizedHGFun {α} {β + 1} z + α * z * regularizedHGFun {α + 1} {β + 2} z := by
  refine regularizedHGFun_singleton_eq_of_hasSum_succ ?_
  convert ((hasSum_nat_add_iff' 1).mpr ((hasSum_regularizedHGFun (a := {α}) (b := {β + 1})
    (by simp) z).mul_left β)).add ((hasSum_regularizedHGFun (a := {α + 1}) (b := {β + 2})
    (by simp) z).mul_left (α * z)) using 1
  · ext n
    rw [regularizedHGFunCoeff_singleton_singleton_succ_eq_mul_add_mul]
    ring
  · simp [regularizedHGFunCoeff_zero_eq_mul α α β]
    ring

/-- A contiguous relation of the regularized Kummer function, for all complex `α`, `β` and `z`:
`𝐌(α, β, z) = β 𝐌(α + 1, β + 1, z) − (β − α) z 𝐌(α + 1, β + 2, z)`. -/
theorem regularizedHGFun_singleton_singleton_eq_mul_sub_mul (α β z : ℂ) :
    regularizedHGFun {α} {β} z =
      β * regularizedHGFun {α + 1} {β + 1} z -
        (β - α) * z * regularizedHGFun {α + 1} {β + 2} z := by
  refine regularizedHGFun_singleton_eq_of_hasSum_succ ?_
  convert ((hasSum_nat_add_iff' 1).mpr ((hasSum_regularizedHGFun (a := {α + 1}) (b := {β + 1})
    (by simp) z).mul_left β)).sub ((hasSum_regularizedHGFun (a := {α + 1}) (b := {β + 2})
    (by simp) z).mul_left ((β - α) * z)) using 1
  · ext n
    rw [regularizedHGFunCoeff_singleton_singleton_succ_eq_mul_sub_mul]
    ring
  · simp [regularizedHGFunCoeff_zero_eq_mul α (α + 1) β]
    ring

end Complex
