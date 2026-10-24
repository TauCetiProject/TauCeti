/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import TauCeti.Algebra.Polynomial.Degree.Operations

/-!
# Eisenstein binomials and trinomials

For an ideal `𝓟` of a commutative ring, `X ^ n - C ϖ` is Eisenstein at `𝓟` when
`n` is positive and `ϖ` lies in `𝓟` but not in `𝓟 ^ 2`. Likewise `X ^ n + C a * X + C ϖ` is
Eisenstein at `𝓟` when moreover `a ∈ 𝓟` and `2 ≤ n`.

## Main results

* `TauCeti.isEisensteinAt_X_pow_sub_C` constructs Eisenstein binomials from ideal membership.
* `TauCeti.isEisensteinAt_X_pow_add_C_mul_X_add_C` constructs Eisenstein trinomials from ideal
  membership.
-/

public section

namespace TauCeti

open Polynomial

/-- `X ^ n - C ϖ` is Eisenstein at an ideal `𝓟` when `ϖ ∈ 𝓟` but `ϖ ∉ 𝓟 ^ 2`,
for positive `n`. -/
theorem isEisensteinAt_X_pow_sub_C {R : Type*} [CommRing R] {𝓟 : Ideal R}
    {ϖ : R} (hmem : ϖ ∈ 𝓟) (hnotmem : ϖ ∉ 𝓟 ^ 2)
    {n : ℕ} (hn : 0 < n) : (X ^ n - C ϖ).IsEisensteinAt 𝓟 := by
  have : Nontrivial R := nontrivial_of_ne ϖ 0 (by
    rintro rfl
    exact hnotmem (Ideal.zero_mem _))
  have h𝓟 : 𝓟 ≠ ⊤ := by
    rintro rfl
    exact hnotmem (by simp [Ideal.top_pow])
  refine (monic_X_pow_sub_C ϖ hn.ne').isEisensteinAt_of_mem_of_notMem h𝓟 ?_ ?_
  · intro i hi
    rw [natDegree_X_pow_sub_C] at hi
    by_cases hi0 : i = 0
    · subst i
      simpa [Ne.symm hn.ne'] using 𝓟.neg_mem hmem
    · simp [coeff_sub, coeff_X_pow, coeff_C, hi.ne, hi0]
  · simpa [coeff_sub, coeff_X_pow, Ne.symm hn.ne', Ideal.neg_mem_iff] using hnotmem

/-- `X ^ n + C a * X + C ϖ` is Eisenstein at an ideal `𝓟` when `a ∈ 𝓟`, `ϖ ∈ 𝓟` but
`ϖ ∉ 𝓟 ^ 2`, for `2 ≤ n`. -/
theorem isEisensteinAt_X_pow_add_C_mul_X_add_C {R : Type*} [CommSemiring R] {𝓟 : Ideal R}
    {a ϖ : R} (ha : a ∈ 𝓟) (hmem : ϖ ∈ 𝓟) (hnotmem : ϖ ∉ 𝓟 ^ 2) {n : ℕ} (hn : 2 ≤ n) :
    (X ^ n + C a * X + C ϖ).IsEisensteinAt 𝓟 := by
  have : Nontrivial R := nontrivial_of_ne ϖ 0 (by
    rintro rfl
    exact hnotmem (Ideal.zero_mem _))
  have h𝓟 : 𝓟 ≠ ⊤ := by
    rintro rfl
    exact hnotmem (by simp [Ideal.top_pow])
  have hmonic : (X ^ n + C a * X + C ϖ).Monic := by
    rw [add_assoc]
    exact monic_X_pow_add (degree_linear_le.trans_lt (by exact_mod_cast (by omega : 1 < n)))
  refine hmonic.isEisensteinAt_of_mem_of_notMem h𝓟 (fun {i} hi ↦ ?_) ?_ <;>
    simp only [coeff_add, coeff_X_pow, coeff_C_mul_X, coeff_C]
  · rw [natDegree_X_pow_add_C_mul_X_add_C a ϖ hn] at hi
    obtain rfl | rfl | hi2 : i = 0 ∨ i = 1 ∨ 2 ≤ i := by omega
    · simp [hi.ne, hmem]
    · simp [hi.ne, ha]
    · rw [ite_eq_right hi.ne, ite_eq_right (by omega), ite_eq_right (by omega), zero_add,
        zero_add]
      exact 𝓟.zero_mem
  · rw [ite_eq_right (by omega), zero_add]
    simpa using hnotmem

end TauCeti
