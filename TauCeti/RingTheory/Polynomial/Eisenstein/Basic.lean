/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!
# Eisenstein binomials

For an ideal `𝓟` of a commutative ring, `X ^ n - C ϖ` is Eisenstein at `𝓟` when
`n` is positive and `ϖ` lies in `𝓟` but not in `𝓟 ^ 2`.

## Main results

* `TauCeti.isEisensteinAt_X_pow_sub_C` constructs Eisenstein binomials from ideal membership.
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

end TauCeti
