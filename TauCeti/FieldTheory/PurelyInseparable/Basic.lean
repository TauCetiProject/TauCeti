/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.PurelyInseparable.Basic

import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.Algebra.Polynomial.Expand

/-!
# Polynomials over purely inseparable extensions

Over a purely inseparable extension `L / K` in exponential characteristic `p`, taking a common
`p`-power exponent across the coefficients of any `Q : L[X]` shows that some `Q ^ p ^ n` is mapped
from `K[X]` (`Polynomial.exists_map_eq_pow_expChar_pow_of_isPurelyInseparable`).
-/

public section

namespace Polynomial

/-- Over a purely inseparable extension `L / K` in exponential characteristic `p`, some `p ^ n`-th
power of any polynomial `Q : L[X]` is mapped from a polynomial over `K`. -/
theorem exists_map_eq_pow_expChar_pow_of_isPurelyInseparable {L : Type*} [CommRing L] [IsDomain L]
    (Q : L[X]) (K : Type*) [Field K] [Algebra K L] [IsPurelyInseparable K L]
    (p : ℕ) [ExpChar K p] :
    ∃ (n : ℕ) (R : K[X]), R.map (algebraMap K L) = Q ^ p ^ n := by
  classical
  have : ExpChar L p := expChar_of_injective_algebraMap (algebraMap K L).injective p
  choose m a ha using fun i ↦ IsPurelyInseparable.pow_mem K p (Q.coeff i)
  set n : ℕ := Q.support.sup m
  have hq : p ^ n ≠ 0 := (pow_pos (expChar_pos K p) n).ne'
  obtain ⟨Q₀, hQ₀⟩ : Q.map (iterateFrobenius L p n) ∈ (mapRingHom (algebraMap K L)).range :=
    (mem_map_range (algebraMap K L)).mpr fun i ↦ by
      rw [coeff_map, iterateFrobenius_def]
      by_cases hi : i ∈ Q.support
      · exact ⟨a i ^ p ^ (n - m i), by
          rw [map_pow, ha i, ← pow_mul, ← pow_add, Nat.add_sub_cancel' (Finset.le_sup hi)]⟩
      · exact ⟨0, by rw [notMem_support_iff.mp hi, zero_pow hq, map_zero]⟩
  refine ⟨n, expand K (p ^ n) Q₀, ?_⟩
  rw [coe_mapRingHom] at hQ₀
  rw [map_expand, hQ₀, ← map_expand, map_iterateFrobenius_expand]

end Polynomial
