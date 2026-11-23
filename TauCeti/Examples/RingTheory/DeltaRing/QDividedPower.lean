/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.DeltaRing.QDividedPower

/-!
# Checks for the q-divided power operation

Over `ℤ` with its unique `δ`-structure and `q = 1`, so that `[p]_q = p`: the prime `p` lies in
`N(ℤ) = φ⁻¹(p ℤ)` and `γ p = p ^ (p - 1)`, the value `p ^ p / p` of the divided power operation;
at `p = 2` this is `γ 2 = 2`, and the congruence `δ [p]_q ≡ 1` reads `δ 2 = -1 ≡ 1` modulo `2`.
-/

namespace TauCeti.QDividedPowerChecks

open DeltaRing QCrys

/-- In `ℤ` with `q = 1`, `γ p = p ^ (p - 1)`. -/
example (p : ℕ) [hp : Fact p.Prime] : gamma p (1 : ℤ) p = p ^ (p - 1) := by
  have hreg : IsRegular (qInteger (1 : ℤ) p) := by
    rw [qInteger_one_left]
    exact isRegular_iff_ne_zero.mpr (Nat.cast_ne_zero.mpr hp.out.ne_zero)
  refine gamma_eq_of_mul_eq hreg ?_
  have h := frobenius_sub_pow (p := p) (p : ℤ)
  have hpow : (p : ℤ) ^ p = p * p ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hp.out.one_le]
  rw [frobenius_int, RingHom.id_apply] at h ⊢
  rw [qInteger_one_left]
  linear_combination -h - hpow

/-- In `ℤ` with `q = 1`, the prime `p` lies in `N(ℤ)`: its Frobenius `p` is divisible by
`[p]_1 = p`. -/
example (p : ℕ) [Fact p.Prime] : (p : ℤ) ∈ frobeniusPreimageIdeal p (1 : ℤ) := by
  rw [mem_frobeniusPreimageIdeal, frobenius_int, RingHom.id_apply, qInteger_one_left]

/-- At `p = 2` in `ℤ` with `q = 1`: `γ 2 = 2`. -/
example : gamma 2 (1 : ℤ) 2 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine gamma_eq_of_mul_eq (by simpa using isRegular_iff_ne_zero.mpr (two_ne_zero (α := ℤ))) ?_
  rw [frobenius_int, RingHom.id_apply, delta_int, qInteger_one_left]
  norm_num

/-- The congruence `δ [p]_q ≡ 1` modulo `[p]_q` at `p = 2` in `ℤ` with `q = 1`:
`δ 2 - 1 = -2 ∈ (2)`. -/
example : delta 2 (qInteger (1 : ℤ) 2) - 1 ∈ Ideal.span {qInteger (1 : ℤ) 2} :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  delta_pAnalog_sub_one_mem (by simp)

end TauCeti.QDividedPowerChecks
