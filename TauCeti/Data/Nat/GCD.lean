/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.GCD.Basic

/-!
# Coprimality of `q` and `q ^ N - 1`

For `q > 1` and `N > 0`, the natural numbers `q` and `q ^ N - 1` are coprime, because any common
divisor of `q` and `q ^ N - 1` also divides `q ^ N - (q ^ N - 1) = 1`.

## Main results

* `Nat.coprime_pow_sub_one`: `q` is coprime to `q ^ N - 1`. Its consumers are the order
  computation `TauCeti.ZMod.orderOf_unitOfCoprime_pow_sub_one` in
  `TauCeti/Data/ZMod/Units.lean` and the cyclotomic normalization of the local Artin map in
  `TauCeti/NumberTheory/ClassFieldTheory/Local/ExplicitCyclotomicSymbol/ArtinMap.lean`.
-/

public section

namespace Nat

/-- If `q > 1` and `N > 0`, then `q` is coprime to `q ^ N - 1`. -/
theorem coprime_pow_sub_one (q N : ℕ) (hq : 1 < q) (hN : N ≠ 0) :
    q.Coprime (q ^ N - 1) := by
  have hpow : 1 ≤ q ^ N := Nat.one_le_iff_ne_zero.mpr
    (pow_ne_zero N (Nat.ne_zero_of_lt hq))
  apply Nat.Coprime.of_dvd_left (dvd_pow_self q hN)
  exact (Nat.coprime_self_sub_right hpow).2 (Nat.coprime_one_right _)

end Nat
