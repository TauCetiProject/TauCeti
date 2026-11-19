/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Data.Int.GCD
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Commute

/-!
# Natural numbers that are units modulo a nilpotent natural number

If the image of a natural number `a` in a semiring `R` is nilpotent, then `a ^ k = 0` in `R` for
some `k`, so an inverse of `n` modulo `a ^ k` is an inverse of `n` in `R`: every natural number
coprime to `a` becomes a unit in `R`. For a prime `ℓ` this says that in a ring of `ℓ`-power torsion
(`ℓ ^ k R = 0`) each integer prime to `ℓ` is invertible; in a nonzero such ring this is also
necessary, since multiples of `ℓ` are nilpotent there.

This is the arithmetic input that turns pro-orders prime to `ℓ` into invertible indices of open
subgroups with coefficients in `ℓ`-power-torsion rings.

## Main results

* `IsNilpotent.isUnit_natCast_of_coprime`: if `(a : R)` is nilpotent, every `n` coprime to `a` is
  a unit of `R`.
* `IsNilpotent.isUnit_natCast_iff_not_dvd`: if `(ℓ : R)` is nilpotent for a prime `ℓ` and `R` is
  nontrivial, `n` is a unit of `R` exactly when `ℓ` does not divide `n`.
-/

public section

namespace IsNilpotent

variable {R : Type*} [Semiring R]

/-- If the image of a natural number `a` in a semiring `R` is nilpotent, then every natural number
coprime to `a` is a unit of `R`. -/
theorem isUnit_natCast_of_coprime {a n : ℕ} (ha : IsNilpotent (a : R)) (hn : n.Coprime a) :
    IsUnit (n : R) := by
  obtain ⟨k, hk⟩ := ha
  rw [← Nat.cast_pow] at hk
  have hnk : n.Coprime (a ^ k) := hn.pow_right k
  obtain h | h | h : a ^ k = 0 ∨ a ^ k = 1 ∨ 1 < a ^ k := by lia
  · rw [h, Nat.coprime_zero_right] at hnk
    simp [hnk]
  · rw [h, Nat.cast_one] at hk
    have : Subsingleton R := subsingleton_of_zero_eq_one hk.symm
    exact isUnit_of_subsingleton _
  · -- An inverse of `n` modulo `a ^ k` is an inverse of `n` in `R`, as `a ^ k = 0` there.
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hnk h
    have hnm : (n : R) * m = 1 := by
      rw [← Nat.cast_mul, ← Nat.mod_add_div (n * m) (a ^ k), hm, Nat.cast_add, Nat.cast_mul, hk,
        zero_mul, add_zero, Nat.cast_one]
    exact ⟨⟨n, m, hnm, (Nat.cast_commute m (n : R)).eq.trans hnm⟩, rfl⟩

/-- If the image of a prime `ℓ` in a nontrivial semiring `R` is nilpotent, then a natural number
is a unit of `R` exactly when `ℓ` does not divide it. -/
theorem isUnit_natCast_iff_not_dvd [Nontrivial R] {ℓ n : ℕ} (hℓ : ℓ.Prime)
    (h : IsNilpotent (ℓ : R)) : IsUnit (n : R) ↔ ¬ ℓ ∣ n := by
  refine ⟨fun hn hdvd ↦ ?_,
    fun hn ↦ h.isUnit_natCast_of_coprime (hℓ.coprime_iff_not_dvd.2 hn).symm⟩
  obtain ⟨c, rfl⟩ := hdvd
  obtain ⟨k, hk⟩ := (Nat.cast_commute ℓ (c : R)).isNilpotent_mul_right h
  rw [Nat.cast_mul] at hn
  -- `(ℓ * c) ^ k` is both a unit and zero.
  exact not_isUnit_zero (hk ▸ hn.pow k)

end IsNilpotent
