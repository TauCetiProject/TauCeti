/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.Data.Nat.Factorial.NatCast
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Natural numbers that are units modulo a nilpotent prime

If the image of a prime `ℓ` in a commutative ring `R` is nilpotent, so that `ℓ ^ k R = 0` for
some `k`, then each natural number prime to `ℓ` is invertible in `R`
(`IsUnit.natCast_of_isNilpotent_of_coprime`). In a nonzero such ring this is also necessary, since
multiples of `ℓ` are nilpotent there.

This is the arithmetic input that turns pro-orders prime to `ℓ` into invertible indices of open
subgroups with coefficients in `ℓ`-power-torsion rings.

## Main results

* `IsNilpotent.isUnit_natCast_iff_not_dvd`: if `(ℓ : R)` is nilpotent for a prime `ℓ` and `R` is
  nontrivial, `n` is a unit of `R` exactly when `ℓ` does not divide `n`.
-/

public section

namespace IsNilpotent

variable {R : Type*} [CommRing R]

/-- If the image of a prime `ℓ` in a nontrivial commutative ring `R` is nilpotent, then a natural
number is a unit of `R` exactly when `ℓ` does not divide it. -/
theorem isUnit_natCast_iff_not_dvd [Nontrivial R] {ℓ n : ℕ} (hℓ : ℓ.Prime)
    (h : IsNilpotent (ℓ : R)) : IsUnit (n : R) ↔ ¬ ℓ ∣ n := by
  refine ⟨fun hn hdvd ↦ ?_,
    fun hn ↦ IsUnit.natCast_of_isNilpotent_of_coprime h (hℓ.coprime_iff_not_dvd.2 hn)⟩
  obtain ⟨c, rfl⟩ := hdvd
  rw [Nat.cast_mul] at hn
  exact ((Nat.cast_commute ℓ (c : R)).isNilpotent_mul_right h).not_isUnit hn

end IsNilpotent
