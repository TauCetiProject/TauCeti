/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Bounds on root exponents in a free group

The cyclically reduced part of a nonidentity word has positive length. Consequently,
the exponent of any positive power representing a nonidentity element is bounded by
the length of that element's reduced word.

The length calculation is in `TauCeti.GroupTheory.FreeGroup.CyclicallyReduced`.
-/

public section

namespace FreeGroup

variable {α : Type*}

section

variable [DecidableEq α]

/-- The exponent of a power representing a nonidentity element cannot exceed its
reduced-word length. -/
@[to_additive]
theorem le_norm_of_pow_eq {x y : FreeGroup α} {n : ℕ}
    (hx : x ≠ 1) (hpow : y ^ n = x) : n ≤ norm x := by
  have hn : 0 < n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0, pow_zero] at hpow
    exact hx hpow.symm
  have hy : y ≠ 1 := by
    intro h
    rw [h, one_pow] at hpow
    exact hx hpow.symm
  have hl : 0 < (reduceCyclically y.toWord).length :=
    List.length_pos_iff_ne_nil.mpr (by simpa using hy)
  rw [← hpow, norm_pow_eq y hn]
  calc
    n = n * 1 := by omega
    _ ≤ n * (reduceCyclically y.toWord).length := Nat.mul_le_mul_left n hl
    _ ≤ 2 * (reduceCyclically.conjugator y.toWord).length +
      n * (reduceCyclically y.toWord).length := Nat.le_add_left _ _

end

end FreeGroup
