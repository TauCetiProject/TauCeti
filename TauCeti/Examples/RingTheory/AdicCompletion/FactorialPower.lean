/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.Basic
import TauCeti.RingTheory.AdicCompletion.FactorialPower

/-!
# Checks for the factorial idempotent

A finite ring is complete for the zero ideal, with finite quotients, so its factorial idempotents
are the eventual values of the factorial powers. In `ZMod 6 ≃ ZMod 2 × ZMod 3`, multiplication by
`2` is nilpotent on the first factor and invertible on the second, and its factorial idempotent
is `4`, the idempotent cutting out the second factor. It is neither `0` nor `1`, so the factorial
idempotent of a non-unit need not vanish. The nilpotent `2` of `ZMod 8` has factorial idempotent
`0`, and the unit `3` of `ZMod 8` has factorial idempotent `1`.
-/

namespace TauCeti.FactorialIdempotentChecks

open scoped Nat

/-- In `ZMod 6`, the factorial idempotent of `2` is `4`. -/
example : (⊥ : Ideal (ZMod 6)).factorialIdempotent (2 : ZMod 6) = 4 := by
  refine Ideal.factorialIdempotent_eq_of_eventually_sub_mem fun _ ↦
    (Filter.eventually_ge_atTop 2).mono fun n hn ↦ ?_
  -- `n !` is even and positive, and `2 ^ 2 = 4` is idempotent.
  obtain ⟨m, hm⟩ := Nat.dvd_factorial two_pos hn
  have hm0 : m ≠ 0 := by rintro rfl; simp [Nat.factorial_ne_zero] at hm
  have h4 : IsIdempotentElem (4 : ZMod 6) := isIdempotentElem_iff.mpr (by decide)
  rw [hm, pow_mul, show (2 : ZMod 6) ^ 2 = 4 by decide, h4.pow_eq hm0, sub_self]
  exact Submodule.zero_mem _

/-- In `ZMod 8`, the nilpotent `2` has factorial idempotent `0`. -/
example : (⊥ : Ideal (ZMod 8)).factorialIdempotent (2 : ZMod 8) = 0 :=
  Ideal.factorialIdempotent_eq_zero_of_isNilpotent ⟨3, by decide⟩

/-- In `ZMod 8`, the unit `3` has factorial idempotent `1`. -/
example : (⊥ : Ideal (ZMod 8)).factorialIdempotent (3 : ZMod 8) = 1 :=
  Ideal.factorialIdempotent_eq_one_of_isUnit (isUnit_iff_exists_inv.mpr ⟨3, by decide⟩)

end TauCeti.FactorialIdempotentChecks
