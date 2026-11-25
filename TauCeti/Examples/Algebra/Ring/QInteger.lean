/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Algebra.Ring.QInteger

/-!
# Checks for the q-integers

`[0]_q = 0` even at `q = 0`, `[2]_q = 1 + q`, `[3]_2 = 7` (distinguishing the polynomial in `q`
from the constant index) and `[n]_1 = n`.
-/

namespace TauCeti.QIntegerChecks

open QCrys

example : qInteger (0 : ℤ) 0 = 0 := qInteger_zero 0

example {R : Type*} [CommRing R] (q : R) : qInteger q 2 = 1 + q := by
  simp [qInteger_succ]

example : qInteger (2 : ℤ) 3 = 7 := by
  simp [qInteger_succ]

example (n : ℕ) : qInteger (1 : ℤ) n = n := qInteger_one_left n

/-- At `q = 0` the `q`-integer `[n]_0` is `1` for `n ≥ 1`, unlike `n`. -/
example : qInteger (0 : ℤ) 3 = 1 := by
  simp [qInteger_succ]

end TauCeti.QIntegerChecks
