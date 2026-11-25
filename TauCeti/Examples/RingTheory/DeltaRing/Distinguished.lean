/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.DeltaRing.Distinguished

/-!
# Checks for distinguished elements

In `ℤ` with its unique `δ`-structure, `2` is distinguished for `p = 2` (`δ 2 = -1`), while `3` is
not distinguished for `p = 3` (`δ 3 = -8`), although `3 ∈ (3, φ 3) = (3)`: the criterion
`p ∈ (d, φ d)` needs `d` and `p` in the Jacobson radical, which is `0` in `ℤ`. The element `0` is
never distinguished in a nonzero `δ`-ring.
-/

namespace TauCeti.Examples

open DeltaRing

-- `2` is distinguished in `ℤ` for `p = 2`.
example : IsDistinguished 2 (2 : ℤ) := by
  rw [isDistinguished_iff, delta_int]
  norm_num

-- `3` is not distinguished in `ℤ` for `p = 3`, as `δ 3 = -8`.
example : ¬ IsDistinguished 3 (3 : ℤ) := by
  rw [isDistinguished_iff, delta_int, Int.isUnit_iff]
  norm_num

-- Yet `3 ∈ (3, φ 3)` in `ℤ`: the converse criterion needs the Jacobson radical hypotheses.
example : ((3 : ℕ) : ℤ) ∈ Ideal.span {(3 : ℤ), frobenius 3 ℤ 3} :=
  Ideal.subset_span (by simp)

-- `0` is not distinguished in a nonzero `δ`-ring.
example {A : Type*} [CommRing A] [Nontrivial A] (p : ℕ) [DeltaRing p A] :
    ¬ IsDistinguished p (0 : A) := by
  rw [isDistinguished_iff, delta_zero]
  exact not_isUnit_zero

end TauCeti.Examples
