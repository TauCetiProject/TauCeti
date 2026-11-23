/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.DeltaRing.Completion

/-!
# Checks for the `δ`-structure on an adic completion

These examples exercise the `δ`-structure on the `2`-adic completion of `ℤ`, with its unique
`2`-`δ`-structure `δ n = (n - n ^ 2) / 2`. The operation loses exactly one power of `2`: `2` is
divisible by `2` but `δ 2 = -1` is not, so the shifted function `ℤ ⧸ 4 → ℤ ⧸ 2` sends the class
of `2` to the nonzero class of `-1`, and so does the completed operation on the image of `2`.
-/

namespace TauCeti.Examples

open TauCeti.DeltaRing AdicCompletion

-- `h2` records that the ideal `(2)` of `ℤ` contains `2`.
variable (h2 : ((2 : ℕ) : ℤ) ∈ Ideal.span {(2 : ℤ)})

-- `δ 2 = -1` for the `2`-`δ`-structure on `ℤ`.
example : delta 2 (2 : ℤ) = -1 := by
  rw [delta_int]
  norm_num

-- The shifted operation `ℤ ⧸ 4 → ℤ ⧸ 2` sends the class of `2` to the nonzero class of `-1`.
example : quotientDelta h2 1 (Ideal.Quotient.mk _ 2) ≠ 0 := by
  rw [quotientDelta_mk, delta_int, Ne, Ideal.Quotient.eq_zero_iff_mem, pow_one,
    Ideal.mem_span_singleton]
  norm_num

-- On the `2`-adic completion of `ℤ`, the image of `δ 2` in `ℤ ⧸ 2` is nonzero.
example : evalₐ _ 1 ((adicCompletion h2).delta
    (algebraMap ℤ (AdicCompletion (Ideal.span {(2 : ℤ)}) ℤ) 2)) ≠ 0 := by
  rw [delta_adicCompletion_algebraMap, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, delta_int,
    Ne, Ideal.Quotient.eq_zero_iff_mem, pow_one, Ideal.mem_span_singleton]
  norm_num

end TauCeti.Examples
