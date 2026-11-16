/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs

/-!
# Elements outside subsets containing `1` or `0`

An element outside any `OneMemClass` subset differs from `1`; additively, an element outside any
`ZeroMemClass` subset (such as an additive submonoid, subgroup, ideal, or submodule) is nonzero.

## Main results

* `TauCeti.ne_one_of_notMem` and `TauCeti.ne_zero_of_notMem`: `x ∉ s → x ≠ 1` and `x ∉ s → x ≠ 0`.
-/

public section

namespace TauCeti

/-- An element outside a subset containing `1` is not `1`. -/
@[to_additive /-- An element outside a subset containing `0` is nonzero. -/]
theorem ne_one_of_notMem {S M : Type*} [One M] [SetLike S M] [OneMemClass S M] {s : S} {x : M}
    (hx : x ∉ s) : x ≠ 1 :=
  (ne_of_mem_of_not_mem (one_mem s) hx).symm

end TauCeti

end
