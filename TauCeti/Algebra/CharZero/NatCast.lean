/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fin.Basic
public import Mathlib.Logic.Pairwise
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic

/-!
# Distinct squares of shifted natural numbers

In a semiring of characteristic zero the squares `(k + 1)²` of the shifted natural numbers are
pairwise distinct. Taking `cₖ = k + 1` therefore gives, in every dimension, a family of nonzero
rates with distinct squares, as needed for the regular elements of Williamson's normal forms.

## Main results

* `TauCeti.pairwise_sq_natCast_add_one_ne`: the squares `(k + 1)²`, `k : Fin n`, are pairwise
  distinct in characteristic zero.
-/

public section

namespace TauCeti

/-- In characteristic zero, the squares `(k + 1)²` for `k : Fin n` are pairwise distinct. -/
theorem pairwise_sq_natCast_add_one_ne {R : Type*} [Semiring R] [CharZero R] {n : ℕ} :
    Pairwise fun k l : Fin n ↦ ((k : R) + 1) ^ 2 ≠ ((l : R) + 1) ^ 2 := fun _ _ hkl h ↦
  hkl (Fin.ext (Nat.succ_injective (Nat.pow_left_injective two_ne_zero (by exact_mod_cast h))))

end TauCeti
