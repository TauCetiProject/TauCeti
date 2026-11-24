/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# The coefficients of `(1 - X)⁻ᵈ`

The power series `(1 - X)⁻ᵈ` counts multisets: its coefficient of `Xⁿ` is the number
`d.multichoose n` of multisets of size `n` drawn from `d` elements. This is the shape of the
Hilbert series of a polynomial ring in `d` variables.

## Main results

* `PowerSeries.mk_multichoose_eq_invOneSubPow`: `∑ₙ (d multichoose n) Xⁿ = (1 - X)⁻ᵈ`.
-/

public section

namespace PowerSeries

/-- The series `∑ₙ (d multichoose n) Xⁿ` is `(1 - X)⁻ᵈ`, the inverse of `(1 - X)ᵈ`. -/
theorem mk_multichoose_eq_invOneSubPow (R : Type*) [CommRing R] (d : ℕ) :
    mk (fun n ↦ (d.multichoose n : R)) = invOneSubPow R d := by
  cases d with
  | zero =>
    ext n
    cases n <;> simp [invOneSubPow_zero]
  | succ r =>
    rw [invOneSubPow_val_succ_eq_mk_add_choose]
    ext n
    simp only [coeff_mk, Nat.multichoose_eq]
    rw [Nat.succ_add_sub_one, Nat.choose_symm_add]

end PowerSeries
