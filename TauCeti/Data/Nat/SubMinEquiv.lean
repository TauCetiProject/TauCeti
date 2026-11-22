/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Int.Init
public import Mathlib.Logic.Equiv.Defs

/-!
# Difference-and-minimum equivalence on `ℕ × ℕ`

Every pair `(a, b) : ℕ × ℕ` is uniquely determined by its signed difference `(a : ℤ) - b` and its
minimum `min a b`, recovering `(a, b) = (m.toNat + k, (-m).toNat + k)` for `(m, k) : ℤ × ℕ`. This
reindexing parametrizes two-variable monomials along diagonals `i - j = m`.
-/

public section

namespace Nat

/-- The difference-and-minimum equivalence `ℕ × ℕ ≃ ℤ × ℕ`, sending `(a, b)` to
`((a : ℤ) - b, min a b)` with inverse `(m, k) ↦ (m.toNat + k, (-m).toNat + k)`. -/
def subMinEquiv : ℕ × ℕ ≃ ℤ × ℕ where
  toFun ab := ((ab.1 : ℤ) - ab.2, min ab.1 ab.2)
  invFun mk := (mk.1.toNat + mk.2, (-mk.1).toNat + mk.2)
  left_inv ab := by ext <;> dsimp <;> omega
  right_inv mk := by ext <;> dsimp <;> omega

@[simp]
theorem subMinEquiv_apply (ab : ℕ × ℕ) :
    subMinEquiv ab = ((ab.1 : ℤ) - ab.2, min ab.1 ab.2) :=
  (rfl)

@[simp]
theorem subMinEquiv_symm_apply (mk : ℤ × ℕ) :
    subMinEquiv.symm mk = (mk.1.toNat + mk.2, (-mk.1).toNat + mk.2) :=
  (rfl)

end Nat
