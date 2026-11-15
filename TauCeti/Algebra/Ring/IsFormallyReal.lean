/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Formally real rings have no additive torsion

In a formally real ring, an element with vanishing square is zero. If `n • a = 0` for a positive
natural number `n`, then `n • (a * a) = (n • a) * a` is a sum of `n` squares equal to zero, so
`a * a = 0` and therefore `a = 0`. Hence a formally real ring has unique division by positive
natural numbers (`HasUniqueDiv.of_isFormallyReal`), so it is additively torsion-free.
-/

public section

namespace IsFormallyReal

variable {R : Type*} [NonUnitalNonAssocSemiring R] [IsFormallyReal R]

/-- In a formally real ring, an element whose square vanishes is zero. -/
theorem eq_zero_of_mul_self_eq_zero {a : R} (h : a * a = 0) : a = 0 := by
  by_contra ha
  exact not_isSumNonzeroSq_zero (h ▸ IsSumNonzeroSq.sq ha)

/-- A formally real ring has no additive torsion: `n • a = 0` with `n ≠ 0` forces `a = 0`. -/
theorem eq_zero_of_nsmul_eq_zero {n : ℕ} (hn : n ≠ 0) {a : R} (h : n • a = 0) : a = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one.mpr (Nat.pos_of_ne_zero hn)
  refine eq_zero_of_mul_self_eq_zero <| eq_zero_of_add_right (.mul_self a)
    (AddSubmonoid.mem_sumSq.mp (nsmul_mem (AddSubmonoid.mem_sumSq.mpr (.mul_self a)) k)) ?_
  rw [← succ_nsmul', ← AddMonoidHom.mulRight_apply, ← map_nsmul, AddMonoidHom.mulRight_apply,
    h, zero_mul]

end IsFormallyReal

/-- A formally real ring has unique division by positive natural numbers. -/
instance HasUniqueDiv.of_isFormallyReal {R : Type*} [NonUnitalNonAssocRing R]
    [IsFormallyReal R] : HasUniqueDiv R where
  nsmul_right_injective _ hn _ _ h :=
    sub_eq_zero.mp <| IsFormallyReal.eq_zero_of_nsmul_eq_zero hn <| by
      simp only [nsmul_sub, h, sub_self]
