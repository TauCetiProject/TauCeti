/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.NumberOfRoots

/-!
# Coxeter numbers of Dynkin types

Defines the Coxeter number `TauCeti.DynkinType.coxeterNumber` (`h = n + 1` for `Aₙ`, `2n` for
`Bₙ`/`Cₙ`, `2(n - 1)` for `Dₙ`, and `12, 18, 30, 12, 6` for `E₆, E₇, E₈, F₄, G₂`), `2 ≤ h` for
valid types, and `|Φ| = r h`.

## Main definitions & results

* `TauCeti.DynkinType.coxeterNumber`, `two_le_coxeterNumber`, `coxeterNumber_pos`,
  `numRoots_eq_rank_mul_coxeterNumber`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. V, §6, and Plates I--IX.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge (1990), §§ 3.16–3.20.
-/

public section

namespace TauCeti.DynkinType

/-- The **Coxeter number** `h` of a Dynkin type: for a valid Dynkin type, this is the order of
every Coxeter element (`TauCeti.Coxeter.orderOf_wordProd_of_hasCartanType`). -/
def coxeterNumber : DynkinType → ℕ
  | .A n => n + 1
  | .B n | .C n => 2 * n
  | .D n => 2 * (n - 1)
  | .E6 => 12
  | .E7 => 18
  | .E8 => 30
  | .F4 => 12
  | .G2 => 6

@[simp] lemma coxeterNumber_A (n : ℕ) : (A n).coxeterNumber = n + 1 := (rfl)
@[simp] lemma coxeterNumber_B (n : ℕ) : (B n).coxeterNumber = 2 * n := (rfl)
@[simp] lemma coxeterNumber_C (n : ℕ) : (C n).coxeterNumber = 2 * n := (rfl)
@[simp] lemma coxeterNumber_D (n : ℕ) : (D n).coxeterNumber = 2 * (n - 1) := (rfl)
@[simp] lemma coxeterNumber_E6 : E6.coxeterNumber = 12 := (rfl)
@[simp] lemma coxeterNumber_E7 : E7.coxeterNumber = 18 := (rfl)
@[simp] lemma coxeterNumber_E8 : E8.coxeterNumber = 30 := (rfl)
@[simp] lemma coxeterNumber_F4 : F4.coxeterNumber = 12 := (rfl)
@[simp] lemma coxeterNumber_G2 : G2.coxeterNumber = 6 := (rfl)

/-- Every valid Dynkin type has Coxeter number at least `2`. -/
lemma two_le_coxeterNumber {t : DynkinType} (ht : t.Valid) : 2 ≤ t.coxeterNumber := by
  cases t with
  | A n => have := valid_A.mp ht; simp; omega
  | B n => have := valid_B.mp ht; simp; omega
  | C n => have := valid_C.mp ht; simp; omega
  | D n => have := valid_D.mp ht; simp; omega
  | E6 | E7 | E8 | F4 | G2 => simp

/-- Every valid Dynkin type has positive Coxeter number. -/
lemma coxeterNumber_pos {t : DynkinType} (ht : t.Valid) : 0 < t.coxeterNumber :=
  lt_of_lt_of_le (by norm_num) (two_le_coxeterNumber ht)

/-- **For every Dynkin type, the number of roots equals the rank times the Coxeter number**:
`|Φ| = r h`. -/
theorem numRoots_eq_rank_mul_coxeterNumber (t : DynkinType) :
    t.numRoots = t.rank * t.coxeterNumber := by
  cases t with
  | A n | E6 | E7 | E8 | F4 | G2 => rfl
  | B n | C n | D n => simp; ring

end TauCeti.DynkinType
