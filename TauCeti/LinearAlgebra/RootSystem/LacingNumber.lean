/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.RootLength

/-!
# The lacing number of a Dynkin type

The lacing number of a type records the ratio of the squared length of a long root to that of a
short one: it is `1` for `A`, `D`, `E`, `2` for `B`, `C`, `F₄` and `3` for `G₂`. This file defines
it family by family and compares it with the length table `TauCeti.DynkinType.rootLength`. It is
the number `r` for which the squared root lengths of an invariant form on an irreducible root
system are `s` and `r * s`.

## Main definitions

* `TauCeti.DynkinType.lacingNumber`: the ratio of the long and short squared lengths of a type.

## Main results

* `TauCeti.DynkinType.lacingNumber_eq_one_iff`: a type has lacing number `1` exactly when it is
  simply laced.
* `TauCeti.DynkinType.range_rootLength`: a valid type has exactly the lengths `1` and its lacing
  number.
-/

public section

namespace TauCeti.DynkinType

/-- The **lacing number** of a Dynkin type: the ratio of the squared length of a long root to that
of a short one, which is `1` for `A`, `D`, `E`, `2` for `B`, `C`, `F₄` and `3` for `G₂`.
`TauCeti.DynkinType.range_rootLength` is the comparison with the length table. -/
def lacingNumber : DynkinType → ℤ
  | .A _ | .D _ | .E6 | .E7 | .E8 => 1
  | .B _ | .C _ | .F4 => 2
  | .G2 => 3

@[simp] lemma lacingNumber_A (n : ℕ) : (A n).lacingNumber = 1 := (rfl)
@[simp] lemma lacingNumber_B (n : ℕ) : (B n).lacingNumber = 2 := (rfl)
@[simp] lemma lacingNumber_C (n : ℕ) : (C n).lacingNumber = 2 := (rfl)
@[simp] lemma lacingNumber_D (n : ℕ) : (D n).lacingNumber = 1 := (rfl)
@[simp] lemma lacingNumber_E6 : E6.lacingNumber = 1 := (rfl)
@[simp] lemma lacingNumber_E7 : E7.lacingNumber = 1 := (rfl)
@[simp] lemma lacingNumber_E8 : E8.lacingNumber = 1 := (rfl)
@[simp] lemma lacingNumber_F4 : F4.lacingNumber = 2 := (rfl)
@[simp] lemma lacingNumber_G2 : G2.lacingNumber = 3 := (rfl)

/-- A type has lacing number `1` exactly when it is simply laced. -/
theorem lacingNumber_eq_one_iff {t : DynkinType} : t.lacingNumber = 1 ↔ t.IsSimplyLaced := by
  cases t <;> simp

/-- **The lengths occurring in a valid Dynkin type are `1` and its lacing number.** In particular
both occur, including the long and the short length of a type that is not simply laced. -/
theorem range_rootLength {t : DynkinType} (ht : t.Valid) :
    Set.range t.rootLength = {1, t.lacingNumber} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨i, rfl⟩
    cases t with
    | A n | D n | E6 | E7 | E8 => simp
    | B n | C n | F4 =>
        simp only [rootLength_B, rootLength_C, rootLength_F4, lacingNumber_B, lacingNumber_C,
          lacingNumber_F4]
        split_ifs <;> simp
    | G2 =>
        simp only [rootLength_G2, lacingNumber_G2]
        split_ifs <;> simp
  · rintro _ (rfl | rfl)
    · exact Set.mem_range.mpr (exists_rootLength_eq_one ht)
    · cases t with
      | A n | D n | E6 | E7 | E8 =>
          obtain ⟨i, -⟩ := exists_rootLength_eq_one ht
          exact ⟨i, by simp⟩
      | B n =>
          -- The first node of `Bₙ` is long, since it is not the last node.
          have hn : 2 ≤ n := valid_B.mp ht
          exact ⟨⟨0, by simp only [rank_B]; omega⟩, by
            simp only [rootLength_B, lacingNumber_B]; split_ifs <;> omega⟩
      | C n =>
          -- The last node of `Cₙ` is long.
          have hn : 3 ≤ n := valid_C.mp ht
          exact ⟨⟨n - 1, by simp only [rank_C]; omega⟩, by
            simp only [rootLength_C, lacingNumber_C]; split_ifs <;> omega⟩
      | F4 => exact ⟨⟨0, by simp⟩, by simp⟩
      | G2 => exact ⟨⟨1, by simp⟩, by simp⟩

end TauCeti.DynkinType
