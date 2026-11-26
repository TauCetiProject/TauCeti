/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.SignedQuotient
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ZMod.Basic
import TauCeti.Algebra.Group.Subgroup.ZPowers
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Card

/-!
# Orders of `{±I}` and the signed quotient `SL₂(ℤ/Nℤ) ⧸ {±I}`

When `N ∣ 2` (`N = 1` or `N = 2`), `-I = I` modulo `N`, so `{±I}` is trivial and the signed
quotient `Q_N = TauCeti.Matrix.SignedQuotient (Fin 2) (ZMod N)` has order `|SL₂(ℤ/Nℤ)|` (`6` at
`N = 2`). For `¬ N ∣ 2` — in particular for all `N ≥ 3` — `{±I}` has order `2`, giving
`2 · |Q_N| = |SL₂(ℤ/Nℤ)|`.

## References

* F. Diamond and J. Shurman, *A First Course in Modular Forms*, Graduate Texts in Mathematics 228,
  Springer, 2005, §1.2.
-/

public section

open scoped MatrixGroups

namespace TauCeti.Matrix.SpecialLinearGroup

open _root_.Matrix.SpecialLinearGroup

/-- When `N ∣ 2` (`N = 1` or `N = 2`), `{±I} ≤ SL₂(ℤ/Nℤ)` is trivial of order `1`. -/
theorem card_zpowers_neg_one_zmod_eq_one_of_dvd_two {N : ℕ} (h : N ∣ 2) :
    Nat.card (Subgroup.zpowers (-1 : SL(2, ZMod N))) = 1 := by
  rw [Nat.card_zpowers, neg_one_eq_one_zmod_iff.mpr h, orderOf_one]

/-- When `¬ (N ∣ 2)`, `{±I} ≤ SL₂(ℤ/Nℤ)` has order `2`. -/
theorem card_zpowers_neg_one_zmod_eq_two {N : ℕ} (h : ¬ N ∣ 2) :
    Nat.card (Subgroup.zpowers (-1 : SL(2, ZMod N))) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime neg_one_sq fun heq ↦ h (neg_one_eq_one_zmod_iff.mp heq)

end TauCeti.Matrix.SpecialLinearGroup

namespace TauCeti.Matrix.SignedQuotient

open _root_.Matrix.SpecialLinearGroup
open TauCeti.Matrix.SpecialLinearGroup

/-- When `N ∣ 2` (`N = 1` or `N = 2`), `-I = I` modulo `N`, so `|Q_N| = |SL₂(ℤ/Nℤ)|`. -/
theorem card_fin_two_zmod_of_dvd_two {N : ℕ} (h : N ∣ 2) :
    Nat.card (SignedQuotient (Fin 2) (ZMod N)) = Nat.card SL(2, ZMod N) := by
  have hlag :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (-1 : SL(2, ZMod N)))
  rw [card_zpowers_neg_one_zmod_eq_one_of_dvd_two h, mul_one] at hlag; exact hlag.symm

/-- When `¬ (N ∣ 2)` (in particular for all `N ≥ 3`, and at `N = 0`), `2 · |Q_N| = |SL₂(ℤ/Nℤ)|`. -/
theorem two_mul_card_fin_two_zmod_of_not_dvd_two {N : ℕ} (h : ¬ N ∣ 2) :
    2 * Nat.card (SignedQuotient (Fin 2) (ZMod N)) = Nat.card SL(2, ZMod N) := by
  have hlag :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers (-1 : SL(2, ZMod N)))
  rw [card_zpowers_neg_one_zmod_eq_two h, mul_comm] at hlag; exact hlag.symm

/-- For `N ≥ 3`, `2 · |Q_N| = |SL₂(ℤ/Nℤ)|`. -/
theorem two_mul_card_fin_two_zmod {N : ℕ} (hN : 3 ≤ N) :
    2 * Nat.card (SignedQuotient (Fin 2) (ZMod N)) = Nat.card SL(2, ZMod N) :=
  two_mul_card_fin_two_zmod_of_not_dvd_two fun h ↦ by have := Nat.le_of_dvd two_pos h; omega

/-- At level `2`, `-I = I` modulo `2`, so the signed quotient `Q_2 = SL₂(ℤ/2ℤ) ⧸ {±I}` has order
`6 = |SL₂(𝔽₂)|`. -/
theorem card_fin_two_zmod_two : Nat.card (SignedQuotient (Fin 2) (ZMod 2)) = 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [card_fin_two_zmod_of_dvd_two dvd_rfl, TauCeti.natCard_SL_fin_two_zmod]; norm_num

end TauCeti.Matrix.SignedQuotient
