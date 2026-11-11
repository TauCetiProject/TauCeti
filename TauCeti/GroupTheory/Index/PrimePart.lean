/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Index
public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Prime parts of subgroup indices

If the order of a subgroup is prime to `p`, its index has the same `p`-part as the order of
the ambient group. This arithmetic constraint on indices gives dimension constraints on
induced representations.

The `ℓ`-adic valuation of the index is antitone along inclusions of subgroups of nonzero index
(`Subgroup.padicValNat_index_le_of_le`), and the valuation of the index of a subgroup `A` is the
sum of the valuations of its relative index in a larger subgroup `B` and of the index of `B`
(`Subgroup.padicValNat_relIndex_add_padicValNat_index`), as an identity in `ℕ∞`.
-/

public section

namespace Subgroup

/-- The index of a subgroup of order prime to `p` has the same `p`-part as the order of the
ambient group. No primality of `p` or finiteness of the group is needed. -/
theorem ordProj_index_eq_ordProj_natCard {G : Type*} [Group G]
    (S : Subgroup G) {p : ℕ} (hS : ¬ p ∣ Nat.card S) :
    ordProj[p] S.index = ordProj[p] (Nat.card G) := by
  have hS₀ : Nat.card S ≠ 0 := fun h ↦ hS (h ▸ dvd_zero p)
  rcases eq_or_ne S.index 0 with h | h
  · simp [← S.card_mul_index, h]
  rw [← S.card_mul_index, Nat.factorization_mul hS₀ h, Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hS, zero_add]

/-- The `ℓ`-adic valuation of the index of a subgroup is at most that of any subgroup it contains,
provided the smaller subgroup has nonzero index. -/
theorem padicValNat_index_le_of_le {G : Type*} [Group G] {A B : Subgroup G} (h : A ≤ B)
    (hA : A.index ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] :
    (padicValNat ℓ B.index : ℕ∞) ≤ padicValNat ℓ A.index := by
  have hdvd := Subgroup.index_dvd_of_le h
  simp only [Nat.padicValNat_def]
  rw [multiplicity_eq_emultiplicity (ne_zero_of_dvd_ne_zero hA hdvd),
    multiplicity_eq_emultiplicity hA]
  exact emultiplicity_le_emultiplicity_of_dvd_right hdvd

/-- For subgroups `A ≤ B` with `A` of nonzero index, the `ℓ`-adic valuation of the index of `A`
is the sum of the valuations of the relative index of `A` in `B` and of the index of `B`. -/
theorem padicValNat_relIndex_add_padicValNat_index {G : Type*} [Group G] {A B : Subgroup G}
    (h : A ≤ B) (hA : A.index ≠ 0) (ℓ : ℕ) [Fact ℓ.Prime] :
    (padicValNat ℓ (A.relIndex B) : ℕ∞) + padicValNat ℓ B.index = padicValNat ℓ A.index := by
  have hmul := A.relIndex_mul_index h
  rw [← hmul] at hA ⊢
  simp only [Nat.padicValNat_def]
  rw [Nat.multiplicity_mul (left_ne_zero_of_mul hA) (right_ne_zero_of_mul hA), Nat.cast_add]

end Subgroup
