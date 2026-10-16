/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WorkedExamples.CyclotomicEight.Basic
public import TauCeti.NumberTheory.LocalField.Herbrand.Basic

/-!
# Herbrand functions of `ℚ₂(ζ₈)/ℚ₂`

The lower breaks at one and three become upper breaks at one and two. The Herbrand
function has slopes one, one half, and one quarter on the three corresponding intervals;
in particular its value at the lower index two is the noninteger `3/2`. Its inverse has
slopes one, two, and four, and the upper filtration retains the exponent-five subgroup
through upper index two.

These formulas compute the canonical Herbrand functions and filtrations, reusing the lower
filtration in `CyclotomicEight.Basic` and the affine-interval theorem in `Herbrand.Basic`.
They provide an explicit example of the change from lower to upper numbering.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §§1 and 3.
-/

public section
noncomputable section

namespace TauCeti.DyadicCyclotomicEight

open LocalFieldsRamification

private theorem herbrand_one :
    (herbrand ℚ_[2] DyadicCyclotomicEight ⟨1, by norm_num⟩ : ℝ) = 1 := by
  rw [coe_herbrand_of_coe_eq_natCast ℚ_[2] DyadicCyclotomicEight 1 (by norm_num),
    natCard_lowerRamificationGroup_zero, ramificationIndex_eq_four]
  simp only [Finset.Icc_self, Finset.sum_singleton, lowerRamificationGroup_eq]
  norm_num only [ite_true, Subgroup.card_top, IsGalois.card_aut_eq_finrank,
    finrank_eq_four, Nat.cast_ofNat]

private theorem herbrand_three :
    (herbrand ℚ_[2] DyadicCyclotomicEight ⟨3, by norm_num⟩ : ℝ) = 2 := by
  rw [coe_herbrand_of_coe_eq_natCast ℚ_[2] DyadicCyclotomicEight 3 rfl,
    natCard_lowerRamificationGroup_zero, ramificationIndex_eq_four]
  have hIcc : Finset.Icc (1 : ℕ) 3 = {1, 2, 3} := by decide
  rw [hIcc,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp only [lowerRamificationGroup_eq]
  norm_num only [ite_true, ite_false, Subgroup.card_top, Nat.card_zpowers,
    orderOf_sigmaFive, IsGalois.card_aut_eq_finrank, finrank_eq_four, Nat.cast_ofNat]

/-- The Herbrand function has slopes `1`, `1/2`, and `1/4`, with lower breaks `1` and `3`.
The formula includes the prescribed identity on `[-1, 0]`. -/
@[simp]
theorem coe_herbrand_eq (u : RamificationIndexDomain) :
    (herbrand ℚ_[2] DyadicCyclotomicEight u : ℝ) =
      if (u : ℝ) ≤ 1 then (u : ℝ) else if (u : ℝ) ≤ 3 then ((u : ℝ) + 1) / 2
        else ((u : ℝ) + 5) / 4 := by
  split_ifs with h1 h3
  · by_cases h0 : (u : ℝ) ≤ 0
    · rw [herbrand_of_coe_le_zero ℚ_[2] DyadicCyclotomicEight h0]
    · exact congrArg Subtype.val <|
        herbrand_eq_self_of_forall_eq ℚ_[2] DyadicCyclotomicEight (le_of_not_ge h0) <|
          fun t _ ht ↦ by
            rw [lowerRamificationGroupReal_eq, ite_eq_left (ht.trans h1)]
            simp
  · have h := coe_herbrand_sub_coe_herbrand_of_forall_eq ℚ_[2] DyadicCyclotomicEight
      (a := ⟨1, by norm_num⟩) (b := u) (by exact le_of_lt (lt_of_not_ge h1))
      (fun t ht htu ↦ by
        rw [lowerRamificationGroupReal_eq, lowerRamificationGroupReal_eq]
        simp only [ite_eq_right (by linarith : ¬t ≤ 1), ite_eq_left (htu.trans h3),
          ite_eq_right h1, ite_eq_left h3])
    rw [herbrand_one, lowerRamificationGroupReal_eq, ite_eq_right h1, ite_eq_left h3] at h
    rw [natCard_lowerRamificationGroup_zero, ramificationIndex_eq_four] at h
    norm_num only [Nat.card_zpowers, orderOf_sigmaFive, Nat.cast_ofNat] at h
    linarith
  · have h := coe_herbrand_sub_coe_herbrand_of_forall_eq ℚ_[2] DyadicCyclotomicEight
      (a := ⟨3, by norm_num⟩) (b := u) (by exact le_of_lt (lt_of_not_ge h3))
      (fun t ht _ ↦ by
        rw [lowerRamificationGroupReal_eq, lowerRamificationGroupReal_eq]
        simp only [ite_eq_right (by linarith : ¬t ≤ 1), ite_eq_right (by linarith : ¬t ≤ 3),
          ite_eq_right h1, ite_eq_right h3])
    rw [herbrand_three, lowerRamificationGroupReal_eq, ite_eq_right h1, ite_eq_right h3] at h
    rw [natCard_lowerRamificationGroup_zero, ramificationIndex_eq_four] at h
    norm_num only [Subgroup.card_bot, Nat.cast_one, Nat.cast_ofNat] at h
    linarith

/-- The inverse Herbrand function has upper breaks `1` and `2`, and slopes `1`, `2`, and `4`. -/
@[simp]
theorem coe_inverseHerbrand_eq (v : RamificationIndexDomain) :
    (inverseHerbrand ℚ_[2] DyadicCyclotomicEight v : ℝ) =
      if (v : ℝ) ≤ 1 then (v : ℝ) else if (v : ℝ) ≤ 2 then 2 * (v : ℝ) - 1
        else 4 * (v : ℝ) - 5 := by
  have h := coe_herbrand_eq (inverseHerbrand ℚ_[2] DyadicCyclotomicEight v)
  rw [herbrand_inverseHerbrand] at h
  split_ifs at h ⊢ <;> linarith

/-- The upper filtration is the whole group through `1`, the exponent-five subgroup
through `2`, and trivial above `2`. -/
@[simp]
theorem upperRamificationGroup_eq (v : RamificationIndexDomain) :
    upperRamificationGroup ℚ_[2] DyadicCyclotomicEight v =
      if (v : ℝ) ≤ 1 then ⊤ else if (v : ℝ) ≤ 2 then Subgroup.zpowers sigmaFive else ⊥ := by
  rw [upperRamificationGroup_def, lowerRamificationGroupReal_eq, coe_inverseHerbrand_eq]
  split_ifs <;> first | rfl | exfalso; linarith

/-- The value at lower index two is `3/2`, illustrating that integral lower indices
need not have integral Herbrand values. -/
@[simp]
theorem herbrand_two :
    herbrand ℚ_[2] DyadicCyclotomicEight ⟨2, by norm_num⟩ = ⟨3 / 2, by norm_num⟩ := by
  apply Subtype.ext
  rw [coe_herbrand_eq]
  norm_num

/-- The integral inverse-Herbrand depths are `n` through depth one and `4n - 5` thereafter. -/
@[simp]
theorem psiNat_eq (n : ℕ) :
    psiNat ℚ_[2] DyadicCyclotomicEight n = if n ≤ 1 then n else 4 * n - 5 := by
  have h := coe_psiNat ℚ_[2] DyadicCyclotomicEight n
  rw [coe_inverseHerbrand_eq] at h
  -- Reduce the coercions of the natural-index subtype constructor.
  dsimp only at h
  by_cases h1 : n ≤ 1
  · rw [ite_eq_left h1] at ⊢
    rw [ite_eq_left (by exact_mod_cast h1)] at h
    exact_mod_cast h
  · rw [ite_eq_right h1] at ⊢
    rw [ite_eq_right (by exact_mod_cast h1)] at h
    by_cases h2 : n ≤ 2
    · have hn : n = 2 := by omega
      subst n
      norm_num only at h ⊢
      exact_mod_cast h
    · rw [ite_eq_right (by exact_mod_cast h2)] at h
      apply Nat.cast_injective (R := ℝ)
      rw [Nat.cast_sub (by omega : 5 ≤ 4 * n), Nat.cast_mul, Nat.cast_ofNat]
      exact h

end TauCeti.DyadicCyclotomicEight
