/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Herbrand.Basic
public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Two

/-!
# Upper ramification of `ℚ₂(√2)/ℚ₂`

The unique lower break of this ramified quadratic extension is two. Its Herbrand function is
the identity through two and has slope one half thereafter, so the upper break is also two.
This computes the canonical upper filtration and the integral depths used by the unit-filtration
norm theorems.

## References

* J.-P. Serre, *Local Fields*, Chapter IV, §§1 and 3.
-/

public section
noncomputable section

namespace TauCeti.DyadicSqrtTwo

open LocalFieldsRamification

/-- The real lower filtration has a single break at two. -/
@[simp]
theorem lowerRamificationGroupReal_eq (u : ℝ) :
    lowerRamificationGroupReal ℚ_[2] DyadicSqrtTwo u =
      if u ≤ 2 then ⊤ else ⊥ := by
  rw [LocalFieldsRamification.lowerRamificationGroupReal_def, lowerRamificationGroup_eq]
  simp only [Int.ceil_le, Int.cast_ofNat]

/-- The Herbrand function of `ℚ₂(√2)/ℚ₂` is the identity through the lower break two
and has slope one half beyond it. -/
@[simp]
theorem coe_herbrand_eq (u : RamificationIndexDomain) :
    (herbrand ℚ_[2] DyadicSqrtTwo u : ℝ) =
      if (u : ℝ) ≤ 2 then (u : ℝ) else ((u : ℝ) + 2) / 2 := by
  split_ifs with h2
  · by_cases h0 : (u : ℝ) ≤ 0
    · rw [herbrand_of_coe_le_zero ℚ_[2] DyadicSqrtTwo h0]
    · exact congrArg Subtype.val <|
        herbrand_eq_self_of_forall_eq ℚ_[2] DyadicSqrtTwo (le_of_not_ge h0) <|
          fun t _ ht ↦ by
            rw [lowerRamificationGroupReal_eq, ite_eq_left (ht.trans h2)]
            simp
  · have h := coe_herbrand_sub_coe_herbrand_of_forall_eq ℚ_[2] DyadicSqrtTwo
      (a := ⟨2, by norm_num⟩) (b := u) (by exact le_of_lt (lt_of_not_ge h2))
      (fun t ht _ ↦ by
        rw [lowerRamificationGroupReal_eq, lowerRamificationGroupReal_eq]
        simp only [ite_eq_right (by linarith : ¬t ≤ 2), ite_eq_right h2])
    have hbreak : (herbrand ℚ_[2] DyadicSqrtTwo ⟨2, by norm_num⟩ : ℝ) = 2 := by
      exact congrArg Subtype.val <|
        herbrand_eq_self_of_forall_eq ℚ_[2] DyadicSqrtTwo (by norm_num) <|
          fun t _ ht ↦ by
            rw [lowerRamificationGroupReal_eq, ite_eq_left ht]
            simp
    rw [hbreak, lowerRamificationGroupReal_eq, ite_eq_right h2] at h
    rw [natCard_lowerRamificationGroup_zero, ramificationIndex_eq_two] at h
    norm_num only [Subgroup.card_bot, Nat.cast_one, Nat.cast_ofNat] at h
    linarith

/-- The inverse Herbrand function has slope two beyond the upper break two. -/
@[simp]
theorem coe_inverseHerbrand_eq (v : RamificationIndexDomain) :
    (inverseHerbrand ℚ_[2] DyadicSqrtTwo v : ℝ) =
      if (v : ℝ) ≤ 2 then (v : ℝ) else 2 * (v : ℝ) - 2 := by
  have h := coe_herbrand_eq (inverseHerbrand ℚ_[2] DyadicSqrtTwo v)
  rw [herbrand_inverseHerbrand] at h
  split_ifs at h ⊢ <;> linarith

/-- The upper filtration has the same break at two and is trivial above it. -/
@[simp]
theorem upperRamificationGroup_eq (v : RamificationIndexDomain) :
    upperRamificationGroup ℚ_[2] DyadicSqrtTwo v =
      if (v : ℝ) ≤ 2 then ⊤ else ⊥ := by
  rw [upperRamificationGroup_def, lowerRamificationGroupReal_eq, coe_inverseHerbrand_eq]
  split_ifs <;> first | rfl | exfalso; linarith

/-- Integral upper depth `n` corresponds to lower depth `n` up to the break and `2n - 2`
thereafter. -/
@[simp]
theorem psiNat_eq (n : ℕ) :
    psiNat ℚ_[2] DyadicSqrtTwo n = if n ≤ 2 then n else 2 * n - 2 := by
  have h := coe_psiNat ℚ_[2] DyadicSqrtTwo n
  rw [coe_inverseHerbrand_eq] at h
  dsimp only at h
  by_cases hn : n ≤ 2
  · rw [ite_eq_left hn]
    rw [ite_eq_left (by exact_mod_cast hn)] at h
    exact_mod_cast h
  · rw [ite_eq_right hn]
    rw [ite_eq_right (by exact_mod_cast hn)] at h
    apply Nat.cast_injective (R := ℝ)
    rw [Nat.cast_sub (by omega : 2 ≤ 2 * n), Nat.cast_mul, Nat.cast_ofNat]
    exact h

end TauCeti.DyadicSqrtTwo
