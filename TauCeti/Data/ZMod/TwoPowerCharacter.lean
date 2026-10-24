/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.CharacterModule
public import TauCeti.Algebra.AddCircle
public import TauCeti.RingTheory.ZMod.UnitsTwoPow

/-!
# Characters of units modulo powers of two

The unit group modulo `2^(n+3)` admits a character to `ℚ/ℤ` with kernel of order at most two
and with nonzero value at `-1`. Its value on `5` has order `2^(n+1)`. Such a character cuts out
a cyclic, totally complex subextension of a two-power cyclotomic extension.

The construction uses `TauCeti.CharacterModule.exists_apply_eq_inv_addOrderOf` to extend
characters and `TauCeti.ZMod.orderOf_unitsTwoPowFive` for the kernel bound. A character modulo
four ensures the nonzero value at `-1`.

## Reference

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 7.3,
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>.
-/

public section

noncomputable section

namespace TauCeti.CharacterModule

/-- A character of the units modulo `2^(n+3)` detects complex conjugation and has kernel of
order at most two. Its value on `5` has order `2^(n+1)`. -/
theorem exists_character_units_two_pow (n : ℕ) :
    ∃ χ : Additive (ZMod (2 ^ (n + 3)))ˣ →+ AddCircle (1 : ℚ),
      χ (Additive.ofMul (ZMod.unitsTwoPowFive (n + 1))) =
          ((1 / 2 ^ (n + 1) : ℚ) : AddCircle (1 : ℚ)) ∧
      χ (Additive.ofMul (-1)) ≠ 0 ∧ Nat.card χ.ker ≤ 2 := by
  -- The value at five forces a cyclic image of order at least half the unit group.
  let u := ZMod.unitsTwoPowFive (n + 1)
  have hu : addOrderOf (Additive.ofMul u) = 2 ^ (n + 1) := by
    rw [addOrderOf_ofMul_eq_orderOf]
    exact ZMod.orderOf_unitsTwoPowFive (n + 1)
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ : Additive (ZMod (2 ^ (n + 3)))ˣ →+ AddCircle (1 : ℚ),
      χ (Additive.ofMul u) = ((1 / addOrderOf (Additive.ofMul u) : ℚ) : AddCircle (1 : ℚ)) :=
    exists_apply_eq_inv_addOrderOf (Additive.ofMul u) (hu.trans_ne (by positivity))
  have hχ₀ : χ₀ (Additive.ofMul u) = ((1 / 2 ^ (n + 1) : ℚ) : AddCircle (1 : ℚ)) := by
    simpa only [hu, Nat.cast_pow, Nat.cast_ofNat] using hχ₀
  -- A character modulo four changes the value at -1 without changing the value at five.
  have hneg : addOrderOf (Additive.ofMul (-1 : (ZMod 4)ˣ)) = 2 := by
    rw [addOrderOf_ofMul_eq_orderOf]
    exact orderOf_eq_prime (by simp) (by decide)
  obtain ⟨δ, hδ⟩ : ∃ δ : Additive (ZMod 4)ˣ →+ AddCircle (1 : ℚ),
      δ (Additive.ofMul (-1)) =
        ((1 / addOrderOf (Additive.ofMul (-1 : (ZMod 4)ˣ)) : ℚ) : AddCircle (1 : ℚ)) :=
    exists_apply_eq_inv_addOrderOf (Additive.ofMul (-1 : (ZMod 4)ˣ)) (hneg.trans_ne (by decide))
  have hδ : δ (Additive.ofMul (-1)) = ((1 / 2 : ℚ) : AddCircle (1 : ℚ)) := by
    simpa only [hneg, Nat.cast_ofNat] using hδ
  have h4 : 4 ∣ 2 ^ (n + 3) := by
    exact_mod_cast (pow_dvd_pow 2 (show 2 ≤ n + 3 by omega))
  let ρ := ZMod.unitsMap h4
  have hρu : ρ u = 1 := ZMod.unitsMap_unitsTwoPowFive (n + 1) h4
  have hρneg : ρ (-1) = -1 := by
    simpa only [ρ, ZMod.unitsMap_def] using Units.map_neg_one (ZMod.castHom h4 (ZMod 4))
  let χ : Additive (ZMod (2 ^ (n + 3)))ˣ →+ AddCircle (1 : ℚ) :=
    if χ₀ (Additive.ofMul (-1)) = 0 then χ₀ + δ.comp ρ.toAdditive else χ₀
  have hχu : χ (Additive.ofMul u) = ((1 / 2 ^ (n + 1) : ℚ) : AddCircle (1 : ℚ)) := by
    simp only [χ]
    split_ifs <;> simp [hχ₀, hρu]
  have hχneg : χ (Additive.ofMul (-1)) ≠ 0 := by
    simp only [χ]
    split_ifs with h
    · simp only [AddMonoidHom.add_apply, AddMonoidHom.comp_apply, MonoidHom.toAdditive_apply_apply,
        toMul_ofMul, hρneg, h, zero_add, hδ]
      have hord := AddCircle.addOrderOf_period_div_of_ne_zero (1 : ℚ) (n := 2) (by decide)
      norm_num only [Nat.cast_ofNat] at hord
      intro hz
      rw [hz, addOrderOf_zero] at hord
      omega
    · exact h
  -- The image-order bound and the kernel/image formula give the index-two bound.
  have hcard : Nat.card (Additive (ZMod (2 ^ (n + 3)))ˣ) = 2 * 2 ^ (n + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_additive, ZMod.card_units_eq_totient,
      Nat.totient_prime_pow Nat.prime_two (by omega)]
    simp [pow_succ, Nat.mul_comm]
  have hrange : 2 ^ (n + 1) ≤ Nat.card χ.range := by
    have hmem : χ (Additive.ofMul u) ∈ χ.range := ⟨_, rfl⟩
    have hdvd := χ.range.addOrderOf_dvd_natCard hmem
    have hord : addOrderOf ((1 / 2 ^ (n + 1) : ℚ) : AddCircle (1 : ℚ)) = 2 ^ (n + 1) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using
        AddCircle.addOrderOf_period_div_of_ne_zero (1 : ℚ) (n := 2 ^ (n + 1)) (by positivity)
    rw [hχu, hord] at hdvd
    exact Nat.le_of_dvd Nat.card_pos hdvd
  refine ⟨χ, hχu, hχneg, ?_⟩
  have hmul := AddSubgroup.card_ker_mul_card_range χ
  rw [hcard] at hmul
  have hpos : 0 < 2 ^ (n + 1) := by positivity
  nlinarith

end TauCeti.CharacterModule
