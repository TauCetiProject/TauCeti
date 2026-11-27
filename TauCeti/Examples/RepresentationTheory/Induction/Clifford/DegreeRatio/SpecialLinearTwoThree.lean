/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Examples.RepresentationTheory.CharacterTable.Gallagher.SpecialLinearTwoThree

/-!
# The degree ratio over `Q₈` in `SL(2, 3)`

An example of the degree ratio over a normal subgroup
(`FDRep.finrank_dvd_finrank_and_finrank_div_finrank_dvd_index_of_liesOver`): for `G = SL(2, 3)`
and `N = Q₈` (`TauCeti.sl2ZModThreeQuaternionSubgroup`), of index `3`,

* the character of degree `3` lies over a nontrivial linear character `θ'` of `Q₈`, here the row
  of the table of `QuaternionGroup 2` with kernel the cyclic subgroup `⟨a 1⟩`, read through
  `TauCeti.sl2ZModThreeQuaternionEquiv`: the ratio is `3 / 1 = 3`, which divides `3`;
* the three characters of degree `2` lie over the character `χ₂` of degree two of `Q₈`
  (`GallagherSpecialLinearTwoThree.irreducibleCharactersOver_θ`): the ratio is `2 / 2 = 1`, which
  divides `3`.

The character of degree `3` is `3` at `±1` and `-1` at the six elements of order four of `Q₈`, so
its pairing with `θ'` is `(3 + 3 + 2 · (-1) + 4 · 1) / 8 = 1`.
-/

public section

namespace TauCeti.Examples.RepresentationTheory.DegreeRatioSpecialLinearTwoThree

open Matrix QuaternionGroup TauCeti.Examples.RepresentationTheory.GallagherSpecialLinearTwoThree

/-- Sums over `Q₈`. Local, so that `Nat.card N` stays in simp-normal form elsewhere. -/
noncomputable local instance fintypeN : Fintype N := Fintype.ofFinite _

/-- The character `χ₃` of degree three of `SL(2, 3)`. -/
noncomputable abbrev χ₃ : SpecialLinearGroup (Fin 2) (ZMod 3) → ℂ :=
  specialLinearTwoThreeCharacter ⟨3, by decide⟩

/-- The linear character `θ'` of `Q₈`: row `2` of the table of `QuaternionGroup 2`, read through
`TauCeti.sl2ZModThreeQuaternionEquiv`. -/
noncomputable def θ' (n : N) : ℂ :=
  (quaternionGroupTwoCharacterTable ⟨2, by decide⟩
    ((quaternionClassData 2).index (sl2ZModThreeQuaternionEquiv.symm n)) : ℂ)

/-- `θ'` is an irreducible character of `Q₈`. -/
theorem θ'_mem : θ' ∈ irreducibleCharacters ℂ N := by
  rw [← sl2ZModThreeQuaternionEquiv.comp_mem_irreducibleCharacters_iff,
    irreducibleCharacters_quaternionGroupTwo]
  exact ⟨⟨2, by decide⟩, funext fun x ↦ by simp [θ']⟩

/-- `θ'` is linear: `θ'(1) = 1`. -/
theorem θ'_one : θ' 1 = 1 := by
  have h : (quaternionClassData 2).index 1 = ⟨0, by decide⟩ := by decide
  have hv : quaternionGroupTwoCharacterTable ⟨2, by decide⟩ ⟨0, by decide⟩ = 1 := by
    rw [quaternionGroupTwoCharacterTable_apply]
    decide
  rw [θ', map_one, h, hv, Int.cast_one]

/-- `θ'` is not the trivial character: it is `-1` at the image of `xa 0`. -/
theorem θ'_xa_zero : θ' (sl2ZModThreeQuaternionEquiv (xa 0)) = -1 := by
  have h : (quaternionClassData 2).index (xa 0) = ⟨2, by decide⟩ := by decide
  have hv : quaternionGroupTwoCharacterTable ⟨2, by decide⟩ ⟨2, by decide⟩ = -1 := by
    rw [quaternionGroupTwoCharacterTable_apply]
    decide
  rw [θ', MulEquiv.symm_apply_apply, h, hv, Int.cast_neg, Int.cast_one]

/-- The values of `χ₃` at elements whose fourth power is trivial. -/
private theorem table_three_of_pow_four :
    ∀ g : SpecialLinearGroup (Fin 2) (ZMod 3), g ^ 4 = 1 →
      specialLinearTwoThreeExactCharacterTable ⟨3, by decide⟩
          (specialLinearTwoThreeClassData.index g) =
        if g = 1 ∨ g = -1 then 3 else -1 := by
  simp only [specialLinearTwoThreeExactCharacterTable_apply]
  decide +kernel

/-- `χ₃` is `3` at `±1` and `-1` at the other elements of `Q₈`. -/
private theorem χ₃_equiv (x : QuaternionGroup 2) :
    χ₃ (sl2ZModThreeQuaternionEquiv x) = if x = 1 ∨ x = a 2 then 3 else -1 := by
  have h4 : (sl2ZModThreeQuaternionHom x) ^ 4 = 1 := by
    rw [← map_pow, show x ^ 4 = 1 by revert x; decide, map_one]
  have hinj := sl2ZModThreeQuaternionHom_injective
  have h1 : sl2ZModThreeQuaternionHom x = 1 ↔ x = 1 := by
    rw [← map_one sl2ZModThreeQuaternionHom, hinj.eq_iff]
  have h2 : sl2ZModThreeQuaternionHom x = -1 ↔ x = a 2 := by
    rw [← sl2ZModThreeQuaternionHom_a_two, hinj.eq_iff]
  rw [χ₃, specialLinearTwoThreeCharacter_apply, coe_sl2ZModThreeQuaternionEquiv,
    table_three_of_pow_four _ h4]
  simp only [h1, h2]
  split_ifs <;> simp [map_ofNat]

/-- **The character of degree `3` lies over `θ'`.** -/
theorem χ₃_mem_irreducibleCharactersOver : χ₃ ∈ irreducibleCharactersOver ℂ N θ' := by
  rw [mem_irreducibleCharactersOver_iff_sum]
  refine ⟨specialLinearTwoThreeCharacter_mem_irreducibleCharacters _, ?_⟩
  rw [← sl2ZModThreeQuaternionEquiv.toEquiv.sum_comp]
  simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, ← map_inv, θ',
    MulEquiv.symm_apply_apply, χ₃_equiv]
  have key : ∑ x : QuaternionGroup 2, (if x = 1 ∨ x = a 2 then 3 else -1 : ℤ) *
      quaternionGroupTwoCharacterTable ⟨2, by decide⟩ ((quaternionClassData 2).index x⁻¹) = 8 := by
    simp only [quaternionGroupTwoCharacterTable_apply]
    decide +kernel
  have hc := congrArg (fun z : ℤ ↦ (z : ℂ)) key
  push_cast [apply_ite] at hc
  rw [hc]
  norm_num

/-- The value at `1` of row `i` is its degree. -/
private theorem character_one_eq {i : SpecialLinearTwoThreeClassIndex} {n : ℕ}
    (h : specialLinearTwoThreeCharacterDegrees i = n) : specialLinearTwoThreeCharacter i 1 = n := by
  rw [specialLinearTwoThreeCharacter_one, h]

/-- Reading a degree off the displayed list. -/
private theorem degree_eq {i : SpecialLinearTwoThreeClassIndex} {n : ℕ}
    (h : ![1, 1, 1, 3, 2, 2, 2] i = n) : specialLinearTwoThreeCharacterDegrees i = n := by
  rw [specialLinearTwoThreeCharacterDegrees_apply, h]

/-- **The degree ratio of `χ₃` over `θ'` is `3`**, which divides `|SL(2, 3) : Q₈| = 3`. -/
theorem χ₃_one_eq_and_dvd_index : χ₃ 1 = 3 * θ' 1 ∧ 3 ∣ N.index := by
  refine ⟨?_, by rw [index_sl2ZModThreeQuaternionSubgroup]⟩
  rw [θ'_one, mul_one, χ₃, character_one_eq (n := 3) (degree_eq (by decide))]
  norm_num

/-- **The characters over `χ₂` have degree ratio `1`**, which divides `|SL(2, 3) : Q₈| = 3`. -/
theorem apply_one_eq_and_dvd_index_of_mem_irreducibleCharactersOver_θ
    {ψ : SpecialLinearGroup (Fin 2) (ZMod 3) → ℂ} (hψ : ψ ∈ irreducibleCharactersOver ℂ N θ) :
    ψ 1 = 1 * θ 1 ∧ 1 ∣ N.index := by
  refine ⟨?_, one_dvd _⟩
  have h2 : χhat 1 = 2 := by
    rw [χhat, character_one_eq (n := 2) (degree_eq (by decide))]
    norm_num
  have hθ : θ 1 = 2 := by
    rw [← χhat_restrict, OneMemClass.coe_one, h2]
  rw [irreducibleCharactersOver_θ] at hψ
  rw [one_mul, hθ]
  rcases hψ with rfl | rfl | rfl
  · exact h2
  · dsimp only
    rw [h2, ω₁, character_one_eq (n := 1) (degree_eq (by decide))]
    norm_num
  · dsimp only
    rw [h2, ω₂, character_one_eq (n := 1) (degree_eq (by decide))]
    norm_num

end TauCeti.Examples.RepresentationTheory.DegreeRatioSpecialLinearTwoThree
