/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Automorphism
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.SpecialLinearTwoThree
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.QuaternionEight
public import TauCeti.RepresentationTheory.CharacterTable.Gallagher

/-!
# Gallagher's correspondence for `SL(2, 3)` over the character of degree two of `Q₈`

Let `G = SL(2, 3)`, `N = Q₈` its quaternion subgroup (`TauCeti.sl2ZModThreeQuaternionSubgroup`)
and `θ` the restriction to `N` of the rational character `χhat` of degree two of `G`, the fifth row
of the certified table (`TauCeti.irreducibleCharacters_specialLinearTwoThree`). These checks read
the characters of `G` off that table and prove:

* `θ` is the character `χ₂` of degree two of `Q₈`: precomposed with
  `TauCeti.sl2ZModThreeQuaternionEquiv` it is the last row of the table of `QuaternionGroup 2`;
* `Irr(G | θ)` consists of the three characters `χhat`, `χhat ω` and `χhat ω²` of degree two,
  where `ω` and `ω²` are the nonreal linear characters of `G`, inflated from `G ⧸ N ≅ C₃`, and
  these three are distinct;
* so, by `TauCeti.gallagher_bijOn` with the extension `χhat` of `θ`, the quotient `G ⧸ N` has
  exactly three irreducible characters.

On `N` the character `χhat` takes the value `2` at `1`, `-2` at `-1` and `0` at the six elements of
order four; every element of `N` has order dividing four, because its order divides both `|N| = 8`
and the exponent `12` of `G`.
-/

public section

namespace TauCeti.Examples.RepresentationTheory.GallagherSpecialLinearTwoThree

open Matrix QuaternionGroup

/-- The quaternion subgroup `Q₈` of `SL(2, 3)`. -/
abbrev N : Subgroup (SpecialLinearGroup (Fin 2) (ZMod 3)) := sl2ZModThreeQuaternionSubgroup

/-- The rational character `χhat` of degree two of `SL(2, 3)`. -/
noncomputable abbrev χhat : SpecialLinearGroup (Fin 2) (ZMod 3) → ℂ :=
  specialLinearTwoThreeCharacter ⟨4, by decide⟩

/-- The linear character `ω` of `SL(2, 3)`, with value `ω = exp (2πi/3)` at `t`. -/
noncomputable abbrev ω₁ : SpecialLinearGroup (Fin 2) (ZMod 3) → ℂ :=
  specialLinearTwoThreeCharacter ⟨1, by decide⟩

/-- The linear character `ω²` of `SL(2, 3)`, the complex conjugate of `ω₁`. -/
noncomputable abbrev ω₂ : SpecialLinearGroup (Fin 2) (ZMod 3) → ℂ :=
  specialLinearTwoThreeCharacter ⟨2, by decide⟩

/-- The restriction of `χhat` to `Q₈`. -/
@[expose] noncomputable def θ (n : N) : ℂ := χhat n

/-- Sums over `Q₈`. Local, so that `Nat.card N` stays in simp-normal form elsewhere. -/
noncomputable local instance fintypeN : Fintype N := Fintype.ofFinite _

private theorem index_neg_one : specialLinearTwoThreeClassData.index (-1) = ⟨1, by decide⟩ := by
  decide

/-- At `-1`, row `i` takes the value in the second column. -/
private theorem specialLinearTwoThreeCharacter_neg_one (i : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeCharacter i (-1) =
      Cyclotomic.complexEmbedding (specialLinearTwoThreeExactCharacterTable i ⟨1, by decide⟩) := by
  rw [specialLinearTwoThreeCharacter_apply, index_neg_one]

/-- The values of `χhat` at elements whose fourth power is trivial. -/
private theorem table_four_of_pow_four :
    ∀ g : SpecialLinearGroup (Fin 2) (ZMod 3), g ^ 4 = 1 →
      specialLinearTwoThreeExactCharacterTable ⟨4, by decide⟩
          (specialLinearTwoThreeClassData.index g) =
        if g = 1 then 2 else if g = -1 then -2 else 0 := by
  simp only [specialLinearTwoThreeExactCharacterTable_apply]
  decide +kernel

/-- Every element of `Q₈` has fourth power `1`: its order divides `8` and the exponent `12`. -/
private theorem pow_four_eq_one (n : N) : (n : SpecialLinearGroup (Fin 2) (ZMod 3)) ^ 4 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one]
  have h8 : orderOf (n : SpecialLinearGroup (Fin 2) (ZMod 3)) ∣ 8 := by
    rw [Subgroup.orderOf_coe, ← natCard_sl2ZModThreeQuaternionSubgroup]
    exact orderOf_dvd_natCard n
  have h12 : orderOf (n : SpecialLinearGroup (Fin 2) (ZMod 3)) ∣ 12 :=
    exponent_specialLinearGroup_two_three ▸ Monoid.order_dvd_exponent _
  exact (Nat.dvd_gcd h8 h12).trans (by decide)

/-- `-1` as an element of `Q₈`. -/
private def negOne : N := ⟨-1, neg_one_mem_sl2ZModThreeQuaternionSubgroup⟩

private theorem coe_negOne : (negOne : SpecialLinearGroup (Fin 2) (ZMod 3)) = -1 :=
  rfl

private theorem negOne_inv : negOne⁻¹ = negOne :=
  Subtype.ext (by rw [Subgroup.coe_inv, coe_negOne]; decide)

private theorem one_ne_negOne : (1 : N) ≠ negOne := by
  rw [Ne, Subtype.ext_iff]
  decide

/-- `θ` is `2` at `1`, `-2` at `-1` and `0` elsewhere on `Q₈`. -/
private theorem θ_eq (n : N) :
    θ n = (if n = 1 then 2 else 0) + (if n = negOne then -2 else 0) := by
  rw [θ, χhat, specialLinearTwoThreeCharacter_apply, table_four_of_pow_four _ (pow_four_eq_one n)]
  have h1 : ((n : SpecialLinearGroup (Fin 2) (ZMod 3)) = 1) ↔ n = 1 := OneMemClass.coe_eq_one
  have h2 : ((n : SpecialLinearGroup (Fin 2) (ZMod 3)) = -1) ↔ n = negOne := by
    rw [Subtype.ext_iff, coe_negOne]
  simp only [h1, h2]
  by_cases ha : n = 1
  · subst ha
    simp [one_ne_negOne, map_ofNat]
  · by_cases hb : n = negOne
    · subst hb
      simp [one_ne_negOne.symm, map_ofNat]
    · simp [ha, hb]

private theorem θ_inv (n : N) : θ n⁻¹ = θ n := by
  have h1 : n⁻¹ = 1 ↔ n = 1 := inv_eq_one
  have h2 : n⁻¹ = negOne ↔ n = negOne := by
    rw [inv_eq_iff_eq_inv, negOne_inv]
  simp only [θ_eq, h1, h2]

/-- **The defining sum of `Irr(G | θ)`**, at any function on `G`, is `2 ψ(1) - 2 ψ(-1)`. -/
private theorem sum_mul_θ_inv (ψ : SpecialLinearGroup (Fin 2) (ZMod 3) → ℂ) :
    ∑ n : N, ψ n * θ n⁻¹ = 2 * ψ 1 - 2 * ψ (-1) := by
  simp only [θ_inv]
  simp [θ_eq, mul_add, Finset.sum_add_distrib, coe_negOne]
  ring

/-- `χhat` restricts to `θ` on `Q₈`. -/
theorem χhat_restrict (n : N) : χhat n = θ n :=
  rfl

/-- At `1` and at `-1`, `θ` takes the values of `χhat`. -/
private theorem θ_one : θ 1 = χhat 1 := by
  rw [← χhat_restrict, OneMemClass.coe_one]

private theorem θ_negOne : θ negOne = χhat (-1) :=
  (χhat_restrict negOne).symm

/-- **`θ` is an irreducible character of `Q₈`**: it is a character, and its norm is
`(2² + 2²)/8 = 1`. -/
theorem θ_mem : θ ∈ irreducibleCharacters ℂ N := by
  obtain ⟨W, hW⟩ := irreducibleCharacters_subset_range
    (specialLinearTwoThreeCharacter_mem_irreducibleCharacters ⟨4, by decide⟩)
  have hθW : θ = W.character ∘ N.subtype := by
    rw [hW]
    exact (funext χhat_restrict).symm
  have hv : θ ∈ virtualCharacters ℂ N :=
    hθW ▸ comp_mem_virtualCharacters N.subtype (character_mem_virtualCharacters W)
  refine mem_irreducibleCharacters_of_characterPairing_self_eq_one
    (f := ⟨θ, virtualCharacters_le_classFunction hv⟩) hv ?_ (n := 2) ?_
  · have h := sum_mul_θ_inv χhat
    simp only [χhat_restrict] at h
    rw [ClassFunction.characterPairing_apply]
    dsimp only
    rw [h, natCard_sl2ZModThreeQuaternionSubgroup, ← θ_one, ← θ_negOne]
    simp only [θ_eq, one_ne_negOne, one_ne_negOne.symm]
    norm_num
  · simp only [θ_eq, one_ne_negOne]
    norm_num

/-- The only row of degree two in the table of `Q₈` is the last. -/
private theorem eq_four_of_degree_two :
    ∀ j, quaternionGroupTwoCharacterTable j ⟨0, by decide⟩ = 2 → j = ⟨4, by decide⟩ := by
  simp only [quaternionGroupTwoCharacterTable_apply]
  decide

/-- **`θ` is the character `χ₂` of degree two of `Q₈`**: read through
`TauCeti.sl2ZModThreeQuaternionEquiv`, it is the last row of the table of `QuaternionGroup 2`. -/
example : θ ∘ sl2ZModThreeQuaternionEquiv = fun x : QuaternionGroup 2 =>
    (quaternionGroupTwoCharacterTable ⟨4, by decide⟩ ((quaternionClassData 2).index x) : ℂ) := by
  have h := sl2ZModThreeQuaternionEquiv.comp_mem_irreducibleCharacters_iff.2 θ_mem
  rw [irreducibleCharacters_quaternionGroupTwo] at h
  obtain ⟨j, hj⟩ := h
  have h1 := congrFun hj 1
  simp only [Function.comp_apply, map_one] at h1
  simp only [θ_eq, one_ne_negOne] at h1
  have hidx : (quaternionClassData 2).index 1 = ⟨0, by decide⟩ := by decide
  rw [hidx] at h1
  have h1' : quaternionGroupTwoCharacterTable j ⟨0, by decide⟩ = 2 := by exact_mod_cast h1
  rw [← hj, eq_four_of_degree_two j h1']

/-- In the table of `SL(2, 3)`, only the three rows of degree two differ at `1` and `-1`. -/
private theorem degree_ne_table_one_iff :
    ∀ i : SpecialLinearTwoThreeClassIndex,
      (specialLinearTwoThreeCharacterDegrees i : Cyclotomic 12) ≠
          specialLinearTwoThreeExactCharacterTable i ⟨1, by decide⟩ ↔
        i = ⟨4, by decide⟩ ∨ i = ⟨5, by decide⟩ ∨ i = ⟨6, by decide⟩ := by
  simp only [specialLinearTwoThreeCharacterDegrees_apply,
    specialLinearTwoThreeExactCharacterTable_apply]
  decide +kernel

/-- Row `i` takes the same value at `1` and `-1` exactly when its degree is the entry in the
second column. -/
private theorem character_one_eq_neg_one_iff (i : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeCharacter i 1 = specialLinearTwoThreeCharacter i (-1) ↔
      (specialLinearTwoThreeCharacterDegrees i : Cyclotomic 12) =
        specialLinearTwoThreeExactCharacterTable i ⟨1, by decide⟩ := by
  simp [specialLinearTwoThreeCharacter_one, specialLinearTwoThreeCharacter_neg_one,
    ← Cyclotomic.complexEmbedding_injective.eq_iff]

/-- `χhat ω` and `χhat ω²` are the last two rows of the table. -/
private theorem χhat_mul_ω₁ :
    (fun g => χhat g * ω₁ g) = specialLinearTwoThreeCharacter ⟨5, by decide⟩ := by
  funext g
  simp only [χhat, ω₁, specialLinearTwoThreeCharacter_apply]
  rw [← map_mul,
    (specialLinearTwoThreeExactCharacterTable_row_four_mul _).1]

private theorem χhat_mul_ω₂ :
    (fun g => χhat g * ω₂ g) = specialLinearTwoThreeCharacter ⟨6, by decide⟩ := by
  funext g
  simp only [χhat, ω₂, specialLinearTwoThreeCharacter_apply]
  rw [← map_mul,
    (specialLinearTwoThreeExactCharacterTable_row_four_mul _).2]

/-- **`Irr(SL(2, 3) | χ₂)` consists of `χhat`, `χhat ω` and `χhat ω²`.** -/
theorem irreducibleCharactersOver_θ :
    irreducibleCharactersOver ℂ N θ =
      {χhat, fun g => χhat g * ω₁ g, fun g => χhat g * ω₂ g} := by
  ext ψ
  rw [mem_irreducibleCharactersOver_iff_sum, sum_mul_θ_inv, χhat_mul_ω₁, χhat_mul_ω₂]
  have key (i : SpecialLinearTwoThreeClassIndex) :
      2 * specialLinearTwoThreeCharacter i 1 - 2 * specialLinearTwoThreeCharacter i (-1) ≠ 0 ↔
        i = ⟨4, by decide⟩ ∨ i = ⟨5, by decide⟩ ∨ i = ⟨6, by decide⟩ := by
    refine Iff.trans ?_ ((character_one_eq_neg_one_iff i).not.trans (degree_ne_table_one_iff i))
    simp [← mul_sub, sub_eq_zero]
  constructor
  · rintro ⟨hψ, hne⟩
    obtain ⟨i, rfl⟩ : ψ ∈ Set.range specialLinearTwoThreeCharacter := by
      rw [irreducibleCharacters_specialLinearTwoThree] at hψ
      exact hψ
    rcases (key i).1 hne with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨specialLinearTwoThreeCharacter_mem_irreducibleCharacters _, (key _).2 (Or.inl rfl)⟩
    · exact ⟨specialLinearTwoThreeCharacter_mem_irreducibleCharacters _,
        (key _).2 (Or.inr (Or.inl rfl))⟩
    · exact ⟨specialLinearTwoThreeCharacter_mem_irreducibleCharacters _,
        (key _).2 (Or.inr (Or.inr rfl))⟩

/-- The value of row `i` at `t`, the fourth column of the table. -/
private theorem specialLinearTwoThreeCharacter_t (i : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeCharacter i sl2ZModThreeT =
      Cyclotomic.complexEmbedding (specialLinearTwoThreeExactCharacterTable i ⟨3, by decide⟩) := by
  have h : specialLinearTwoThreeClassData.index sl2ZModThreeT = ⟨3, by decide⟩ := by decide
  rw [specialLinearTwoThreeCharacter_apply, h]

/-- **The three characters of `SL(2, 3)` over `χ₂` are distinct**: at `t`, of order three, they
take the values `-1`, `-ω` and `-ω²`. -/
theorem ncard_irreducibleCharactersOver_θ : (irreducibleCharactersOver ℂ N θ).ncard = 3 := by
  rw [irreducibleCharactersOver_θ, χhat_mul_ω₁, χhat_mul_ω₂]
  have hne (i j : SpecialLinearTwoThreeClassIndex)
      (h : specialLinearTwoThreeExactCharacterTable i ⟨3, by decide⟩ ≠
        specialLinearTwoThreeExactCharacterTable j ⟨3, by decide⟩) :
      specialLinearTwoThreeCharacter i ≠ specialLinearTwoThreeCharacter j := by
    intro hij
    have := congrFun hij sl2ZModThreeT
    rw [specialLinearTwoThreeCharacter_t, specialLinearTwoThreeCharacter_t,
      Cyclotomic.complexEmbedding_injective.eq_iff] at this
    exact h this
  refine Set.ncard_eq_three.2 ⟨_, _, _, hne _ _ ?_, hne _ _ ?_, hne _ _ ?_, rfl⟩ <;>
    simp only [specialLinearTwoThreeExactCharacterTable_apply] <;> decide +kernel

/-- **Gallagher's correspondence counts `Irr(G ⧸ N)`**: `β ↦ χhat · (β ∘ π)` is a bijection from
`Irr(SL(2, 3) ⧸ Q₈)` onto the three characters over `χ₂`, so the quotient, which is cyclic of order
three, has three irreducible characters. -/
example : (irreducibleCharacters ℂ (SpecialLinearGroup (Fin 2) (ZMod 3) ⧸ N)).ncard = 3 := by
  have h := gallagher_bijOn
    (specialLinearTwoThreeCharacter_mem_irreducibleCharacters ⟨4, by decide⟩) θ_mem χhat_restrict
  exact h.ncard_eq.trans ncard_irreducibleCharactersOver_θ

end TauCeti.Examples.RepresentationTheory.GallagherSpecialLinearTwoThree
