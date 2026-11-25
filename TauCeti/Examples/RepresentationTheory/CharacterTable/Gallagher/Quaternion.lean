/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.QuaternionEight
import TauCeti.RepresentationTheory.LinearCharacter.Basic

/-!
# Gallagher's correspondence needs an extension: the centre of `Q₈`

Let `N = Z(Q₈) = {1, a 2}` and let `θ` be its faithful linear character, `θ (a 2) = -1`. These
checks read the irreducible characters of `Q₈` off its certified character table
(`TauCeti.irreducibleCharacters_quaternionGroupTwo`) and prove:

* `θ` is an irreducible character of `N` with no extension to an irreducible character of `Q₈`:
  the four linear characters take the value `1` at `a 2`, and the remaining one has degree `2`.
  So of the hypotheses of `TauCeti.gallagher_bijOn` only the extension hypothesis fails;
* `Irr(Q₈ | θ)` has exactly one member, the character of degree `2`.

Set against the four irreducible characters of `Q₈ ⧸ N`, a count this file does not prove, this
illustrates why Gallagher's correspondence needs the extension hypothesis.
-/

public section

namespace TauCeti.Examples.RepresentationTheory.GallagherQuaternion

open QuaternionGroup

/-- The centre `{1, a 2}` of `Q₈`. -/
abbrev N : Subgroup (QuaternionGroup 2) := Subgroup.center (QuaternionGroup 2)

/-- The faithful linear character of the centre of `Q₈`. -/
def θ (n : N) : ℂ := if (n : QuaternionGroup 2) = 1 then 1 else -1

/-- The character of degree `2` of `Q₈`, the last row of its character table. -/
noncomputable def χ₂ (g : QuaternionGroup 2) : ℂ :=
  (quaternionGroupTwoCharacterTable ⟨4, by decide⟩ ((quaternionClassData 2).index g) : ℂ)

private theorem a_two_mem : (a 2 : QuaternionGroup 2) ∈ N := by decide

/-- `θ` as a homomorphism to `ℤˣ`. -/
private def θHom : N →* ℤˣ where
  toFun n := if (n : QuaternionGroup 2) = 1 then 1 else -1
  map_one' := by simp
  map_mul' := by decide

/-- `θ` is an irreducible character of `N`, the character of a one-dimensional representation. -/
theorem θ_mem : θ ∈ irreducibleCharacters ℂ N := by
  let ψ : N →* ℂˣ := (Units.map (Int.castRingHom ℂ).toMonoidHom).comp θHom
  have : (Representation.ofLinearCharacter ψ).IsIrreducible :=
    Representation.isIrreducible_of_finrank_eq_one _ (Module.finrank_self ℂ)
  convert character_mem_irreducibleCharacters (Representation.ofLinearCharacter ψ) using 1
  funext n
  rw [Representation.char_ofLinearCharacter]
  by_cases hn : n = 1 <;> simp [ψ, θ, θHom, hn]

private theorem univ_eq : (Finset.univ : Finset N) = {1, ⟨a 2, a_two_mem⟩} := by decide

/-- The sum defining `Irr(Q₈ | θ)`, at any function on `Q₈`. -/
private theorem sum_mul_θ_inv (χ : QuaternionGroup 2 → ℂ) :
    ∑ n : N, χ n * θ n⁻¹ = χ 1 - χ (a 2) := by
  rw [univ_eq, Finset.sum_pair (by decide)]
  have h : (a (-2) : QuaternionGroup 2) ≠ 1 := by decide
  simp [θ, h, sub_eq_add_neg]

private theorem index_one : (quaternionClassData 2).index 1 = ⟨0, by decide⟩ := by decide

private theorem index_a_two : (quaternionClassData 2).index (a 2) = ⟨1, by decide⟩ :=
  by decide

/-- `χ₂` is an irreducible character of `Q₈` of degree `2`. -/
theorem χ₂_mem : χ₂ ∈ irreducibleCharacters ℂ (QuaternionGroup 2) := by
  rw [irreducibleCharacters_quaternionGroupTwo]
  exact ⟨⟨4, by decide⟩, rfl⟩

/-- In the table of `Q₈`, the rows of degree `1` take the value `1` at the class of `a 2`. -/
private theorem table_one_of_degree_one :
    ∀ i, quaternionGroupTwoCharacterTable i ⟨0, by decide⟩ = 1 →
      quaternionGroupTwoCharacterTable i ⟨1, by decide⟩ = 1 := by
  simp only [quaternionGroupTwoCharacterTable_apply]
  decide

/-- In the table of `Q₈`, only the last row differs at the classes of `1` and `a 2`. -/
private theorem eq_four_of_ne :
    ∀ i, quaternionGroupTwoCharacterTable i ⟨0, by decide⟩ -
      quaternionGroupTwoCharacterTable i ⟨1, by decide⟩ ≠ 0 → i = ⟨4, by decide⟩ := by
  simp only [quaternionGroupTwoCharacterTable_apply]
  decide

/-- `θ` is an irreducible character of `N` with no extension to an irreducible character of
`Q₈`: of the hypotheses of `TauCeti.gallagher_bijOn`, only the extension hypothesis fails. -/
example : θ ∈ irreducibleCharacters ℂ N ∧
    ¬ ∃ χ ∈ irreducibleCharacters ℂ (QuaternionGroup 2), ∀ n : N, χ n = θ n := by
  refine ⟨θ_mem, ?_⟩
  rintro ⟨χ, hχ, hext⟩
  rw [irreducibleCharacters_quaternionGroupTwo] at hχ
  obtain ⟨i, rfl⟩ := hχ
  have h1 := hext 1
  have h2 := hext ⟨a 2, a_two_mem⟩
  have ha : (a 2 : QuaternionGroup 2) ≠ 1 := by decide
  simp only [OneMemClass.coe_one, θ, ite_true, index_one, index_a_two, ha, ite_false] at h1 h2
  have h1' : quaternionGroupTwoCharacterTable i ⟨0, by decide⟩ = 1 := by exact_mod_cast h1
  have h2' : quaternionGroupTwoCharacterTable i ⟨1, by decide⟩ = -1 := by exact_mod_cast h2
  rw [table_one_of_degree_one i h1'] at h2'
  exact absurd h2' (by decide)

/-- `Irr(Q₈ | θ)` consists of the single character `χ₂` of degree `2`. -/
example : irreducibleCharactersOver ℂ N θ = {χ₂} := by
  ext χ
  rw [mem_irreducibleCharactersOver_iff_sum, sum_mul_θ_inv, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hχ, hne⟩
    rw [irreducibleCharacters_quaternionGroupTwo] at hχ
    obtain ⟨i, rfl⟩ := hχ
    simp only [index_one, index_a_two] at hne
    obtain rfl := eq_four_of_ne i (by exact_mod_cast hne)
    rfl
  · rintro rfl
    refine ⟨χ₂_mem, ?_⟩
    simp only [χ₂, index_one, index_a_two]
    have : quaternionGroupTwoCharacterTable ⟨4, by decide⟩ ⟨0, by decide⟩ -
        quaternionGroupTwoCharacterTable ⟨4, by decide⟩ ⟨1, by decide⟩ ≠ 0 := by
      simp only [quaternionGroupTwoCharacterTable_apply]
      decide
    exact_mod_cast this

end TauCeti.Examples.RepresentationTheory.GallagherQuaternion
