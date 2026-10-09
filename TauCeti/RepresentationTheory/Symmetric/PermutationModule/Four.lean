/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Symmetric.YoungSubgroup
public import TauCeti.RepresentationTheory.Induction.Character
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.SymmetricFour
import TauCeti.RepresentationTheory.Induction.Permutation

/-!
# Young permutation characters on four letters

The Young permutation characters of shapes `(2,2)` and `(2,1,1)` have values
`6,2,2,0,0` and `12,2,0,0,0`, respectively, on the classes of cycle types
`1⁴`, `2·1²`, `2²`, `3·1`, and `4`. These are the characters obtained by inducing the
trivial representation from the corresponding Young subgroups.

Comparing with the certified integer character table of `S₄` gives formal expansion coefficients
`1,0,1,1,0` and `1,0,1,2,1`, in its row order: trivial, sign, degree two, standard,
and sign-twisted standard. These character identities hold over arbitrary fields; in characteristic
zero, the Hom-dimension theorems recover these coefficients as multiplicities. Together with the
one-row, all-ones, and singleton-second-row calculations, these give every Young permutation
character on four letters.

The fixed-tabloid calculation uses `quotientFiberSubgroupEquiv`: a fixed tabloid is a
colouring constant on cycles, with the prescribed row sizes. No division or characteristic
assumption enters the character values. Characteristic zero is needed only to recover
natural-number Hom dimensions from the character pairing.

## References

* G. James and M. Liebeck, *Representations and Characters of Groups*, Chapter 21.
* J.-P. Serre, *Linear Representations of Finite Groups*, §7.3.
-/

public section

namespace TauCeti

open Equiv Finset

private theorem youngBlock_val_two_two (μ : Nat.Partition 4) (hμ : μ.parts = {2, 2})
    (x : Fin 4) : (youngBlock μ x : ℕ) = (![0, 0, 1, 1] : Fin 4 → ℕ) x := by
  have hs : μ.parts.sort (· ≥ ·) = [2, 2] := by
    simp [hμ, Multiset.insert_eq_cons, Multiset.sort_cons]
  obtain ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, rfl⟩ := (youngBlocksEquiv μ).surjective x
  rw [youngBlock_youngBlocksEquiv]
  have hi' : i < 2 := by simpa [hs] using hi
  have hj' : j < 2 := by
    interval_cases i <;> simpa [List.get_eq_getElem, hs] using hj
  have hv : (youngBlocksEquiv μ ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ : ℕ) = 2 * i + j := by
    interval_cases i <;> simp [youngBlocksEquiv_apply, List.get_eq_getElem, hs]
  generalize hy : youngBlocksEquiv μ ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ = y at hv ⊢
  fin_cases y <;> dsimp at hv ⊢ <;> omega

private theorem youngBlock_val_two_one_one (μ : Nat.Partition 4)
    (hμ : μ.parts = {2, 1, 1}) (x : Fin 4) :
    (youngBlock μ x : ℕ) = (![0, 0, 1, 2] : Fin 4 → ℕ) x := by
  have hs : μ.parts.sort (· ≥ ·) = [2, 1, 1] := by
    simp [hμ, Multiset.insert_eq_cons, Multiset.sort_cons]
  obtain ⟨⟨⟨i, hi⟩, ⟨j, hj⟩⟩, rfl⟩ := (youngBlocksEquiv μ).surjective x
  rw [youngBlock_youngBlocksEquiv]
  have hi' : i < 3 := by simpa [hs] using hi
  have hj' : j < [2, 1, 1].getD i 0 := by
    interval_cases i <;> simpa [List.get_eq_getElem, hs] using hj
  have hv : (youngBlocksEquiv μ ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ : ℕ) =
      (if i = 0 then j else i + 1 + j) := by
    interval_cases i <;> simp [youngBlocksEquiv_apply, Fin.sum_univ_succ,
      List.get_eq_getElem, hs]
  generalize hy : youngBlocksEquiv μ ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ = y at hv ⊢
  interval_cases i <;> norm_num only [List.getD_cons_zero, List.getD_cons_succ,
    List.getD_nil] at hj'
  all_goals dsimp at hv ⊢
  all_goals fin_cases y
  all_goals dsimp at hv ⊢
  all_goals omega

private theorem youngSubgroup_two_two (μ : Nat.Partition 4) (hμ : μ.parts = {2, 2}) :
    youngSubgroup μ = fiberSubgroup (![0, 0, 1, 1] : Fin 4 → Fin 2) := by
  ext σ
  simp only [mem_youngSubgroup_iff, mem_fiberSubgroup, funext_iff, Function.comp_apply,
    ← Fin.val_inj, youngBlock_val_two_two μ hμ]
  exact forall_congr' fun x => by
    have hc : ∀ z : Fin 4,
        ((![0, 0, 1, 1] : Fin 4 → Fin 2) z : ℕ) = (![0, 0, 1, 1] : Fin 4 → ℕ) z := by
      decide
    rw [hc, hc]

private theorem youngSubgroup_two_one_one (μ : Nat.Partition 4)
    (hμ : μ.parts = {2, 1, 1}) :
    youngSubgroup μ = fiberSubgroup (![0, 0, 1, 2] : Fin 4 → Fin 3) := by
  ext σ
  simp only [mem_youngSubgroup_iff, mem_fiberSubgroup, funext_iff, Function.comp_apply,
    ← Fin.val_inj, youngBlock_val_two_one_one μ hμ]
  exact forall_congr' fun x => by
    have hc : ∀ z : Fin 4,
        ((![0, 0, 1, 2] : Fin 4 → Fin 3) z : ℕ) = (![0, 0, 1, 2] : Fin 4 → ℕ) z := by
      decide
    rw [hc, hc]

end TauCeti

namespace Nat.Partition

open TauCeti Equiv Finset

/-- The induced trivial character of the Young subgroup of shape `(2,2)` has values
`6,2,2,0,0` on the five numbered classes of `S₄`, over every field. -/
theorem character_indFDRep_trivial_parts_two_two {k : Type*} [Field k]
    (μ : Nat.Partition 4) (hμ : μ.parts = {2, 2}) (j : SymmetricGroupFourClassIndex) :
    (indFDRep (FDRep.of (Representation.trivial k (youngSubgroup μ) k))).character
      (symmetricGroupFourClassData.rep j) =
      (![6, 2, 2, 0, 0] : Fin 5 → k) (j.cast numClasses_symmetricGroupFourClassData) := by
  rw [character_indFDRep, FDRep.of_ρ', char_ind_trivial, youngSubgroup_two_two μ hμ,
    card_fixedPoints_quotient_fiberSubgroup]
  have hc : ∀ j : SymmetricGroupFourClassIndex,
      #{c : Fin 4 → Fin 2 | c ∘ symmetricGroupFourClassData.rep j = c ∧
        ∀ i, #{a | c a = i} = #{a | (![0, 0, 1, 1] : Fin 4 → Fin 2) a = i}} =
      (![6, 2, 2, 0, 0] : Fin 5 → ℕ) (j.cast numClasses_symmetricGroupFourClassData) := by
        intro j
        fin_cases j <;> decide
  convert congrArg (fun n : ℕ => (n : k)) (hc j) using 1
  · -- The counting theorem uses classical decisions; the finite check uses computable ones.
    congr 1
    congr 1
    ext c
    congr!
  · fin_cases j <;> norm_num [Fin.cast, Matrix.cons_val]

/-- The induced trivial character of the Young subgroup of shape `(2,1,1)` has values
`12,2,0,0,0` on the five numbered classes of `S₄`, over every field. -/
theorem character_indFDRep_trivial_parts_two_one_one {k : Type*} [Field k]
    (μ : Nat.Partition 4) (hμ : μ.parts = {2, 1, 1}) (j : SymmetricGroupFourClassIndex) :
    (indFDRep (FDRep.of (Representation.trivial k (youngSubgroup μ) k))).character
      (symmetricGroupFourClassData.rep j) =
      (![12, 2, 0, 0, 0] : Fin 5 → k) (j.cast numClasses_symmetricGroupFourClassData) := by
  rw [character_indFDRep, FDRep.of_ρ', char_ind_trivial, youngSubgroup_two_one_one μ hμ,
    card_fixedPoints_quotient_fiberSubgroup]
  have hc : ∀ j : SymmetricGroupFourClassIndex,
      #{c : Fin 4 → Fin 3 | c ∘ symmetricGroupFourClassData.rep j = c ∧
        ∀ i, #{a | c a = i} = #{a | (![0, 0, 1, 2] : Fin 4 → Fin 3) a = i}} =
      (![12, 2, 0, 0, 0] : Fin 5 → ℕ) (j.cast numClasses_symmetricGroupFourClassData) := by
        intro j
        fin_cases j <;> decide
  convert congrArg (fun n : ℕ => (n : k)) (hc j) using 1
  · -- The counting theorem uses classical decisions; the finite check uses computable ones.
    congr 1
    congr 1
    ext c
    congr!
  · fin_cases j <;> norm_num [Fin.cast, Matrix.cons_val]

/-- The `(2,2)` induced character is the sum of the trivial, degree-two, and standard
rows of the certified `S₄` character table. -/
theorem character_indFDRep_trivial_parts_two_two_eq_sum {k : Type*} [Field k]
    (μ : Nat.Partition 4) (hμ : μ.parts = {2, 2}) (g : Perm (Fin 4)) :
    (indFDRep (FDRep.of (Representation.trivial k (youngSubgroup μ) k))).character g =
      ((symmetricGroupFourCharacterTable ⟨0, by decide⟩ (symmetricGroupFourClassData.index g) +
        symmetricGroupFourCharacterTable ⟨2, by decide⟩ (symmetricGroupFourClassData.index g) +
        symmetricGroupFourCharacterTable ⟨3, by decide⟩
          (symmetricGroupFourClassData.index g) : ℤ) : k) := by
  let A := indFDRep (FDRep.of (Representation.trivial k (youngSubgroup μ) k))
  have hg := ClassFunction.eq_of_isConj (ClassFunction.ofCharacter A.ρ)
    (symmetricGroupFourClassData.isConj_rep_index g)
  simp only [ClassFunction.ofCharacter_apply] at hg
  have ha : A.character (symmetricGroupFourClassData.rep (symmetricGroupFourClassData.index g)) =
      A.character g := hg
  rw [← ha, character_indFDRep_trivial_parts_two_two μ hμ]
  generalize symmetricGroupFourClassData.index g = j
  have hc : ∀ j : SymmetricGroupFourClassIndex,
      symmetricGroupFourCharacterTable ⟨0, by decide⟩ j +
        symmetricGroupFourCharacterTable ⟨2, by decide⟩ j +
        symmetricGroupFourCharacterTable ⟨3, by decide⟩ j =
      (![6, 2, 2, 0, 0] : Fin 5 → ℤ) (j.cast numClasses_symmetricGroupFourClassData) := by
    simp only [symmetricGroupFourCharacterTable_apply]
    intro j
    fin_cases j <;> decide
  rw [hc]
  fin_cases j <;> norm_num [Fin.cast, Matrix.cons_val]

/-- The `(2,1,1)` induced character is the sum of the trivial and degree-two rows,
twice the standard row, and the sign-twisted standard row of the certified `S₄` table. -/
theorem character_indFDRep_trivial_parts_two_one_one_eq_sum {k : Type*} [Field k]
    (μ : Nat.Partition 4) (hμ : μ.parts = {2, 1, 1}) (g : Perm (Fin 4)) :
    (indFDRep (FDRep.of (Representation.trivial k (youngSubgroup μ) k))).character g =
      ((symmetricGroupFourCharacterTable ⟨0, by decide⟩ (symmetricGroupFourClassData.index g) +
        symmetricGroupFourCharacterTable ⟨2, by decide⟩ (symmetricGroupFourClassData.index g) +
        2 * symmetricGroupFourCharacterTable ⟨3, by decide⟩ (symmetricGroupFourClassData.index g) +
        symmetricGroupFourCharacterTable ⟨4, by decide⟩
          (symmetricGroupFourClassData.index g) : ℤ) : k) := by
  let A := indFDRep (FDRep.of (Representation.trivial k (youngSubgroup μ) k))
  have hg := ClassFunction.eq_of_isConj (ClassFunction.ofCharacter A.ρ)
    (symmetricGroupFourClassData.isConj_rep_index g)
  simp only [ClassFunction.ofCharacter_apply] at hg
  have ha : A.character (symmetricGroupFourClassData.rep (symmetricGroupFourClassData.index g)) =
      A.character g := hg
  rw [← ha, character_indFDRep_trivial_parts_two_one_one μ hμ]
  generalize symmetricGroupFourClassData.index g = j
  have hc : ∀ j : SymmetricGroupFourClassIndex,
      symmetricGroupFourCharacterTable ⟨0, by decide⟩ j +
        symmetricGroupFourCharacterTable ⟨2, by decide⟩ j +
        2 * symmetricGroupFourCharacterTable ⟨3, by decide⟩ j +
        symmetricGroupFourCharacterTable ⟨4, by decide⟩ j =
      (![12, 2, 0, 0, 0] : Fin 5 → ℤ) (j.cast numClasses_symmetricGroupFourClassData) := by
    simp only [symmetricGroupFourCharacterTable_apply]
    intro j
    fin_cases j <;> decide
  rw [hc]
  fin_cases j <;> norm_num [Fin.cast, Matrix.cons_val]

end Nat.Partition

namespace FDRep

open TauCeti Nat.Partition Equiv Finset

/-- The multiplicities in the Young representation of shape `(2,2)`, indexed by the certified
`S₄` character rows, are `1,0,1,1,0`. The character hypothesis selects a row; no simplicity
or algebraic-closure assumption is needed for the Hom-dimension equality. -/
theorem finrank_hom_indFDRep_trivial_parts_two_two {k : Type*} [Field k] [CharZero k]
    (V : FDRep k (Perm (Fin 4))) (μ : Nat.Partition 4) (hμ : μ.parts = {2, 2})
    (i : Fin 5)
    (hV : ∀ j, V.character (symmetricGroupFourClassData.rep j) =
      (symmetricGroupFourCharacterTable
        (i.cast numClasses_symmetricGroupFourClassData.symm) j : k)) :
    Module.finrank k (V ⟶ indFDRep (FDRep.of (Representation.trivial k (youngSubgroup μ) k))) =
      (![1, 0, 1, 1, 0] : Fin 5 → ℕ) i := by
  have hchar : ∀ g, V.character g =
      (symmetricGroupFourCharacterTable (i.cast numClasses_symmetricGroupFourClassData.symm)
        (symmetricGroupFourClassData.index g) : k) := by
    intro g
    have hg := ClassFunction.eq_of_isConj (ClassFunction.ofCharacter V.ρ)
      (symmetricGroupFourClassData.isConj_rep_index g)
    simp only [ClassFunction.ofCharacter_apply] at hg
    exact hg.symm.trans (hV _)
  have hc : ∑ g : Perm (Fin 4),
      (symmetricGroupFourCharacterTable ⟨0, by decide⟩ (symmetricGroupFourClassData.index g) +
        symmetricGroupFourCharacterTable ⟨2, by decide⟩ (symmetricGroupFourClassData.index g) +
        symmetricGroupFourCharacterTable ⟨3, by decide⟩ (symmetricGroupFourClassData.index g)) *
      symmetricGroupFourCharacterTable (i.cast numClasses_symmetricGroupFourClassData.symm)
        (symmetricGroupFourClassData.index g⁻¹) =
      24 * ((![1, 0, 1, 1, 0] : Fin 5 → ℕ) i : ℤ) := by
    simp only [symmetricGroupFourCharacterTable_apply]
    fin_cases i <;> decide
  let : Invertible (Nat.card (Perm (Fin 4)) : k) := invertibleOfNonzero (by
    rw [Nat.card_perm, Nat.card_fin]; norm_num)
  apply Nat.cast_injective (R := k)
  rw [← scalar_product_char_eq_finrank_equivariant]
  simp_rw [character_indFDRep_trivial_parts_two_two_eq_sum μ hμ, hchar,
    ← Int.cast_mul]
  rw [← Int.cast_sum, hc, Int.cast_mul, Nat.card_perm, Nat.card_fin]
  norm_num
  ring

/-- The multiplicities in the Young representation of shape `(2,1,1)`, indexed by the certified
`S₄` character rows, are `1,0,1,2,1`. The character hypothesis selects a row. -/
theorem finrank_hom_indFDRep_trivial_parts_two_one_one {k : Type*} [Field k] [CharZero k]
    (V : FDRep k (Perm (Fin 4))) (μ : Nat.Partition 4) (hμ : μ.parts = {2, 1, 1})
    (i : Fin 5)
    (hV : ∀ j, V.character (symmetricGroupFourClassData.rep j) =
      (symmetricGroupFourCharacterTable
        (i.cast numClasses_symmetricGroupFourClassData.symm) j : k)) :
    Module.finrank k (V ⟶ indFDRep (FDRep.of (Representation.trivial k (youngSubgroup μ) k))) =
      (![1, 0, 1, 2, 1] : Fin 5 → ℕ) i := by
  have hchar : ∀ g, V.character g =
      (symmetricGroupFourCharacterTable (i.cast numClasses_symmetricGroupFourClassData.symm)
        (symmetricGroupFourClassData.index g) : k) := by
    intro g
    have hg := ClassFunction.eq_of_isConj (ClassFunction.ofCharacter V.ρ)
      (symmetricGroupFourClassData.isConj_rep_index g)
    simp only [ClassFunction.ofCharacter_apply] at hg
    exact hg.symm.trans (hV _)
  have hc : ∑ g : Perm (Fin 4),
      (symmetricGroupFourCharacterTable ⟨0, by decide⟩ (symmetricGroupFourClassData.index g) +
        symmetricGroupFourCharacterTable ⟨2, by decide⟩ (symmetricGroupFourClassData.index g) +
        2 * symmetricGroupFourCharacterTable ⟨3, by decide⟩ (symmetricGroupFourClassData.index g) +
        symmetricGroupFourCharacterTable ⟨4, by decide⟩ (symmetricGroupFourClassData.index g)) *
      symmetricGroupFourCharacterTable (i.cast numClasses_symmetricGroupFourClassData.symm)
        (symmetricGroupFourClassData.index g⁻¹) =
      24 * ((![1, 0, 1, 2, 1] : Fin 5 → ℕ) i : ℤ) := by
    simp only [symmetricGroupFourCharacterTable_apply]
    fin_cases i <;> decide
  let : Invertible (Nat.card (Perm (Fin 4)) : k) := invertibleOfNonzero (by
    rw [Nat.card_perm, Nat.card_fin]; norm_num)
  apply Nat.cast_injective (R := k)
  rw [← scalar_product_char_eq_finrank_equivariant]
  simp_rw [character_indFDRep_trivial_parts_two_one_one_eq_sum μ hμ, hchar,
    ← Int.cast_mul]
  rw [← Int.cast_sum, hc, Int.cast_mul, Nat.card_perm, Nat.card_fin]
  norm_num
  ring

end FDRep
