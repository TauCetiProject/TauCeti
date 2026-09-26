/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Alternating.Five
public import TauCeti.RingTheory.Cyclotomic.Conjugation

/-!
# Exact cyclotomic candidate-table data for the alternating group of degree five

This file records exact candidate character-table data for `A₅`. Its conjugacy classes use the
numbering fixed by `TauCeti.alternatingGroupFiveClassData` and have sizes `1`, `15`, `20`, `12`,
and `12`.
If `ζ` is the distinguished primitive fifth root in `TauCeti.Cyclotomic 5`, the two
quadratic values have canonical representatives

```
φ  = -ζ³ - ζ²,
φ' =  ζ³ + ζ² + 1.
```

These are the roots of `X² - X - 1`. The two degree-three rows exchange `φ` and `φ'` on the
two classes of five-cycles. The central-to-ordinary conversion, degree constraints, and Hermitian
row orthogonality are proved in the computable cyclotomic coefficient ring. These identities do
not by themselves certify that the rows are the irreducible characters of `A₅`.

## Main definitions

* `TauCeti.alternatingGroupFiveCandidateCentralCharacterTable`: candidate central-character data.
* `TauCeti.alternatingGroupFiveCandidateCharacterTable`: candidate ordinary character data.
* `TauCeti.alternatingGroupFiveCandidateCharacterDegrees`: the candidate degrees `1`, `3`, `3`,
  `4`, and `5`.

## Main results

* `TauCeti.alternatingGroupFive_candidateDegree_mul_candidateCentralCharacterTable`: the candidate
  central and ordinary data agree under the division-free conversion formula.
* `TauCeti.alternatingGroupFive_candidateCharacterTable_orthogonal`: the candidate rows satisfy
  Hermitian orthogonality.

## References

The candidate is the classical displayed `A₅` table; see J.-P. Serre, *Linear Representations of
Finite Groups*, §5.2.
-/

public section

namespace TauCeti

open Matrix

/-- The numbered conjugacy classes of the alternating group of degree five. -/
abbrev AlternatingGroupFiveClassIndex := Fin alternatingGroupFiveClassData.numClasses

/-- The positive golden-ratio character value `(1 + √5) / 2`, represented in
`TauCeti.Cyclotomic 5`. -/
abbrev alternatingGroupFiveGolden : Cyclotomic 5 :=
  Cyclotomic.ofCoeffList 5 [-1, -1, 0, 0]

/-- The Galois conjugate `(1 - √5) / 2` of the positive golden-ratio character value. -/
abbrev alternatingGroupFiveGoldenGaloisConjugate : Cyclotomic 5 :=
  Cyclotomic.ofCoeffList 5 [1, 1, 0, 1]

/-- The two golden-ratio character values sum to one. -/
theorem alternatingGroupFiveGolden_add_galoisConjugate :
    alternatingGroupFiveGolden + alternatingGroupFiveGoldenGaloisConjugate = 1 := by
  decide

/-- The two golden-ratio character values have product negative one. -/
theorem alternatingGroupFiveGolden_mul_galoisConjugate :
    alternatingGroupFiveGolden * alternatingGroupFiveGoldenGaloisConjugate = -1 := by
  decide

/-- The two golden-ratio character values are distinct. -/
theorem alternatingGroupFiveGolden_ne_galoisConjugate :
    alternatingGroupFiveGolden ≠ alternatingGroupFiveGoldenGaloisConjugate := by
  decide

/-- Both golden-ratio character values are fixed by exact complex conjugation. -/
@[simp]
theorem star_alternatingGroupFiveGolden : star alternatingGroupFiveGolden =
    alternatingGroupFiveGolden := by
  apply Cyclotomic.ext
  intro j
  fin_cases j <;> decide

/-- The conjugate golden-ratio character value is also real. -/
@[simp]
theorem star_alternatingGroupFiveGoldenGaloisConjugate :
    star alternatingGroupFiveGoldenGaloisConjugate =
      alternatingGroupFiveGoldenGaloisConjugate := by
  apply Cyclotomic.ext
  intro j
  fin_cases j <;> decide

/-- Exact candidate central-character data for `A₅`. Columns are the identity, double
transpositions, three-cycles, and the two classes of five-cycles. -/
def alternatingGroupFiveCandidateCentralCharacterTable :
    Matrix AlternatingGroupFiveClassIndex AlternatingGroupFiveClassIndex (Cyclotomic 5) :=
  let φ := alternatingGroupFiveGolden
  let φ' := alternatingGroupFiveGoldenGaloisConjugate
  !![1, 15, 20,      12,      12;
     1, -5,  0, 4 * φ,  4 * φ';
     1, -5,  0, 4 * φ', 4 * φ;
     1,  0,  5,      -3,      -3;
     1,  3, -4,       0,       0]

/-- The entrywise formula for the candidate central-character data. -/
@[simp]
theorem alternatingGroupFiveCandidateCentralCharacterTable_apply
    (i j : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveCandidateCentralCharacterTable i j =
      (let φ := alternatingGroupFiveGolden
       let φ' := alternatingGroupFiveGoldenGaloisConjugate
       !![1, 15, 20,      12,      12;
          1, -5,  0, 4 * φ,  4 * φ';
          1, -5,  0, 4 * φ', 4 * φ;
          1,  0,  5,      -3,      -3;
          1,  3, -4,       0,       0]
        (finCongr numClasses_alternatingGroupFiveClassData i)
        (finCongr numClasses_alternatingGroupFiveClassData j)) := by
  fin_cases i <;> fin_cases j <;> decide

/-- Exact candidate ordinary character data for `A₅`, in the same row and column order as the
candidate central-character data. -/
def alternatingGroupFiveCandidateCharacterTable :
    Matrix AlternatingGroupFiveClassIndex AlternatingGroupFiveClassIndex (Cyclotomic 5) :=
  let φ := alternatingGroupFiveGolden
  let φ' := alternatingGroupFiveGoldenGaloisConjugate
  !![1,  1,  1,  1,  1;
     3, -1,  0,  φ, φ';
     3, -1,  0, φ',  φ;
     4,  0,  1, -1, -1;
     5,  1, -1,  0,  0]

/-- The entrywise formula for the candidate ordinary character data. -/
@[simp]
theorem alternatingGroupFiveCandidateCharacterTable_apply
    (i j : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveCandidateCharacterTable i j =
      (let φ := alternatingGroupFiveGolden
       let φ' := alternatingGroupFiveGoldenGaloisConjugate
       !![1,  1,  1,  1,  1;
          3, -1,  0,  φ, φ';
          3, -1,  0, φ',  φ;
          4,  0,  1, -1, -1;
          5,  1, -1,  0,  0]
        (finCongr numClasses_alternatingGroupFiveClassData i)
        (finCongr numClasses_alternatingGroupFiveClassData j)) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The candidate character degrees attached to the five rows. -/
def alternatingGroupFiveCandidateCharacterDegrees : AlternatingGroupFiveClassIndex → ℕ :=
  ![1, 3, 3, 4, 5]

/-- The entries of the candidate degree vector are `1`, `3`, `3`, `4`, and `5`. -/
@[simp]
theorem alternatingGroupFiveCandidateCharacterDegrees_apply (i : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveCandidateCharacterDegrees i =
      ![1, 3, 3, 4, 5] (finCongr numClasses_alternatingGroupFiveClassData i) := by
  fin_cases i <;> decide

/-- The identity-class entry of each candidate row is its candidate degree. -/
@[simp]
theorem alternatingGroupFiveCandidateCharacterTable_index_one
    (i : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveCandidateCharacterTable i
      (alternatingGroupFiveClassData.index 1) =
        alternatingGroupFiveCandidateCharacterDegrees i := by
  have hrep : alternatingGroupFiveClassData.rep ⟨0, by simp⟩ = 1 := by
    -- `ClassData.rep` computes the zeroth entry of the displayed representative list.
    rfl
  have hindex : alternatingGroupFiveClassData.index 1 = ⟨0, by simp⟩ := by
    rw [← hrep]
    exact alternatingGroupFiveClassData.index_rep _
  rw [hindex]
  fin_cases i <;> decide

/-- The two degree-three rows are genuinely distinct. -/
theorem alternatingGroupFiveCandidateCharacterTable_row_one_ne_row_two :
    alternatingGroupFiveCandidateCharacterTable ⟨1, by simp⟩ ≠
      alternatingGroupFiveCandidateCharacterTable ⟨2, by simp⟩ := by
  decide

/-- Every candidate central-character row is normalized at the identity class. -/
@[simp]
theorem alternatingGroupFiveCandidateCentralCharacterTable_index_one
    (i : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveCandidateCentralCharacterTable i
      (alternatingGroupFiveClassData.index 1) = 1 := by
  have hrep : alternatingGroupFiveClassData.rep ⟨0, by simp⟩ = 1 := by
    -- `ClassData.rep` computes the zeroth entry of the displayed representative list.
    rfl
  have hindex : alternatingGroupFiveClassData.index 1 = ⟨0, by simp⟩ := by
    rw [← hrep]
    exact alternatingGroupFiveClassData.index_rep _
  rw [hindex]
  fin_cases i <;> decide

/-- Every candidate degree is positive and divides the order of `A₅`. -/
theorem alternatingGroupFive_candidateCharacterDegrees_pos_and_dvd
    (i : AlternatingGroupFiveClassIndex) :
    0 < alternatingGroupFiveCandidateCharacterDegrees i ∧
      alternatingGroupFiveCandidateCharacterDegrees i ∣ Nat.card (alternatingGroup (Fin 5)) := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  fin_cases i <;> decide

/-- The sum of the squares of the candidate degrees is the order of `A₅`. -/
theorem alternatingGroupFive_sum_candidateCharacterDegrees_sq :
    ∑ i, alternatingGroupFiveCandidateCharacterDegrees i ^ 2 =
      Nat.card (alternatingGroup (Fin 5)) := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

/-- The candidate central and ordinary data obey the division-free conversion formula. -/
theorem alternatingGroupFive_candidateDegree_mul_candidateCentralCharacterTable
    (i j : AlternatingGroupFiveClassIndex) :
    (alternatingGroupFiveCandidateCharacterDegrees i : Cyclotomic 5) *
        alternatingGroupFiveCandidateCentralCharacterTable i j =
      (alternatingGroupFiveClassData.classFinset j).card *
        alternatingGroupFiveCandidateCharacterTable i j := by
  rw [card_classFinset_alternatingGroupFiveClassData]
  fin_cases i <;> fin_cases j <;> decide

private theorem alternatingGroupFive_candidateCharacterTable_orthogonal_reindex
    (i j : Fin 5) :
    ∑ k, (alternatingGroupFiveClassData.classFinset
        ((finCongr numClasses_alternatingGroupFiveClassData).symm k)).card *
        alternatingGroupFiveCandidateCharacterTable
          ((finCongr numClasses_alternatingGroupFiveClassData).symm i)
          ((finCongr numClasses_alternatingGroupFiveClassData).symm k) *
          star (alternatingGroupFiveCandidateCharacterTable
            ((finCongr numClasses_alternatingGroupFiveClassData).symm j)
            ((finCongr numClasses_alternatingGroupFiveClassData).symm k)) =
      if i = j then (Nat.card (alternatingGroup (Fin 5)) : Cyclotomic 5) else 0 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hgolden : alternatingGroupFiveGolden =
      1 - alternatingGroupFiveGoldenGaloisConjugate := by
    linear_combination alternatingGroupFiveGolden_add_galoisConjugate
  have hpoly : alternatingGroupFiveGoldenGaloisConjugate ^ 2 -
      alternatingGroupFiveGoldenGaloisConjugate - 1 = 0 := by
    calc
      alternatingGroupFiveGoldenGaloisConjugate ^ 2 -
          alternatingGroupFiveGoldenGaloisConjugate - 1 =
          -((1 - alternatingGroupFiveGoldenGaloisConjugate) *
            alternatingGroupFiveGoldenGaloisConjugate + 1) := by ring
      _ = -(alternatingGroupFiveGolden * alternatingGroupFiveGoldenGaloisConjugate + 1) := by
        rw [← hgolden]
      _ = 0 := by rw [alternatingGroupFiveGolden_mul_galoisConjugate]; ring
  have hsq : alternatingGroupFiveGoldenGaloisConjugate ^ 2 =
      alternatingGroupFiveGoldenGaloisConjugate + 1 := by
    linear_combination hpoly
  fin_cases i <;> fin_cases j <;>
    norm_num [Fin.sum_univ_succ, card_classFinset_alternatingGroupFiveClassData,
      alternatingGroupFiveCandidateCharacterTable_apply]
  all_goals
    try rw [hgolden]
    ring_nf
    try rw [hsq]
    try ring

/-- The candidate ordinary-character rows satisfy Hermitian row orthogonality. -/
theorem alternatingGroupFive_candidateCharacterTable_orthogonal
    (i j : AlternatingGroupFiveClassIndex) :
    ∑ k, (alternatingGroupFiveClassData.classFinset k).card *
        alternatingGroupFiveCandidateCharacterTable i k *
          star (alternatingGroupFiveCandidateCharacterTable j k) =
      if i = j then (Nat.card (alternatingGroup (Fin 5)) : Cyclotomic 5) else 0 := by
  let e := finCongr numClasses_alternatingGroupFiveClassData
  calc
    ∑ k, (alternatingGroupFiveClassData.classFinset k).card *
          alternatingGroupFiveCandidateCharacterTable i k *
            star (alternatingGroupFiveCandidateCharacterTable j k) =
        ∑ k : Fin 5, (alternatingGroupFiveClassData.classFinset (e.symm k)).card *
          alternatingGroupFiveCandidateCharacterTable i (e.symm k) *
            star (alternatingGroupFiveCandidateCharacterTable j (e.symm k)) := by
      simpa only [Equiv.symm_apply_apply] using e.sum_comp fun k ↦
        (alternatingGroupFiveClassData.classFinset (e.symm k)).card *
          alternatingGroupFiveCandidateCharacterTable i (e.symm k) *
            star (alternatingGroupFiveCandidateCharacterTable j (e.symm k))
    _ = if i = j then (Nat.card (alternatingGroup (Fin 5)) : Cyclotomic 5) else 0 := by
      simpa only [e, Equiv.symm_apply_apply, e.injective.eq_iff] using
        alternatingGroupFive_candidateCharacterTable_orthogonal_reindex (e i) (e j)

end TauCeti
