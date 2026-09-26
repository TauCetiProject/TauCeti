/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Alternating.Five
public import TauCeti.RingTheory.Cyclotomic.Conjugation

/-!
# Exact cyclotomic character-table data for the alternating group of degree five

This file records exact character-table data for `A₅`. Its conjugacy classes, in the numbering
fixed by `TauCeti.alternatingGroupFiveClassData`, have sizes `1`, `15`, `20`, `12`, and `12`.
If `ζ` is the distinguished primitive fifth root in `TauCeti.Cyclotomic 5`, the two
quadratic values have canonical representatives

```
φ  = -ζ³ - ζ²,
φ' =  ζ³ + ζ² + 1.
```

These are the roots of `X² - X - 1`. The two degree-three rows exchange `φ` and `φ'` on the
two classes of five-cycles. The central-to-ordinary conversion, degree constraints, and Hermitian
row orthogonality are proved in the computable cyclotomic coefficient ring.

## Main definitions

* `TauCeti.alternatingGroupFiveExactCentralCharacterTable`: the exact central-character table.
* `TauCeti.alternatingGroupFiveExactCharacterTable`: the exact ordinary character table.
* `TauCeti.alternatingGroupFiveCharacterDegrees`: the degrees `1`, `3`, `3`, `4`, and `5`.

## Main results

* `TauCeti.alternatingGroupFive_degree_mul_centralCharacterTable`: the central and ordinary tables
  agree under the division-free conversion formula.
* `TauCeti.alternatingGroupFive_characterTable_orthogonal`: the displayed rows satisfy
  Hermitian orthogonality.

## References

The table is the classical `A₅` table; see J.-P. Serre, *Linear Representations of Finite Groups*,
§5.2. The certificate uses the Burnside--Dixon--Schneider framework developed in the surrounding
files.
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
abbrev alternatingGroupFiveGoldenConjugate : Cyclotomic 5 :=
  Cyclotomic.ofCoeffList 5 [1, 1, 0, 1]

/-- The two golden-ratio character values sum to one. -/
theorem alternatingGroupFiveGolden_add_conjugate :
    alternatingGroupFiveGolden + alternatingGroupFiveGoldenConjugate = 1 := by
  decide

/-- The two golden-ratio character values have product negative one. -/
theorem alternatingGroupFiveGolden_mul_conjugate :
    alternatingGroupFiveGolden * alternatingGroupFiveGoldenConjugate = -1 := by
  decide

/-- The sum of the squares of the two golden-ratio character values is three. -/
theorem alternatingGroupFiveGolden_sq_add_conjugate_sq :
    alternatingGroupFiveGolden ^ 2 + alternatingGroupFiveGoldenConjugate ^ 2 = 3 := by
  calc
    alternatingGroupFiveGolden ^ 2 + alternatingGroupFiveGoldenConjugate ^ 2 =
        (alternatingGroupFiveGolden + alternatingGroupFiveGoldenConjugate) ^ 2 -
          2 * (alternatingGroupFiveGolden * alternatingGroupFiveGoldenConjugate) := by ring
    _ = 3 := by
      rw [alternatingGroupFiveGolden_add_conjugate,
        alternatingGroupFiveGolden_mul_conjugate]
      norm_num

/-- The two golden-ratio character values are distinct. -/
theorem alternatingGroupFiveGolden_ne_conjugate :
    alternatingGroupFiveGolden ≠ alternatingGroupFiveGoldenConjugate := by
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
theorem star_alternatingGroupFiveGoldenConjugate :
    star alternatingGroupFiveGoldenConjugate = alternatingGroupFiveGoldenConjugate := by
  apply Cyclotomic.ext
  intro j
  fin_cases j <;> decide

/-- **The exact central-character table of `A₅`.** Columns are the identity, double
transpositions, three-cycles, and the two classes of five-cycles. -/
def alternatingGroupFiveExactCentralCharacterTable :
    Matrix AlternatingGroupFiveClassIndex AlternatingGroupFiveClassIndex (Cyclotomic 5) :=
  let φ := alternatingGroupFiveGolden
  let φ' := alternatingGroupFiveGoldenConjugate
  !![1, 15, 20,      12,      12;
     1, -5,  0, 4 * φ,  4 * φ';
     1, -5,  0, 4 * φ', 4 * φ;
     1,  0,  5,      -3,      -3;
     1,  3, -4,       0,       0]

/-- The entrywise formula for the exact central-character table. -/
@[simp]
theorem alternatingGroupFiveExactCentralCharacterTable_apply
    (i j : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveExactCentralCharacterTable i j =
      (let φ := alternatingGroupFiveGolden
       let φ' := alternatingGroupFiveGoldenConjugate
       !![1, 15, 20,      12,      12;
          1, -5,  0, 4 * φ,  4 * φ';
          1, -5,  0, 4 * φ', 4 * φ;
          1,  0,  5,      -3,      -3;
          1,  3, -4,       0,       0]
        (finCongr numClasses_alternatingGroupFiveClassData i)
        (finCongr numClasses_alternatingGroupFiveClassData j)) := by
  fin_cases i <;> fin_cases j <;> decide

/-- **The exact ordinary character table of `A₅`**, in the same row and column order as the
central-character table. -/
def alternatingGroupFiveExactCharacterTable :
    Matrix AlternatingGroupFiveClassIndex AlternatingGroupFiveClassIndex (Cyclotomic 5) :=
  let φ := alternatingGroupFiveGolden
  let φ' := alternatingGroupFiveGoldenConjugate
  !![1,  1,  1,  1,  1;
     3, -1,  0,  φ, φ';
     3, -1,  0, φ',  φ;
     4,  0,  1, -1, -1;
     5,  1, -1,  0,  0]

/-- The entrywise formula for the exact ordinary character table. -/
@[simp]
theorem alternatingGroupFiveExactCharacterTable_apply
    (i j : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveExactCharacterTable i j =
      (let φ := alternatingGroupFiveGolden
       let φ' := alternatingGroupFiveGoldenConjugate
       !![1,  1,  1,  1,  1;
          3, -1,  0,  φ, φ';
          3, -1,  0, φ',  φ;
          4,  0,  1, -1, -1;
          5,  1, -1,  0,  0]
        (finCongr numClasses_alternatingGroupFiveClassData i)
        (finCongr numClasses_alternatingGroupFiveClassData j)) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The character degrees attached to the five exact rows. -/
def alternatingGroupFiveCharacterDegrees : AlternatingGroupFiveClassIndex → ℕ :=
  ![1, 3, 3, 4, 5]

/-- The entries of the degree vector are `1`, `3`, `3`, `4`, and `5`. -/
@[simp]
theorem alternatingGroupFiveCharacterDegrees_apply (i : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveCharacterDegrees i =
      ![1, 3, 3, 4, 5] (finCongr numClasses_alternatingGroupFiveClassData i) := by
  fin_cases i <;> decide

/-- The two degree-three rows are genuinely distinct. -/
theorem alternatingGroupFiveExactCharacterTable_row_one_ne_row_two :
    alternatingGroupFiveExactCharacterTable ⟨1, by simp⟩ ≠
      alternatingGroupFiveExactCharacterTable ⟨2, by simp⟩ := by
  decide

/-- Every displayed central-character row is normalized at the identity class. -/
theorem alternatingGroupFiveExactCentralCharacterTable_index_one
    (i : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveExactCentralCharacterTable i
      (alternatingGroupFiveClassData.index 1) = 1 := by
  have hrep : alternatingGroupFiveClassData.rep ⟨0, by simp⟩ = 1 := by rfl
  have hindex : alternatingGroupFiveClassData.index 1 = ⟨0, by simp⟩ := by
    rw [← hrep]
    exact alternatingGroupFiveClassData.index_rep _
  rw [hindex]
  fin_cases i <;> decide

/-- Every displayed degree is positive and divides the order of `A₅`. -/
theorem alternatingGroupFive_characterDegrees_pos_and_dvd (i : AlternatingGroupFiveClassIndex) :
    0 < alternatingGroupFiveCharacterDegrees i ∧
      alternatingGroupFiveCharacterDegrees i ∣ Nat.card (alternatingGroup (Fin 5)) := by
  rw [natCard_alternatingGroup_five]
  fin_cases i <;> decide

/-- The sum of the squares of the displayed degrees is the order of `A₅`. -/
theorem alternatingGroupFive_sum_characterDegrees_sq :
    ∑ i, alternatingGroupFiveCharacterDegrees i ^ 2 =
      Nat.card (alternatingGroup (Fin 5)) := by
  rw [natCard_alternatingGroup_five]
  decide

/-- The displayed central and ordinary tables obey the division-free conversion formula. -/
theorem alternatingGroupFive_degree_mul_centralCharacterTable
    (i j : AlternatingGroupFiveClassIndex) :
    (alternatingGroupFiveCharacterDegrees i : Cyclotomic 5) *
        alternatingGroupFiveExactCentralCharacterTable i j =
      (alternatingGroupFiveClassData.classFinset j).card *
        alternatingGroupFiveExactCharacterTable i j := by
  rw [card_classFinset_alternatingGroupFiveClassData]
  fin_cases i <;> fin_cases j <;> decide

private theorem alternatingGroupFive_characterTable_orthogonal_reindex
    (i j : Fin 5) :
    ∑ k, (alternatingGroupFiveClassData.classFinset
        ((finCongr numClasses_alternatingGroupFiveClassData).symm k)).card *
        alternatingGroupFiveExactCharacterTable
          ((finCongr numClasses_alternatingGroupFiveClassData).symm i)
          ((finCongr numClasses_alternatingGroupFiveClassData).symm k) *
          star (alternatingGroupFiveExactCharacterTable
            ((finCongr numClasses_alternatingGroupFiveClassData).symm j)
            ((finCongr numClasses_alternatingGroupFiveClassData).symm k)) =
      if i = j then (Nat.card (alternatingGroup (Fin 5)) : Cyclotomic 5) else 0 := by
  rw [natCard_alternatingGroup_five]
  simp only [alternatingGroupFiveExactCharacterTable_apply]
  have hgolden : alternatingGroupFiveGolden =
      1 - alternatingGroupFiveGoldenConjugate := by
    linear_combination alternatingGroupFiveGolden_add_conjugate
  have hpoly : alternatingGroupFiveGoldenConjugate ^ 2 -
      alternatingGroupFiveGoldenConjugate - 1 = 0 := by
    calc
      alternatingGroupFiveGoldenConjugate ^ 2 - alternatingGroupFiveGoldenConjugate - 1 =
          -((1 - alternatingGroupFiveGoldenConjugate) *
            alternatingGroupFiveGoldenConjugate + 1) := by ring
      _ = -(alternatingGroupFiveGolden * alternatingGroupFiveGoldenConjugate + 1) := by
        rw [← hgolden]
      _ = 0 := by rw [alternatingGroupFiveGolden_mul_conjugate]; ring
  have hsq : alternatingGroupFiveGoldenConjugate ^ 2 =
      alternatingGroupFiveGoldenConjugate + 1 := by
    linear_combination hpoly
  fin_cases i <;> fin_cases j <;>
    simp only [finCongr_symm, finCongr_apply,
      card_classFinset_alternatingGroupFiveClassData, Finset.sum_fin_eq_sum_range,
      Finset.sum_range_succ, Nat.succ_eq_add_one, Nat.reduceAdd,
      Fin.cast_cast, Fin.cast_eq_self, Fin.zero_eta, Fin.isValue, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_fin_one, Matrix.cons_val_zero, Fin.mk_one,
      Matrix.cons_val_one, zero_ne_one, one_ne_zero, Fin.reduceFinMk, Matrix.cons_val,
      Fin.reduceEq, ↓reduceIte, Nat.cast_ofNat]
  all_goals
    simp only [Finset.range_zero, Finset.sum_empty, Nat.ofNat_pos, ↓reduceDIte,
      Nat.cast_one, one_mul, mul_one, zero_add, add_zero, Nat.one_lt_ofNat, Nat.reduceLT,
      Nat.lt_add_one, star_ofNat, star_one, star_zero, star_neg, mul_neg, neg_mul, neg_neg,
      neg_zero, mul_zero, zero_mul, star_alternatingGroupFiveGolden,
      star_alternatingGroupFiveGoldenConjugate]
    try rw [hgolden]
    ring_nf
    try rw [hsq]
    try ring

/-- The displayed exact ordinary-character rows satisfy Hermitian row orthogonality. -/
theorem alternatingGroupFive_characterTable_orthogonal
    (i j : AlternatingGroupFiveClassIndex) :
    ∑ k, (alternatingGroupFiveClassData.classFinset k).card *
        alternatingGroupFiveExactCharacterTable i k *
          star (alternatingGroupFiveExactCharacterTable j k) =
      if i = j then (Nat.card (alternatingGroup (Fin 5)) : Cyclotomic 5) else 0 := by
  let e := finCongr numClasses_alternatingGroupFiveClassData
  calc
    ∑ k, (alternatingGroupFiveClassData.classFinset k).card *
          alternatingGroupFiveExactCharacterTable i k *
            star (alternatingGroupFiveExactCharacterTable j k) =
        ∑ k : Fin 5, (alternatingGroupFiveClassData.classFinset (e.symm k)).card *
          alternatingGroupFiveExactCharacterTable i (e.symm k) *
            star (alternatingGroupFiveExactCharacterTable j (e.symm k)) := by
      simpa only [Equiv.symm_apply_apply] using e.sum_comp fun k ↦
        (alternatingGroupFiveClassData.classFinset (e.symm k)).card *
          alternatingGroupFiveExactCharacterTable i (e.symm k) *
            star (alternatingGroupFiveExactCharacterTable j (e.symm k))
    _ = if i = j then (Nat.card (alternatingGroup (Fin 5)) : Cyclotomic 5) else 0 := by
      simpa only [e, Equiv.symm_apply_apply, e.injective.eq_iff] using
        alternatingGroupFive_characterTable_orthogonal_reindex (e i) (e j)

end TauCeti
