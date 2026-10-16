/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Alternating.Five
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Checker
public import TauCeti.RingTheory.Cyclotomic.Power

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
two classes of five-cycles. The central-character rows satisfy the class-algebra eigenrow equations,
so together with the central-to-ordinary conversion, degree constraints, and Hermitian row
orthogonality they certify the displayed table as the character table of `A₅` up to row
permutation.

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
* `TauCeti.isCyclotomicCharacterTableSpec_alternatingGroupFive`: the exact tables pass the
  cyclotomic character-table certificate.
* `TauCeti.isCharacterTableSpec_alternatingGroupFive`: the distinguished complex embedding of the
  displayed ordinary table is the character table of `A₅` up to row permutation.

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

/-- The cyclotomic Galois automorphism `ζ ↦ ζ²` of `TauCeti.Cyclotomic 5`. -/
noncomputable def alternatingGroupFiveGaloisEquiv : Cyclotomic 5 ≃+* Cyclotomic 5 := by
  let σ2 : Cyclotomic 5 →+* Cyclotomic 5 :=
    Cyclotomic.powRingHom (e := 5) (n := 2) (by decide)
  let σ3 : Cyclotomic 5 →+* Cyclotomic 5 :=
    Cyclotomic.powRingHom (e := 5) (n := 3) (by decide)
  have hleft : σ3.comp σ2 = RingHom.id (Cyclotomic 5) := by
    ext1
    simp only [RingHom.comp_apply, σ2, σ3, Cyclotomic.powRingHom_zeta, map_pow,
      RingHom.id_apply]
    decide
  have hright : σ2.comp σ3 = RingHom.id (Cyclotomic 5) := by
    ext1
    simp only [RingHom.comp_apply, σ2, σ3, Cyclotomic.powRingHom_zeta, map_pow,
      RingHom.id_apply]
    decide
  exact
    { toFun := σ2
      invFun := σ3
      left_inv := fun x ↦ by rw [← RingHom.comp_apply, hleft, RingHom.id_apply]
      right_inv := fun x ↦ by rw [← RingHom.comp_apply, hright, RingHom.id_apply]
      map_mul' := σ2.map_mul
      map_add' := σ2.map_add }

private theorem alternatingGroupFiveGaloisEquiv_apply (x : Cyclotomic 5) :
    alternatingGroupFiveGaloisEquiv x =
      Cyclotomic.powRingHom (e := 5) (n := 2) (by decide) x := by
  rfl

/-- The Galois automorphism sends the distinguished fifth root of unity to its square. -/
@[simp]
theorem alternatingGroupFiveGaloisEquiv_zeta :
    alternatingGroupFiveGaloisEquiv (Cyclotomic.zeta 5) = Cyclotomic.zeta 5 ^ 2 := by
  rw [alternatingGroupFiveGaloisEquiv_apply, Cyclotomic.powRingHom_zeta]

/-- The Galois automorphism `ζ ↦ ζ²` exchanges the two golden-ratio values. -/
@[simp]
theorem alternatingGroupFiveGaloisEquiv_golden :
    alternatingGroupFiveGaloisEquiv alternatingGroupFiveGolden =
      alternatingGroupFiveGoldenGaloisConjugate := by
  rw [alternatingGroupFiveGaloisEquiv_apply, Cyclotomic.powRingHom_apply,
    ← Cyclotomic.evalRingHom_eq_evalCoeffs _ _
      (Cyclotomic.eval₂_cyclotomic_zeta_pow (by decide)), Cyclotomic.evalRingHom_ofCoeffList]
  norm_num [TauCeti.Polynomial.ofCoeffList_cons]
  decide

/-- The Galois automorphism `ζ ↦ ζ²` sends the conjugate golden-ratio value back to the
positive one. -/
@[simp]
theorem alternatingGroupFiveGaloisEquiv_galoisConjugate :
    alternatingGroupFiveGaloisEquiv alternatingGroupFiveGoldenGaloisConjugate =
      alternatingGroupFiveGolden := by
  rw [alternatingGroupFiveGaloisEquiv_apply, Cyclotomic.powRingHom_apply,
    ← Cyclotomic.evalRingHom_eq_evalCoeffs _ _
      (Cyclotomic.eval₂_cyclotomic_zeta_pow (by decide)), Cyclotomic.evalRingHom_ofCoeffList]
  norm_num [TauCeti.Polynomial.ofCoeffList_cons]
  decide

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

/-- The positive golden-ratio character value is fixed by exact complex conjugation. -/
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

/-- The Galois automorphism `ζ ↦ ζ²` exchanges the two degree-three candidate rows. -/
@[simp]
theorem alternatingGroupFiveGaloisEquiv_candidateCharacterTable_row_one
    (j : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveGaloisEquiv
        (alternatingGroupFiveCandidateCharacterTable ⟨1, by simp⟩ j) =
      alternatingGroupFiveCandidateCharacterTable ⟨2, by simp⟩ j := by
  have hjlt : j.val < 5 := by
    simpa only [numClasses_alternatingGroupFiveClassData] using j.isLt
  have hj : finCongr numClasses_alternatingGroupFiveClassData j = ⟨j.val, hjlt⟩ := Fin.ext rfl
  rw [alternatingGroupFiveCandidateCharacterTable_apply,
    alternatingGroupFiveCandidateCharacterTable_apply, hj]
  fin_cases j <;> norm_num; simp only [map_ofNat]

/-- The Galois automorphism `ζ ↦ ζ²` exchanges the two degree-three candidate rows in the
opposite direction as well. -/
@[simp]
theorem alternatingGroupFiveGaloisEquiv_candidateCharacterTable_row_two
    (j : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveGaloisEquiv
        (alternatingGroupFiveCandidateCharacterTable ⟨2, by simp⟩ j) =
      alternatingGroupFiveCandidateCharacterTable ⟨1, by simp⟩ j := by
  have hjlt : j.val < 5 := by
    simpa only [numClasses_alternatingGroupFiveClassData] using j.isLt
  have hj : finCongr numClasses_alternatingGroupFiveClassData j = ⟨j.val, hjlt⟩ := Fin.ext rfl
  rw [alternatingGroupFiveCandidateCharacterTable_apply,
    alternatingGroupFiveCandidateCharacterTable_apply, hj]
  fin_cases j <;> norm_num; simp only [map_ofNat]

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

/-- Every candidate central-character row satisfies the class-algebra eigenrow equations. -/
theorem isModularEigenrow_alternatingGroupFiveCandidateCentralCharacterTable
    (i : AlternatingGroupFiveClassIndex) :
    alternatingGroupFiveClassData.IsModularEigenrow
      (alternatingGroupFiveCandidateCentralCharacterTable i) := by
  rw [alternatingGroupFiveClassData.isModularEigenrow_iff]
  simp_rw [← alternatingGroupFiveClassData.getD_structureConstantTable]
  rw [structureConstantTable_alternatingGroupFiveClassData]
  fin_cases i <;> decide +kernel

/-- **The displayed exact `A₅` tables pass the cyclotomic character-table certificate.** -/
theorem isCyclotomicCharacterTableSpec_alternatingGroupFive :
    alternatingGroupFiveClassData.IsCyclotomicCharacterTableSpec 5
      alternatingGroupFiveCandidateCentralCharacterTable
      alternatingGroupFiveCandidateCharacterTable
      alternatingGroupFiveCandidateCharacterDegrees where
  central_one := alternatingGroupFiveCandidateCentralCharacterTable_index_one
  central_eigen := isModularEigenrow_alternatingGroupFiveCandidateCentralCharacterTable
  degree_pos i := (alternatingGroupFive_candidateCharacterDegrees_pos_and_dvd i).1
  degree_dvd i := by
    simpa only [Nat.card_eq_fintype_card] using
      (alternatingGroupFive_candidateCharacterDegrees_pos_and_dvd i).2
  sum_degree_sq := by
    simpa only [Nat.card_eq_fintype_card] using
      alternatingGroupFive_sum_candidateCharacterDegrees_sq
  degree_mul_central := alternatingGroupFive_candidateDegree_mul_candidateCentralCharacterTable
  row_orthogonal i j := by
    simpa only [Nat.card_eq_fintype_card] using
      alternatingGroupFive_candidateCharacterTable_orthogonal i j

/-- The executable exact cyclotomic checker accepts the displayed `A₅` tables. -/
theorem cyclotomicCharacterTableChecker_alternatingGroupFive :
    alternatingGroupFiveClassData.cyclotomicCharacterTableChecker 5
      alternatingGroupFiveCandidateCentralCharacterTable
      alternatingGroupFiveCandidateCharacterTable
      alternatingGroupFiveCandidateCharacterDegrees = true :=
  (alternatingGroupFiveClassData.cyclotomicCharacterTableChecker_eq_true_iff 5 _ _ _).2
    isCyclotomicCharacterTableSpec_alternatingGroupFive

/-- **The distinguished complex embedding of the displayed exact table is the character table of
`A₅` up to row permutation.** -/
theorem isCharacterTableSpec_alternatingGroupFive :
    IsCharacterTableSpec (alternatingGroup (Fin 5))
      (alternatingGroupFiveClassData.complexTableOfCyclotomic 5
        alternatingGroupFiveCandidateCharacterTable) :=
  isCyclotomicCharacterTableSpec_alternatingGroupFive.isCharacterTableSpec

end TauCeti
