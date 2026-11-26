/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.SpecialLinearTwoThree
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Solver

/-!
# The cyclotomic Dixon computation for `SL(2, 3)`

This file certifies the exact character table of `SL(2, 3) = SpecialLinearGroup (Fin 2) (ZMod 3)`.
Its seven conjugacy classes, numbered by `TauCeti.specialLinearTwoThreeClassData`, have
representatives `1`, `z = -1`, `s`, `t`, `t⁻¹`, `z t` and `z t⁻¹` and sizes `1`, `1`, `6`, `4`,
`4`, `4` and `4`. If `ζ` is the distinguished primitive twelfth root in `TauCeti.Cyclotomic 12` and
`ω = ζ⁴`, the ordinary table is

```
1   1   1    1     1     1    1
1   1   1    ω    ω²     ω   ω²
1   1   1   ω²     ω    ω²    ω
3   3  -1    0     0     0    0
2  -2   0   -1    -1     1    1
2  -2   0   -ω   -ω²     ω   ω²
2  -2   0  -ω²    -ω    ω²    ω
```

The first four rows are inflated from `SL(2, 3) ⧸ {±1} ≅ A₄`; the last three are the faithful
characters of degree two, and the last two are the products of the fifth with the two nonreal
linear characters. All values lie in `ℤ[ω]`, but the exponent of `SL(2, 3)` is twelve, so the
computation runs in `Cyclotomic 12`.

The Dixon prime is `13`, the least prime congruent to `1` modulo `12` above `2⌊√24⌋ = 8`, with the
primitive twelfth root `2`. Its balanced residue window `[-6, 6]` contains every coefficient of the
central-character table, whose entries are the class sizes times the corresponding ordinary
character values divided by the character degrees. Reduction at the root modulo `13` sends the
seven rows to precisely the output of the executable modular eigenrow search, and the exact
checker verifies, inside the computable coefficient-vector ring `Cyclotomic 12`, the
central-character equations, the central-to-ordinary conversion, the degree-square identity and
Hermitian row orthogonality.

## Main definitions

* `TauCeti.specialLinearTwoThreeDixonPrimeData`: the prime `13` with primitive twelfth root `2`.
* `TauCeti.specialLinearTwoThreeExactCentralCharacterTable`: the exact central-character table.
* `TauCeti.specialLinearTwoThreeExactCharacterTable`: the exact ordinary character table.
* `TauCeti.specialLinearTwoThreeCharacterDegrees`: the degrees `1`, `1`, `1`, `3`, `2`, `2`
  and `2`.
* `TauCeti.specialLinearTwoThreeComplexCharacterTable`: the ordinary table embedded in `ℂ`.
* `TauCeti.specialLinearTwoThreeCharacter`: row `i` of the exact table, embedded in `ℂ` and read
  as a function on `SL(2, 3)` through the class numbering.

## Main results

* `TauCeti.complexEmbedding_specialLinearTwoThreeOmega`: the embedded cube root of unity is
  `ω = exp (2πi/3)`.
* `TauCeti.specialLinearTwoThree_centralCharacterSearch`: the modular search returns exactly the
  reductions of the seven displayed central-character rows.
* `TauCeti.specialLinearTwoThreeExactCharacterTable_lift_conjugateResidues`: the structured lift
  recovers every exact ordinary-table entry from its conjugate residues.
* `TauCeti.isSome_dixonCyclotomicCharacterTable_specialLinearTwoThree`: the assembled exact solver
  succeeds on the certified data.
* `TauCeti.isSome_characterTableDixon_specialLinearTwoThree`: the assembled algorithm, searching
  for its own prime with budget `2`, returns a character table.
* `TauCeti.isCyclotomicCharacterTableSpec_specialLinearTwoThree`: the exact tables pass the
  executable cyclotomic certificate.
* `TauCeti.isCharacterTableSpec_specialLinearTwoThree`: the distinguished complex embedding of the
  displayed ordinary table is a character table of `SL(2, 3)`.
* `TauCeti.irreducibleCharacters_specialLinearTwoThree`: the irreducible complex characters of
  `SL(2, 3)` are the seven embedded rows.
* `TauCeti.specialLinearTwoThreeCharacter_one`: the value of an embedded row at `1` is its degree.

## References

The formal declaration order and proof plan follow
`TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.AlternatingFour`, and the
field-by-field assembly of the certificate follows
`TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.AlternatingFive.Basic`. The candidate
is the classical `SL(2, 3)` table, the case `q = 3` of the character table of `SL₂(𝔽_q)` in
W. Fulton and J. Harris, *Representation Theory: A First Course*, §5.2; its first four rows are
the `A₄` table of J.-P. Serre, *Linear Representations of Finite Groups*, §5.7.

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, Journal of Symbolic Computation 9
  (1990), 601--606.
-/

public section

namespace TauCeti

open Matrix

local instance fact_prime_thirteen_specialLinearTwoThree : Fact (Nat.Prime 13) := ⟨by decide⟩

private theorem sqrt_twentyFour : Nat.sqrt 24 = 4 := by
  exact ((Nat.eq_sqrt).2 (by norm_num)).symm

/-- **`13` is a good Dixon prime for `SL(2, 3)`**: it does not divide `24`, the exponent `12`
divides `13 - 1`, and `2⌊√24⌋ = 8 < 13`. -/
theorem isGoodDixonPrime_specialLinearGroup_two_three_thirteen :
    IsGoodDixonPrime (SpecialLinearGroup (Fin 2) (ZMod 3)) 13 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [natCard_sl2_zmod_three]
    decide
  · rw [exponent_specialLinearGroup_two_three]
  · rw [natCard_sl2_zmod_three, sqrt_twentyFour]
    norm_num

/-- Dixon prime data for `SL(2, 3)`: the prime `13`, with `2` as a primitive twelfth root of
unity. -/
@[expose] def specialLinearTwoThreeDixonPrimeData :
    DixonPrimeData (SpecialLinearGroup (Fin 2) (ZMod 3)) where
  p := 13
  root := 2
  isGoodDixonPrime := isGoodDixonPrime_specialLinearGroup_two_three_thirteen
  isPrimitiveRoot_root := by
    simpa only [exponent_specialLinearGroup_two_three] using
      (IsPrimitiveRoot.mk_of_lt (2 : ZMod 13) (by norm_num) (by decide)
        fun l hl0 hl12 ↦ by interval_cases l <;> decide)

/-- The prime carried by `TauCeti.specialLinearTwoThreeDixonPrimeData` is `13`. -/
@[simp]
theorem specialLinearTwoThreeDixonPrimeData_p : specialLinearTwoThreeDixonPrimeData.p = 13 :=
  rfl

/-- The primitive twelfth root carried by `TauCeti.specialLinearTwoThreeDixonPrimeData` is `2`. -/
@[simp]
theorem specialLinearTwoThreeDixonPrimeData_root :
    specialLinearTwoThreeDixonPrimeData.root = 2 := rfl

/-- The numbered conjugacy classes of `SL(2, 3)`. -/
abbrev SpecialLinearTwoThreeClassIndex := Fin specialLinearTwoThreeClassData.numClasses

/-- The primitive cube root `ζ⁴` in the twelfth cyclotomic ring. -/
abbrev specialLinearTwoThreeOmega : Cyclotomic 12 := Cyclotomic.zeta 12 ^ 4

/-- **The distinguished cube root of unity is `exp (2πi/3)`**: the embedding
`TauCeti.Cyclotomic.complexEmbedding` sends `TauCeti.specialLinearTwoThreeOmega = ζ₁₂⁴` to
`exp (2πi/12) ^ 4 = exp (2πi/3)`. -/
theorem complexEmbedding_specialLinearTwoThreeOmega :
    Cyclotomic.complexEmbedding specialLinearTwoThreeOmega =
      Complex.exp (2 * Real.pi * Complex.I / 3) := by
  rw [specialLinearTwoThreeOmega, map_pow, Cyclotomic.complexEmbedding_zeta,
    Cyclotomic.complexRoot_def, ← Complex.exp_natCast_mul]
  congr 1
  push_cast
  ring

/-- **The exact central-character table of `SL(2, 3)`.**  Columns are the classes of `1`, `z`,
`s`, `t`, `t⁻¹`, `z t` and `z t⁻¹`. -/
def specialLinearTwoThreeExactCentralCharacterTable :
    Matrix SpecialLinearTwoThreeClassIndex SpecialLinearTwoThreeClassIndex (Cyclotomic 12) :=
  let ω := specialLinearTwoThreeOmega
  !![1,  1,  6,         4,         4,         4,         4;
     1,  1,  6,     4 * ω, 4 * ω ^ 2,     4 * ω, 4 * ω ^ 2;
     1,  1,  6, 4 * ω ^ 2,     4 * ω, 4 * ω ^ 2,     4 * ω;
     1,  1, -2,         0,         0,         0,         0;
     1, -1,  0,        -2,        -2,         2,         2;
     1, -1,  0,    -2 * ω, -2 * ω ^ 2,    2 * ω, 2 * ω ^ 2;
     1, -1,  0, -2 * ω ^ 2,    -2 * ω, 2 * ω ^ 2,    2 * ω]

/-- The entrywise formula for the exact central-character table. -/
@[simp]
theorem specialLinearTwoThreeExactCentralCharacterTable_apply
    (i j : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeExactCentralCharacterTable i j =
      (let ω := specialLinearTwoThreeOmega
       !![1,  1,  6,         4,         4,         4,         4;
          1,  1,  6,     4 * ω, 4 * ω ^ 2,     4 * ω, 4 * ω ^ 2;
          1,  1,  6, 4 * ω ^ 2,     4 * ω, 4 * ω ^ 2,     4 * ω;
          1,  1, -2,         0,         0,         0,         0;
          1, -1,  0,        -2,        -2,         2,         2;
          1, -1,  0,    -2 * ω, -2 * ω ^ 2,    2 * ω, 2 * ω ^ 2;
          1, -1,  0, -2 * ω ^ 2,    -2 * ω, 2 * ω ^ 2,    2 * ω] i j) := by
  rfl

/-- The exact ordinary character table of `SL(2, 3)`, in the same row and column order as the
central-character table. -/
def specialLinearTwoThreeExactCharacterTable :
    Matrix SpecialLinearTwoThreeClassIndex SpecialLinearTwoThreeClassIndex (Cyclotomic 12) :=
  let ω := specialLinearTwoThreeOmega
  !![1,  1,  1,      1,      1,     1,     1;
     1,  1,  1,      ω,  ω ^ 2,     ω, ω ^ 2;
     1,  1,  1,  ω ^ 2,      ω, ω ^ 2,     ω;
     3,  3, -1,      0,      0,     0,     0;
     2, -2,  0,     -1,     -1,     1,     1;
     2, -2,  0,     -ω, -ω ^ 2,     ω, ω ^ 2;
     2, -2,  0, -ω ^ 2,     -ω, ω ^ 2,     ω]

/-- The entrywise formula for the exact ordinary character table. -/
@[simp]
theorem specialLinearTwoThreeExactCharacterTable_apply
    (i j : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeExactCharacterTable i j =
      (let ω := specialLinearTwoThreeOmega
       !![1,  1,  1,      1,      1,     1,     1;
          1,  1,  1,      ω,  ω ^ 2,     ω, ω ^ 2;
          1,  1,  1,  ω ^ 2,      ω, ω ^ 2,     ω;
          3,  3, -1,      0,      0,     0,     0;
          2, -2,  0,     -1,     -1,     1,     1;
          2, -2,  0,     -ω, -ω ^ 2,     ω, ω ^ 2;
          2, -2,  0, -ω ^ 2,     -ω, ω ^ 2,     ω] i j) := by
  rfl

/-- The character degrees attached to the seven exact rows. -/
def specialLinearTwoThreeCharacterDegrees : SpecialLinearTwoThreeClassIndex → ℕ :=
  ![1, 1, 1, 3, 2, 2, 2]

/-- The entries of the degree vector are `1`, `1`, `1`, `3`, `2`, `2` and `2`. -/
@[simp]
theorem specialLinearTwoThreeCharacterDegrees_apply (i : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeCharacterDegrees i = ![1, 1, 1, 3, 2, 2, 2] i := by
  rfl

/-- Exact conjugation exchanges the two nonreal linear rows of the `SL(2, 3)` table. -/
theorem star_specialLinearTwoThreeExactCharacterTable_row_one
    (j : SpecialLinearTwoThreeClassIndex) :
    star (specialLinearTwoThreeExactCharacterTable ⟨1, by simp⟩ j) =
      specialLinearTwoThreeExactCharacterTable ⟨2, by simp⟩ j := by
  revert j
  decide +kernel

/-- Exact conjugation exchanges the two nonreal rows of degree two of the `SL(2, 3)` table. -/
theorem star_specialLinearTwoThreeExactCharacterTable_row_five
    (j : SpecialLinearTwoThreeClassIndex) :
    star (specialLinearTwoThreeExactCharacterTable ⟨5, by simp⟩ j) =
      specialLinearTwoThreeExactCharacterTable ⟨6, by simp⟩ j := by
  revert j
  decide +kernel

/-- The last two rows of degree two are the products of the rational row of degree two with the
two nonreal linear rows. -/
theorem specialLinearTwoThreeExactCharacterTable_row_four_mul
    (j : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeExactCharacterTable ⟨4, by simp⟩ j *
        specialLinearTwoThreeExactCharacterTable ⟨1, by simp⟩ j =
      specialLinearTwoThreeExactCharacterTable ⟨5, by simp⟩ j ∧
    specialLinearTwoThreeExactCharacterTable ⟨4, by simp⟩ j *
        specialLinearTwoThreeExactCharacterTable ⟨2, by simp⟩ j =
      specialLinearTwoThreeExactCharacterTable ⟨6, by simp⟩ j := by
  revert j
  decide +kernel

/-- The identity is the representative of the class numbered `0`. -/
private theorem specialLinearTwoThreeClassData_index_one :
    specialLinearTwoThreeClassData.index 1 = ⟨0, by simp⟩ := by
  have hrep : specialLinearTwoThreeClassData.rep ⟨0, by simp⟩ = 1 := by
    rw [rep_specialLinearTwoThreeClassData]
    rfl
  rw [← hrep]
  exact specialLinearTwoThreeClassData.index_rep _

private theorem fintypeCard_specialLinearGroup_two_three :
    Fintype.card (SpecialLinearGroup (Fin 2) (ZMod 3)) = 24 := by
  rw [← Nat.card_eq_fintype_card, natCard_sl2_zmod_three]

/-- Every displayed central-character row is normalized at the identity class. -/
theorem specialLinearTwoThreeExactCentralCharacterTable_index_one
    (i : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeExactCentralCharacterTable i
      (specialLinearTwoThreeClassData.index 1) = 1 := by
  rw [specialLinearTwoThreeClassData_index_one]
  revert i
  decide +kernel

/-- Every displayed exact central-character row satisfies the class-algebra eigenrow
equations. -/
theorem isModularEigenrow_specialLinearTwoThreeExactCentralCharacterTable
    (i : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeClassData.IsModularEigenrow
      (specialLinearTwoThreeExactCentralCharacterTable i) := by
  rw [specialLinearTwoThreeClassData.isModularEigenrow_iff]
  simp_rw [← specialLinearTwoThreeClassData.getD_structureConstantTable]
  rw [structureConstantTable_specialLinearTwoThreeClassData]
  revert i
  decide +kernel

/-- **The displayed exact `SL(2, 3)` tables pass the cyclotomic character-table certificate.** -/
theorem isCyclotomicCharacterTableSpec_specialLinearTwoThree :
    specialLinearTwoThreeClassData.IsCyclotomicCharacterTableSpec 12
      specialLinearTwoThreeExactCentralCharacterTable specialLinearTwoThreeExactCharacterTable
      specialLinearTwoThreeCharacterDegrees where
  central_one := specialLinearTwoThreeExactCentralCharacterTable_index_one
  central_eigen := isModularEigenrow_specialLinearTwoThreeExactCentralCharacterTable
  degree_pos := by decide
  degree_dvd := by
    rw [fintypeCard_specialLinearGroup_two_three]
    decide
  sum_degree_sq := by
    rw [fintypeCard_specialLinearGroup_two_three]
    decide
  degree_mul_central := by
    simp only [card_classFinset_specialLinearTwoThreeClassData]
    decide +kernel
  row_orthogonal := by
    simp only [card_classFinset_specialLinearTwoThreeClassData,
      fintypeCard_specialLinearGroup_two_three]
    decide +kernel

/-- The executable exact cyclotomic checker accepts the displayed `SL(2, 3)` tables. -/
theorem cyclotomicCharacterTableChecker_specialLinearTwoThree :
    specialLinearTwoThreeClassData.cyclotomicCharacterTableChecker 12
      specialLinearTwoThreeExactCentralCharacterTable specialLinearTwoThreeExactCharacterTable
      specialLinearTwoThreeCharacterDegrees = true :=
  (specialLinearTwoThreeClassData.cyclotomicCharacterTableChecker_eq_true_iff 12 _ _ _).2
    isCyclotomicCharacterTableSpec_specialLinearTwoThree

/-- The displayed exact central-character rows reduced at the primitive twelfth root `2` modulo
`13`. -/
def specialLinearTwoThreeModularCentralRows :
    Finset (SpecialLinearTwoThreeClassIndex → ZMod 13) :=
  specialLinearTwoThreeClassData.rowsOfMap
    (Cyclotomic.reduce 13 specialLinearTwoThreeDixonPrimeData.root)
    specialLinearTwoThreeExactCentralCharacterTable

/-- A modular row is displayed exactly when it is the reduction of a row of the exact
central-character table. -/
@[simp]
theorem mem_specialLinearTwoThreeModularCentralRows_iff
    {a : SpecialLinearTwoThreeClassIndex → ZMod 13} :
    a ∈ specialLinearTwoThreeModularCentralRows ↔
      ∃ i, (fun j ↦ Cyclotomic.reduce 13 specialLinearTwoThreeDixonPrimeData.root
        (specialLinearTwoThreeExactCentralCharacterTable i j)) = a :=
  specialLinearTwoThreeClassData.mem_rowsOfMap_iff _ _

private theorem isPrimitiveRoot_specialLinearTwoThreeDixonPrimeData_root :
    IsPrimitiveRoot specialLinearTwoThreeDixonPrimeData.root 12 := by
  simpa only [exponent_specialLinearGroup_two_three] using
    specialLinearTwoThreeDixonPrimeData.isPrimitiveRoot_root

/-- Reduction at the chosen root preserves every exact central-character eigenrow equation. -/
theorem isModularEigenrow_specialLinearTwoThreeExactCentralCharacterTable_zmod
    (i : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeClassData.IsModularEigenrow fun j ↦
      Cyclotomic.reduce 13 specialLinearTwoThreeDixonPrimeData.root
        (specialLinearTwoThreeExactCentralCharacterTable i j) := by
  have hroot := isPrimitiveRoot_specialLinearTwoThreeDixonPrimeData_root
  have hmap := (isModularEigenrow_specialLinearTwoThreeExactCentralCharacterTable i).map
    (Cyclotomic.reduceRingHom 13 specialLinearTwoThreeDixonPrimeData.root hroot)
  rw [specialLinearTwoThreeClassData.isModularEigenrow_iff] at hmap ⊢
  intro a b
  simpa only [← Cyclotomic.reduceRingHom_apply 13 specialLinearTwoThreeDixonPrimeData.root hroot]
    using hmap a b

/-- The seven displayed modular central-character rows are pairwise distinct. -/
@[simp]
theorem card_specialLinearTwoThreeModularCentralRows :
    specialLinearTwoThreeModularCentralRows.card = 7 := by
  decide +kernel

/-- **The executable modular central-character search for `SL(2, 3)` returns precisely the seven
reductions of the displayed exact central-character rows.** -/
theorem specialLinearTwoThree_centralCharacterSearch :
    specialLinearTwoThreeClassData.centralCharacterSearch (F := ZMod 13) =
      specialLinearTwoThreeModularCentralRows := by
  rw [specialLinearTwoThreeModularCentralRows]
  apply specialLinearTwoThreeClassData.centralCharacterSearch_eq_rowsOfMap
    (Cyclotomic.reduce 13 specialLinearTwoThreeDixonPrimeData.root)
    specialLinearTwoThreeExactCentralCharacterTable
  · intro i
    have hroot := isPrimitiveRoot_specialLinearTwoThreeDixonPrimeData_root
    rw [specialLinearTwoThreeExactCentralCharacterTable_index_one]
    simpa only [← Cyclotomic.reduceRingHom_apply 13 specialLinearTwoThreeDixonPrimeData.root
      hroot] using
      map_one (Cyclotomic.reduceRingHom 13 specialLinearTwoThreeDixonPrimeData.root hroot)
  · exact isModularEigenrow_specialLinearTwoThreeExactCentralCharacterTable_zmod
  · simpa only [specialLinearTwoThreeModularCentralRows,
      numClasses_specialLinearTwoThreeClassData] using
      card_specialLinearTwoThreeModularCentralRows

/-- Every coordinate of every displayed ordinary-table entry satisfies Dixon's coefficient
bound. -/
theorem specialLinearTwoThreeExactCharacterTable_natAbs_coeff_le_sqrt
    (i j : SpecialLinearTwoThreeClassIndex) (k : Fin (12 : ℕ).totient) :
    ((specialLinearTwoThreeExactCharacterTable i j).coeff k).natAbs ≤
      Nat.sqrt (Nat.card (SpecialLinearGroup (Fin 2) (ZMod 3))) := by
  rw [natCard_sl2_zmod_three, sqrt_twentyFour]
  revert i j k
  decide +kernel

/-- **The structured cyclotomic lift recovers every exact ordinary-table entry from its residues
at the conjugate primitive twelfth roots modulo `13`.** -/
theorem specialLinearTwoThreeExactCharacterTable_lift_conjugateResidues
    (i j : SpecialLinearTwoThreeClassIndex) :
    Cyclotomic.lift 12 specialLinearTwoThreeDixonPrimeData.root
        (Cyclotomic.conjugateResidues specialLinearTwoThreeDixonPrimeData.root
          (specialLinearTwoThreeExactCharacterTable i j)) =
      specialLinearTwoThreeExactCharacterTable i j := by
  have hLift : ∀ {x : Cyclotomic (Monoid.exponent (SpecialLinearGroup (Fin 2) (ZMod 3)))},
      (∀ k : Fin (Monoid.exponent (SpecialLinearGroup (Fin 2) (ZMod 3))).totient,
        (x.coeff k).natAbs ≤ Nat.sqrt (Nat.card (SpecialLinearGroup (Fin 2) (ZMod 3)))) →
      Cyclotomic.lift (Monoid.exponent (SpecialLinearGroup (Fin 2) (ZMod 3)))
        specialLinearTwoThreeDixonPrimeData.root
        (Cyclotomic.conjugateResidues specialLinearTwoThreeDixonPrimeData.root x) = x :=
    fun {_} ↦ specialLinearTwoThreeDixonPrimeData.lift_conjugateResidues
  rw [exponent_specialLinearGroup_two_three] at hLift
  exact hLift (specialLinearTwoThreeExactCharacterTable_natAbs_coeff_le_sqrt i j)

/-- **The assembled cyclotomic Dixon--Schneider solver succeeds on the certified `SL(2, 3)`
data.** -/
theorem isSome_dixonCyclotomicCharacterTable_specialLinearTwoThree :
    (specialLinearTwoThreeClassData.dixonCyclotomicCharacterTable? 12
      specialLinearTwoThreeDixonPrimeData).isSome = true := by
  apply specialLinearTwoThreeClassData.isSome_dixonCyclotomicCharacterTable_of_spec 12
    exponent_specialLinearGroup_two_three.symm specialLinearTwoThreeDixonPrimeData
    specialLinearTwoThreeExactCentralCharacterTable specialLinearTwoThreeExactCharacterTable
    specialLinearTwoThreeCharacterDegrees isCyclotomicCharacterTableSpec_specialLinearTwoThree
  rw [specialLinearTwoThreeDixonPrimeData_p]
  decide +kernel

/-- The displayed exact ordinary table, embedded in `ℂ` and reindexed by actual conjugacy
classes. -/
noncomputable def specialLinearTwoThreeComplexCharacterTable :
    Matrix (Fin (Nat.card (ConjClasses (SpecialLinearGroup (Fin 2) (ZMod 3)))))
      (ConjClasses (SpecialLinearGroup (Fin 2) (ZMod 3))) ℂ :=
  specialLinearTwoThreeClassData.complexTableOfCyclotomic 12
    specialLinearTwoThreeExactCharacterTable

/-- The embedded table evaluated at arbitrary row and conjugacy-class indices. -/
@[simp]
theorem specialLinearTwoThreeComplexCharacterTable_apply
    (i : Fin (Nat.card (ConjClasses (SpecialLinearGroup (Fin 2) (ZMod 3)))))
    (C : ConjClasses (SpecialLinearGroup (Fin 2) (ZMod 3))) :
    specialLinearTwoThreeComplexCharacterTable i C =
      Cyclotomic.complexEmbedding
        (specialLinearTwoThreeExactCharacterTable
          ((finCongr specialLinearTwoThreeClassData.numClasses_eq_card_conjClasses).symm i)
          (specialLinearTwoThreeClassData.equivConjClasses.symm C)) := by
  exact specialLinearTwoThreeClassData.complexTableOfCyclotomic_apply 12 _ _ _

/-- The embedded table evaluated at a numbered row and numbered conjugacy class. -/
theorem specialLinearTwoThreeComplexCharacterTable_apply_classOf
    (i j : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeComplexCharacterTable
        (finCongr specialLinearTwoThreeClassData.numClasses_eq_card_conjClasses i)
        (specialLinearTwoThreeClassData.classOf j) =
      Cyclotomic.complexEmbedding (specialLinearTwoThreeExactCharacterTable i j) := by
  exact specialLinearTwoThreeClassData.complexTableOfCyclotomic_apply_classOf 12 _ _ _

/-- **The embedded exact `SL(2, 3)` table satisfies the complex character-table
specification.** -/
theorem isCharacterTableSpec_specialLinearTwoThree :
    IsCharacterTableSpec (SpecialLinearGroup (Fin 2) (ZMod 3))
      specialLinearTwoThreeComplexCharacterTable :=
  isCyclotomicCharacterTableSpec_specialLinearTwoThree.isCharacterTableSpec

/-- Row `i` of the exact table `TauCeti.specialLinearTwoThreeExactCharacterTable`, embedded in `ℂ`
by `TauCeti.Cyclotomic.complexEmbedding` and read as a function on `SL(2, 3)` through the class
numbering `TauCeti.specialLinearTwoThreeClassData.index`. -/
noncomputable def specialLinearTwoThreeCharacter (i : SpecialLinearTwoThreeClassIndex)
    (g : SpecialLinearGroup (Fin 2) (ZMod 3)) : ℂ :=
  Cyclotomic.complexEmbedding
    (specialLinearTwoThreeExactCharacterTable i (specialLinearTwoThreeClassData.index g))

/-- An embedded row at `g` is the embedded table entry in the class of `g`. -/
theorem specialLinearTwoThreeCharacter_apply (i : SpecialLinearTwoThreeClassIndex)
    (g : SpecialLinearGroup (Fin 2) (ZMod 3)) :
    specialLinearTwoThreeCharacter i g =
      Cyclotomic.complexEmbedding
        (specialLinearTwoThreeExactCharacterTable i (specialLinearTwoThreeClassData.index g)) := by
  rfl

/-- **The irreducible characters of `SL(2, 3)`** are the seven embedded rows
`TauCeti.specialLinearTwoThreeCharacter` of the exact table. -/
theorem irreducibleCharacters_specialLinearTwoThree :
    irreducibleCharacters ℂ (SpecialLinearGroup (Fin 2) (ZMod 3)) =
      Set.range specialLinearTwoThreeCharacter :=
  ClassData.IsExactCharacterTableSpec.irreducibleCharacters_eq_range
    isCyclotomicCharacterTableSpec_specialLinearTwoThree _ Cyclotomic.complexEmbedding_star

/-- Every embedded row of the exact table is an irreducible character of `SL(2, 3)`. -/
theorem specialLinearTwoThreeCharacter_mem_irreducibleCharacters
    (i : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeCharacter i ∈
      irreducibleCharacters ℂ (SpecialLinearGroup (Fin 2) (ZMod 3)) := by
  rw [irreducibleCharacters_specialLinearTwoThree]
  exact Set.mem_range_self i

/-- At `1`, an embedded row takes the value of its degree. -/
@[simp]
theorem specialLinearTwoThreeCharacter_one (i : SpecialLinearTwoThreeClassIndex) :
    specialLinearTwoThreeCharacter i 1 = specialLinearTwoThreeCharacterDegrees i := by
  rw [specialLinearTwoThreeCharacter_apply,
    isCyclotomicCharacterTableSpec_specialLinearTwoThree.table_index_one, map_natCast]

/-- **The Burnside--Dixon--Schneider algorithm, searching for its own prime with budget `2`,
returns a character table of `SL(2, 3)`.** -/
theorem isSome_characterTableDixon_specialLinearTwoThree :
    (specialLinearTwoThreeClassData.characterTableDixon? 12
      exponent_specialLinearGroup_two_three.symm 2).isSome = true :=
  -- The search reaches `13`, finds the primitive twelfth root `2` there, and the solver succeeds.
  specialLinearTwoThreeClassData.isSome_characterTableDixon?_of_isSome 12
    exponent_specialLinearGroup_two_three.symm specialLinearTwoThreeDixonPrimeData
    (DixonPrimeData.ofPrime?_eq_some
      (ZMod.map_val_primitiveRoot?_eq_some_iff.mpr (by decide))) (by decide)
    isSome_dixonCyclotomicCharacterTable_specialLinearTwoThree

end TauCeti
