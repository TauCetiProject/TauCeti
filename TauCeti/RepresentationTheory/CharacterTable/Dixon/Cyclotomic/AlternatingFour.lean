/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Alternating
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Solver

/-!
# The cyclotomic Dixon computation for the alternating group of degree four

This file certifies the exact character table of `A₄`.  Its four conjugacy classes have sizes
`1`, `3`, `4`, and `4`; the last two are the two classes of three-cycles.  If `ζ` is the
distinguished primitive sixth root in `TauCeti.Cyclotomic 6` and `ω = ζ²`, the ordinary table is

```
1  1   1    1
1  1   ω    ω²
1  1   ω²   ω
3 -1   0    0
```

The exponent of `A₄` is six.  The modular certificate uses the Dixon prime `7` and its primitive
sixth root `3`.  The assembled solver uses the larger Dixon prime `13` and the root `4`, whose
balanced residue window contains the central-character coefficients of absolute value four.  The
entries of `alternatingGroupFourExactCentralCharacterTable` are the class sizes times the
corresponding ordinary character values divided by the character degrees.  Reduction at the root
modulo `7` sends its four rows to precisely the output of the executable modular eigenrow search;
at the root modulo `13`, all conjugate reductions are pairwise distinct and reconstruct the exact
table.  The exact checker then verifies, inside the computable coefficient-vector ring
`Cyclotomic 6`, the central-character equations, the central-to-ordinary conversion, the
degree-square identity, and Hermitian row orthogonality.

The two nonreal linear rows form a nontrivial Galois-conjugate pair, so the exact certificate
simultaneously sees a nonlinear row and genuinely cyclotomic values.

## Main definitions

* `TauCeti.alternatingGroupFourDixonPrimeData`: the prime `7` with primitive sixth root `3`.
* `TauCeti.alternatingGroupFourSolverDixonPrimeData`: the prime `13` with primitive sixth root `4`.
* `TauCeti.alternatingGroupFourExactCentralCharacterTable`: the exact central-character table.
* `TauCeti.alternatingGroupFourExactCharacterTable`: the exact ordinary character table.
* `TauCeti.alternatingGroupFourCharacterDegrees`: the degrees `1`, `1`, `1`, and `3`.

## Main results

* `TauCeti.alternatingGroupFour_centralCharacterSearch`: the modular search returns exactly the
  reductions of the four displayed central-character rows.
* `TauCeti.star_alternatingGroupFourExactCharacterTable_row_one`: exact conjugation exchanges the
  two nonreal linear rows.
* `TauCeti.alternatingGroupFourExactCharacterTable_lift_conjugateResidues`: the structured lift
  recovers every exact ordinary-table entry from its conjugate residues.
* `TauCeti.isSome_dixonCyclotomicCharacterTable_alternatingGroupFour`: the assembled exact solver
  succeeds on the certified data.
* `TauCeti.isCyclotomicCharacterTableSpec_alternatingGroupFour`: the exact tables pass the
  executable cyclotomic certificate.
* `TauCeti.isCharacterTableSpec_alternatingGroupFour`: the distinguished complex embedding of the
  displayed ordinary table is a character table of `A₄`.

## References

The formal declaration order and proof plan follow
`TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.CyclicThree`.  The computation uses
the Burnside--Dixon--Schneider framework and the classical table in J.-P. Serre, *Linear
Representations of Finite Groups*, §5.2.

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. Schneider, *Dixon's character table algorithm revisited*, Journal of Symbolic Computation 9
  (1990), 601--606.
-/

public section

namespace TauCeti

open Matrix

local instance fact_prime_seven_alternatingFour : Fact (Nat.Prime 7) := ⟨by decide⟩
local instance fact_prime_thirteen_alternatingFour : Fact (Nat.Prime 13) := ⟨by decide⟩

private theorem sqrt_twelve : Nat.sqrt 12 = 3 := by
  exact ((Nat.eq_sqrt).2 (by norm_num)).symm

/-- **`7` is a good Dixon prime for `A₄`**: it does not divide `12`, the exponent `6` divides
`7 - 1`, and `2⌊√12⌋ = 6 < 7`. -/
theorem isGoodDixonPrime_alternatingGroup_four_seven :
    IsGoodDixonPrime (alternatingGroup (Fin 4)) 7 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [natCard_alternatingGroup_four]
    decide
  · rw [exponent_alternatingGroup_four]
  · rw [natCard_alternatingGroup_four, sqrt_twelve]
    norm_num

/-- Dixon prime data for `A₄`: the prime `7`, with `3` as a primitive sixth root of unity. -/
@[expose] def alternatingGroupFourDixonPrimeData :
    DixonPrimeData (alternatingGroup (Fin 4)) where
  p := 7
  root := 3
  isGoodDixonPrime := isGoodDixonPrime_alternatingGroup_four_seven
  isPrimitiveRoot_root := by
    simpa only [exponent_alternatingGroup_four] using
      (IsPrimitiveRoot.mk_of_lt (3 : ZMod 7) (by norm_num) (by decide)
        fun l hl0 hl6 => by interval_cases l <;> decide)

/-- The prime carried by `TauCeti.alternatingGroupFourDixonPrimeData` is `7`. -/
@[simp]
theorem alternatingGroupFourDixonPrimeData_p : alternatingGroupFourDixonPrimeData.p = 7 := rfl

/-- The primitive sixth root carried by `TauCeti.alternatingGroupFourDixonPrimeData` is `3`. -/
@[simp]
theorem alternatingGroupFourDixonPrimeData_root :
    alternatingGroupFourDixonPrimeData.root = 3 := rfl

/-- **`13` is a good Dixon prime for `A₄`** whose residue window also contains every
central-character coefficient in the displayed table. -/
theorem isGoodDixonPrime_alternatingGroup_four_thirteen :
    IsGoodDixonPrime (alternatingGroup (Fin 4)) 13 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [natCard_alternatingGroup_four]
    decide
  · rw [exponent_alternatingGroup_four]
    norm_num
  · rw [natCard_alternatingGroup_four, sqrt_twelve]
    norm_num

/-- Dixon prime data used by the assembled `A₄` solver: the prime `13`, with `4` as a
primitive sixth root.  The larger prime is needed to reconstruct the central-character entries
whose coefficients have absolute value four. -/
@[expose] def alternatingGroupFourSolverDixonPrimeData :
    DixonPrimeData (alternatingGroup (Fin 4)) where
  p := 13
  root := 4
  isGoodDixonPrime := isGoodDixonPrime_alternatingGroup_four_thirteen
  isPrimitiveRoot_root := by
    simpa only [exponent_alternatingGroup_four] using
      (IsPrimitiveRoot.mk_of_lt (4 : ZMod 13) (by norm_num) (by decide)
        fun l hl0 hl6 ↦ by interval_cases l <;> decide)

/-- The prime carried by `TauCeti.alternatingGroupFourSolverDixonPrimeData` is `13`. -/
@[simp]
theorem alternatingGroupFourSolverDixonPrimeData_p :
    alternatingGroupFourSolverDixonPrimeData.p = 13 := rfl

/-- The primitive sixth root carried by `TauCeti.alternatingGroupFourSolverDixonPrimeData` is
`4`. -/
@[simp]
theorem alternatingGroupFourSolverDixonPrimeData_root :
    alternatingGroupFourSolverDixonPrimeData.root = 4 := rfl

/-- The numbered conjugacy classes of the alternating group of degree four. -/
abbrev AlternatingGroupFourClassIndex := Fin alternatingGroupFourClassData.numClasses

/-- The primitive cube root `ζ²` in the sixth cyclotomic ring. -/
abbrev alternatingGroupFourOmega : Cyclotomic 6 := Cyclotomic.zeta 6 ^ 2

/-- **The exact central-character table of `A₄`.**  Columns are the identity, the class of
double transpositions, and the two classes of three-cycles. -/
def alternatingGroupFourExactCentralCharacterTable :
    Matrix AlternatingGroupFourClassIndex AlternatingGroupFourClassIndex (Cyclotomic 6) :=
  let ω := alternatingGroupFourOmega
  !![1,  3,     4,       4;
     1,  3, 4 * ω, 4 * ω ^ 2;
     1,  3, 4 * ω ^ 2, 4 * ω;
     1, -1,     0,       0]

/-- The entrywise formula for the exact central-character table. -/
@[simp]
theorem alternatingGroupFourExactCentralCharacterTable_apply
    (i j : AlternatingGroupFourClassIndex) :
    alternatingGroupFourExactCentralCharacterTable i j =
      (let ω := alternatingGroupFourOmega
       !![1,  3,     4,       4;
          1,  3, 4 * ω, 4 * ω ^ 2;
          1,  3, 4 * ω ^ 2, 4 * ω;
          1, -1,     0,       0] i j) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The exact ordinary character table of `A₄`, in the same row and column order as the
central-character table. -/
def alternatingGroupFourExactCharacterTable :
    Matrix AlternatingGroupFourClassIndex AlternatingGroupFourClassIndex (Cyclotomic 6) :=
  let ω := alternatingGroupFourOmega
  !![1,  1,   1,     1;
     1,  1,   ω, ω ^ 2;
     1,  1, ω ^ 2,   ω;
     3, -1,   0,     0]

/-- The entrywise formula for the exact ordinary character table. -/
@[simp]
theorem alternatingGroupFourExactCharacterTable_apply
    (i j : AlternatingGroupFourClassIndex) :
    alternatingGroupFourExactCharacterTable i j =
      (let ω := alternatingGroupFourOmega
       !![1,  1,   1,     1;
          1,  1,   ω, ω ^ 2;
          1,  1, ω ^ 2,   ω;
          3, -1,   0,     0] i j) := by
  fin_cases i <;> fin_cases j <;> decide

/-- The character degrees attached to the four exact rows. -/
def alternatingGroupFourCharacterDegrees : AlternatingGroupFourClassIndex → ℕ :=
  ![1, 1, 1, 3]

/-- The entries of the degree vector are `1`, `1`, `1`, and `3`. -/
@[simp]
theorem alternatingGroupFourCharacterDegrees_apply (i : AlternatingGroupFourClassIndex) :
    alternatingGroupFourCharacterDegrees i = ![1, 1, 1, 3] i := by
  rfl

/-- Exact conjugation exchanges the two nonreal linear rows of the `A₄` table. -/
theorem star_alternatingGroupFourExactCharacterTable_row_one
    (j : AlternatingGroupFourClassIndex) :
    star (alternatingGroupFourExactCharacterTable ⟨1, by simp⟩ j) =
      alternatingGroupFourExactCharacterTable ⟨2, by simp⟩ j := by
  fin_cases j <;> decide

/-- The two rows exchanged by exact conjugation are genuinely distinct. -/
theorem alternatingGroupFourExactCharacterTable_row_one_ne_row_two :
    alternatingGroupFourExactCharacterTable ⟨1, by simp⟩ ≠
      alternatingGroupFourExactCharacterTable ⟨2, by simp⟩ := by
  decide

/-- Every displayed central-character row is normalized at the identity class. -/
theorem alternatingGroupFourExactCentralCharacterTable_index_one
    (i : AlternatingGroupFourClassIndex) :
    alternatingGroupFourExactCentralCharacterTable i
      (alternatingGroupFourClassData.index 1) = 1 := by
  fin_cases i <;> decide

/-- Every displayed exact central-character row satisfies the class-algebra eigenrow equations. -/
theorem isModularEigenrow_alternatingGroupFourExactCentralCharacterTable
    (i : AlternatingGroupFourClassIndex) :
    alternatingGroupFourClassData.IsModularEigenrow
      (alternatingGroupFourExactCentralCharacterTable i) := by
  rw [alternatingGroupFourClassData.isModularEigenrow_iff]
  fin_cases i <;> decide

/-- **The displayed exact `A₄` tables pass the cyclotomic character-table certificate.** -/
theorem isCyclotomicCharacterTableSpec_alternatingGroupFour :
    alternatingGroupFourClassData.IsCyclotomicCharacterTableSpec 6
      alternatingGroupFourExactCentralCharacterTable alternatingGroupFourExactCharacterTable
      alternatingGroupFourCharacterDegrees := by
  decide

/-- The executable exact cyclotomic checker accepts the displayed `A₄` tables. -/
theorem cyclotomicCharacterTableChecker_alternatingGroupFour :
    alternatingGroupFourClassData.cyclotomicCharacterTableChecker 6
      alternatingGroupFourExactCentralCharacterTable alternatingGroupFourExactCharacterTable
      alternatingGroupFourCharacterDegrees = true :=
  (alternatingGroupFourClassData.cyclotomicCharacterTableChecker_eq_true_iff 6 _ _ _).2
    isCyclotomicCharacterTableSpec_alternatingGroupFour

/-- The displayed exact central-character rows reduced at the primitive sixth root `3` modulo
`7`. -/
def alternatingGroupFourModularCentralRows :
    Finset (AlternatingGroupFourClassIndex → ZMod 7) :=
  alternatingGroupFourClassData.rowsOfMap
    (Cyclotomic.reduce 7 alternatingGroupFourDixonPrimeData.root)
    alternatingGroupFourExactCentralCharacterTable

/-- A modular row is displayed exactly when it is the reduction of a row of the exact
central-character table. -/
@[simp]
theorem mem_alternatingGroupFourModularCentralRows_iff
    {a : AlternatingGroupFourClassIndex → ZMod 7} :
    a ∈ alternatingGroupFourModularCentralRows ↔
      ∃ i, (fun j ↦ Cyclotomic.reduce 7 alternatingGroupFourDixonPrimeData.root
        (alternatingGroupFourExactCentralCharacterTable i j)) = a :=
  alternatingGroupFourClassData.mem_rowsOfMap_iff _ _

/-- Reduction at the chosen root preserves every exact central-character eigenrow equation. -/
theorem isModularEigenrow_alternatingGroupFourExactCentralCharacterTable_zmod
    (i : AlternatingGroupFourClassIndex) :
    alternatingGroupFourClassData.IsModularEigenrow fun j ↦
      Cyclotomic.reduce 7 alternatingGroupFourDixonPrimeData.root
        (alternatingGroupFourExactCentralCharacterTable i j) := by
  have hroot : IsPrimitiveRoot alternatingGroupFourDixonPrimeData.root 6 := by
    simpa only [exponent_alternatingGroup_four] using
      alternatingGroupFourDixonPrimeData.isPrimitiveRoot_root
  have hmap := (isModularEigenrow_alternatingGroupFourExactCentralCharacterTable i).map
    (Cyclotomic.reduceRingHom 7 alternatingGroupFourDixonPrimeData.root hroot)
  rw [alternatingGroupFourClassData.isModularEigenrow_iff] at hmap ⊢
  intro a b
  simpa only [← Cyclotomic.reduceRingHom_apply 7 alternatingGroupFourDixonPrimeData.root hroot]
    using hmap a b

/-- The four displayed modular central-character rows are pairwise distinct. -/
@[simp]
theorem card_alternatingGroupFourModularCentralRows :
    alternatingGroupFourModularCentralRows.card = 4 := by
  decide

/-- **The executable modular central-character search for `A₄` returns precisely the four
reductions of the displayed exact central-character rows.** -/
theorem alternatingGroupFour_centralCharacterSearch :
    alternatingGroupFourClassData.centralCharacterSearch (F := ZMod 7) =
      alternatingGroupFourModularCentralRows := by
  rw [alternatingGroupFourModularCentralRows]
  apply alternatingGroupFourClassData.centralCharacterSearch_eq_rowsOfMap_of_isGoodDixonPrime
    isGoodDixonPrime_alternatingGroup_four_seven
    (Cyclotomic.reduce 7 alternatingGroupFourDixonPrimeData.root)
    alternatingGroupFourExactCentralCharacterTable
  · intro i
    have hroot : IsPrimitiveRoot alternatingGroupFourDixonPrimeData.root 6 := by
      simpa only [exponent_alternatingGroup_four] using
        alternatingGroupFourDixonPrimeData.isPrimitiveRoot_root
    rw [alternatingGroupFourExactCentralCharacterTable_index_one]
    simpa only [← Cyclotomic.reduceRingHom_apply 7 alternatingGroupFourDixonPrimeData.root hroot]
      using map_one (Cyclotomic.reduceRingHom 7 alternatingGroupFourDixonPrimeData.root hroot)
  · exact isModularEigenrow_alternatingGroupFourExactCentralCharacterTable_zmod
  · simpa only [alternatingGroupFourModularCentralRows,
      numClasses_alternatingGroupFourClassData] using
      card_alternatingGroupFourModularCentralRows

/-- Every coordinate of every displayed ordinary-table entry satisfies Dixon's coefficient
bound. -/
theorem alternatingGroupFourExactCharacterTable_natAbs_coeff_le_sqrt
    (i j : AlternatingGroupFourClassIndex) (k : Fin (6 : ℕ).totient) :
    ((alternatingGroupFourExactCharacterTable i j).coeff k).natAbs ≤
      Nat.sqrt (Nat.card (alternatingGroup (Fin 4))) := by
  rw [natCard_alternatingGroup_four, sqrt_twelve]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- **The structured cyclotomic lift recovers every exact ordinary-table entry from its residues
at the two conjugate primitive sixth roots modulo `7`.** -/
theorem alternatingGroupFourExactCharacterTable_lift_conjugateResidues
    (i j : AlternatingGroupFourClassIndex) :
    Cyclotomic.lift 6 alternatingGroupFourDixonPrimeData.root
        (Cyclotomic.conjugateResidues alternatingGroupFourDixonPrimeData.root
          (alternatingGroupFourExactCharacterTable i j)) =
      alternatingGroupFourExactCharacterTable i j := by
  have hLift : ∀ {x : Cyclotomic (Monoid.exponent (alternatingGroup (Fin 4)))},
      (∀ k : Fin (Monoid.exponent (alternatingGroup (Fin 4))).totient,
        (x.coeff k).natAbs ≤ Nat.sqrt (Nat.card (alternatingGroup (Fin 4)))) →
      Cyclotomic.lift (Monoid.exponent (alternatingGroup (Fin 4)))
        alternatingGroupFourDixonPrimeData.root
        (Cyclotomic.conjugateResidues alternatingGroupFourDixonPrimeData.root x) = x :=
    fun {_} => alternatingGroupFourDixonPrimeData.lift_conjugateResidues
  rw [exponent_alternatingGroup_four] at hLift
  exact hLift (alternatingGroupFourExactCharacterTable_natAbs_coeff_le_sqrt i j)

/-- **The assembled cyclotomic Dixon--Schneider solver succeeds on the certified `A₄` data.** -/
theorem isSome_dixonCyclotomicCharacterTable_alternatingGroupFour :
    (alternatingGroupFourClassData.dixonCyclotomicCharacterTable? 6
      exponent_alternatingGroup_four.symm
      alternatingGroupFourSolverDixonPrimeData).isSome = true := by
  apply alternatingGroupFourClassData.isSome_dixonCyclotomicCharacterTable_of_spec 6
    exponent_alternatingGroup_four.symm alternatingGroupFourSolverDixonPrimeData
    alternatingGroupFourExactCentralCharacterTable alternatingGroupFourExactCharacterTable
    alternatingGroupFourCharacterDegrees isCyclotomicCharacterTableSpec_alternatingGroupFour
  · intro i j k
    rw [alternatingGroupFourSolverDixonPrimeData_p]
    fin_cases i <;> fin_cases j <;> fin_cases k <;> decide
  · intro j i i' h
    have hroot : IsPrimitiveRoot
        (Cyclotomic.conjugateRoot 6 (4 : ZMod 13) j) 6 :=
      Cyclotomic.isPrimitiveRoot_conjugateRoot
        (IsPrimitiveRoot.mk_of_lt (4 : ZMod 13) (by norm_num) (by decide)
          fun l hl0 hl6 ↦ by interval_cases l <;> decide) j
    let f := Cyclotomic.reduceRingHom 13
      (Cyclotomic.conjugateRoot 6 (4 : ZMod 13) j) hroot
    let k₁ : AlternatingGroupFourClassIndex := ⟨1, by decide⟩
    let k₂ : AlternatingGroupFourClassIndex := ⟨2, by decide⟩
    have hcol₁ (r : AlternatingGroupFourClassIndex) :
        alternatingGroupFourExactCentralCharacterTable r k₁ =
          if r.val = 3 then -1 else 3 := by
      fin_cases r <;> decide
    have hcol₂ (r : AlternatingGroupFourClassIndex) :
        alternatingGroupFourExactCentralCharacterTable r k₂ =
          if r.val = 3 then 0 else 4 * alternatingGroupFourOmega ^ r.val := by
      fin_cases r <;> decide
    have h₁ := congrFun h k₁
    have h₂ := congrFun h k₂
    change Cyclotomic.conjugateResidues (4 : ZMod 13)
        (alternatingGroupFourExactCentralCharacterTable i k₁) j =
      Cyclotomic.conjugateResidues (4 : ZMod 13)
        (alternatingGroupFourExactCentralCharacterTable i' k₁) j at h₁
    change Cyclotomic.conjugateResidues (4 : ZMod 13)
        (alternatingGroupFourExactCentralCharacterTable i k₂) j =
      Cyclotomic.conjugateResidues (4 : ZMod 13)
        (alternatingGroupFourExactCentralCharacterTable i' k₂) j at h₂
    simp only [Cyclotomic.conjugateResidues_apply] at h₁ h₂
    rw [← Cyclotomic.reduceRingHom_apply 13 _ hroot,
      ← Cyclotomic.reduceRingHom_apply 13 _ hroot] at h₁ h₂
    change f (alternatingGroupFourExactCentralCharacterTable i k₁) =
      f (alternatingGroupFourExactCentralCharacterTable i' k₁) at h₁
    change f (alternatingGroupFourExactCentralCharacterTable i k₂) =
      f (alternatingGroupFourExactCentralCharacterTable i' k₂) at h₂
    rw [hcol₁ i, hcol₁ i'] at h₁
    rw [hcol₂ i, hcol₂ i'] at h₂
    have hfzeta : f (Cyclotomic.zeta 6) =
        Cyclotomic.conjugateRoot 6 (4 : ZMod 13) j := by
      dsimp only [f]
      rw [Cyclotomic.reduceRingHom_apply, Cyclotomic.reduce_zeta]
      exact hroot
    have hf3 : f (3 : Cyclotomic 6) = (3 : ZMod 13) := map_ofNat f 3
    have hf4 : f (4 : Cyclotomic 6) = (4 : ZMod 13) := map_ofNat f 4
    have hfneg1 : f (-1 : Cyclotomic 6) = (-1 : ZMod 13) := by
      rw [map_neg, map_one]
    have hthree_ne_neg_one : (3 : ZMod 13) ≠ -1 := by decide
    apply Fin.ext
    have hi_lt : i.val < 4 := by
      simpa only [numClasses_alternatingGroupFourClassData] using i.isLt
    have hi'_lt : i'.val < 4 := by
      simpa only [numClasses_alternatingGroupFourClassData] using i'.isLt
    interval_cases hi : i.val <;> interval_cases hi' : i'.val <;> try rfl
    all_goals
      simp only [Nat.reduceEqDiff, reduceCtorEq, ↓reduceIte] at h₁ h₂
      first
      | exact (hthree_ne_neg_one (by simpa only [hf3, hfneg1] using h₁)).elim
      | exact (hthree_ne_neg_one (by simpa only [hf3, hfneg1] using h₁.symm)).elim
      | simp only [map_mul, map_pow, hf4, alternatingGroupFourOmega, hfzeta] at h₂
        have hpows := mul_left_cancel₀ (show (4 : ZMod 13) ≠ 0 by decide) h₂
        rw [← pow_mul, ← pow_mul] at hpows
        have hexponents := hroot.pow_inj (by norm_num) (by norm_num) hpows
        omega
  · intro i j
    fin_cases i <;> fin_cases j <;> decide

/-- The displayed exact ordinary table, embedded in `ℂ` and reindexed by actual conjugacy
classes. -/
noncomputable def alternatingGroupFourComplexCharacterTable :
    Matrix (Fin (Nat.card (ConjClasses (alternatingGroup (Fin 4)))))
      (ConjClasses (alternatingGroup (Fin 4))) ℂ :=
  alternatingGroupFourClassData.complexTableOfCyclotomic 6
    alternatingGroupFourExactCharacterTable

/-- The embedded table evaluated at arbitrary row and conjugacy-class indices. -/
@[simp]
theorem alternatingGroupFourComplexCharacterTable_apply
    (i : Fin (Nat.card (ConjClasses (alternatingGroup (Fin 4)))))
    (C : ConjClasses (alternatingGroup (Fin 4))) :
    alternatingGroupFourComplexCharacterTable i C =
      Cyclotomic.complexEmbedding
        (alternatingGroupFourExactCharacterTable
          ((finCongr alternatingGroupFourClassData.numClasses_eq_card_conjClasses).symm i)
          (alternatingGroupFourClassData.equivConjClasses.symm C)) := by
  exact alternatingGroupFourClassData.complexTableOfCyclotomic_apply 6 _ _ _

/-- The embedded table evaluated at a numbered row and numbered conjugacy class. -/
theorem alternatingGroupFourComplexCharacterTable_apply_classOf
    (i j : AlternatingGroupFourClassIndex) :
    alternatingGroupFourComplexCharacterTable
        (finCongr alternatingGroupFourClassData.numClasses_eq_card_conjClasses i)
        (alternatingGroupFourClassData.classOf j) =
      Cyclotomic.complexEmbedding (alternatingGroupFourExactCharacterTable i j) := by
  exact alternatingGroupFourClassData.complexTableOfCyclotomic_apply_classOf 6 _ _ _

/-- **The embedded exact `A₄` table satisfies the complex character-table specification.** -/
theorem isCharacterTableSpec_alternatingGroupFour :
    IsCharacterTableSpec (alternatingGroup (Fin 4))
      alternatingGroupFourComplexCharacterTable :=
  isCyclotomicCharacterTableSpec_alternatingGroupFour.isCharacterTableSpec

end TauCeti
