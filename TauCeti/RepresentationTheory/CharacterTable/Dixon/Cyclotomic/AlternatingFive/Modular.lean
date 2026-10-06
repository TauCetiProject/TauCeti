/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.AlternatingFive.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.CentralCharacterCount
public import TauCeti.RingTheory.Cyclotomic.Lift

/-!
# Modular recovery of the central characters of A₅

Dixon's simultaneous eigenvalue search at the prime `61` returns exactly the five reductions
of the certified central-character table of `A₅`. Reduction uses the primitive fifth root
`9`; the two degree-three rows remain distinct. The coefficients of the exact central entries
lie in the balanced residue window, so their residues at all conjugate fifth roots reconstruct
the entries in `Cyclotomic 5`.

The group exponent is `30`. Its primitive root `4` modulo `61` has sixth power `9`, making
these reductions compatible with the root used for the full group exponent. The reconstruction
here takes place in the smaller ring containing the displayed character values.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446–450.
* J.-P. Serre, *Linear Representations of Finite Groups*, §5.2 (the displayed A₅ table).
-/

/- The modular-search and reconstruction formalization follows
`TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.AlternatingFour`. -/

public section

namespace TauCeti

open Matrix

local instance fact_prime_sixtyOne_alternatingFive : Fact (Nat.Prime 61) := ⟨by decide⟩

/-- `61` is a good Dixon prime for `A₅`: it splits exponent `30`, does not divide `60`,
and exceeds the size bound `2⌊√60⌋ = 14`. -/
theorem isGoodDixonPrime_alternatingGroup_five_sixtyOne :
    IsGoodDixonPrime (alternatingGroup (Fin 5)) 61 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  · rw [exponent_alternatingGroup_five]
    decide
  · rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    have hsqrt : Nat.sqrt 60 = 7 := ((Nat.eq_sqrt).2 (by norm_num)).symm
    norm_num [hsqrt]

/-- `4` is a primitive root of order `30` modulo `61`, matching the exponent of A₅. -/
theorem isPrimitiveRoot_alternatingGroupFive_exponentRoot :
    IsPrimitiveRoot (4 : ZMod 61) 30 :=
  IsPrimitiveRoot.mk_of_lt _ (by decide) (by decide)
    fun l hl0 hl30 ↦ by interval_cases l <;> decide

/-- `9` is a primitive fifth root modulo `61`, used to reduce the exact A₅ entries. -/
theorem isPrimitiveRoot_alternatingGroupFive_modularRoot :
    IsPrimitiveRoot (9 : ZMod 61) 5 := by
  have hpow : (4 : ZMod 61) ^ 6 = 9 := by decide
  simpa only [hpow] using IsPrimitiveRoot.pow (by decide)
    isPrimitiveRoot_alternatingGroupFive_exponentRoot (by decide : 30 = 6 * 5)

/-- The five central-character rows of A₅ reduced at the primitive fifth root `9` modulo `61`.
The input rows are trivial, the two degree-three rows, degree four, and degree five. -/
def alternatingGroupFiveModularCentralRows : Finset (AlternatingGroupFiveClassIndex → ZMod 61) :=
  alternatingGroupFiveClassData.rowsOfMap (Cyclotomic.reduce 61 9)
    alternatingGroupFiveCandidateCentralCharacterTable

/-- A row belongs to the displayed modular set precisely when it reduces one of the exact
central-character rows. -/
@[simp]
theorem mem_alternatingGroupFiveModularCentralRows_iff
    {a : AlternatingGroupFiveClassIndex → ZMod 61} :
    a ∈ alternatingGroupFiveModularCentralRows ↔
      ∃ i, (fun j ↦ Cyclotomic.reduce 61 9
        (alternatingGroupFiveCandidateCentralCharacterTable i j)) = a :=
  alternatingGroupFiveClassData.mem_rowsOfMap_iff _ _

/-- Entrywise modular reduction of the exact central-character table of A₅. -/
theorem reduce_alternatingGroupFiveCandidateCentralCharacterTable
    (i j : AlternatingGroupFiveClassIndex) :
    Cyclotomic.reduce 61 9 (alternatingGroupFiveCandidateCentralCharacterTable i j) =
      (!![1, 15, 20, 12, 12;
          1, 56, 0, 54, 11;
          1, 56, 0, 11, 54;
          1, 0, 5, 58, 58;
          1, 3, 57, 0, 0] : Matrix (Fin 5) (Fin 5) (ZMod 61))
        (finCongr numClasses_alternatingGroupFiveClassData i)
        (finCongr numClasses_alternatingGroupFiveClassData j) := by
  rw [alternatingGroupFiveCandidateCentralCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide

/-- The five exact central-character rows remain distinct modulo `61`. -/
@[simp]
theorem card_alternatingGroupFiveModularCentralRows :
    alternatingGroupFiveModularCentralRows.card = 5 := by
  simp only [alternatingGroupFiveModularCentralRows, ClassData.rowsOfMap,
    reduce_alternatingGroupFiveCandidateCentralCharacterTable]
  decide

/-- Dixon's executable modular search returns exactly the five reduced central-character
rows of A₅ at any primitive fifth root modulo `61`. Thus every conjugate residue needed for
the cyclotomic lift is represented in the search. -/
theorem alternatingGroupFive_centralCharacterSearch (α : ZMod 61)
    (hα : IsPrimitiveRoot α 5) :
    alternatingGroupFiveClassData.centralCharacterSearch (F := ZMod 61) =
      alternatingGroupFiveClassData.rowsOfMap (Cyclotomic.reduce 61 α)
        alternatingGroupFiveCandidateCentralCharacterTable := by
  let f := Cyclotomic.reduceRingHom 61 α hα
  apply alternatingGroupFiveClassData.centralCharacterSearch_eq_rowsOfMap_of_isGoodDixonPrime
    isGoodDixonPrime_alternatingGroup_five_sixtyOne (Cyclotomic.reduce 61 α)
    alternatingGroupFiveCandidateCentralCharacterTable
  · intro i
    rw [alternatingGroupFiveCandidateCentralCharacterTable_index_one]
    simpa only [← Cyclotomic.reduceRingHom_apply 61 α hα] using map_one f
  · intro i
    simpa only [f, Cyclotomic.reduceRingHom_apply] using
      (isModularEigenrow_alternatingGroupFiveCandidateCentralCharacterTable i).map f
  · have hG : (Fintype.card (alternatingGroup (Fin 5)) : ZMod 61) ≠ 0 := by
      simpa only [Nat.card_eq_fintype_card] using
        isGoodDixonPrime_alternatingGroup_five_sixtyOne.natCast_natCard_ne_zero
    have hinj := isCyclotomicCharacterTableSpec_alternatingGroupFive.map_central_injective f hG
    simp only [Cyclotomic.reduceRingHom_apply, f] at hinj
    rw [ClassData.rowsOfMap, Finset.card_image_of_injective _ hinj,
      Finset.card_univ, Fintype.card_fin]

/-- Dixon's modular search at prime `61` returns the named central-character row set of A₅,
reduced at the chosen primitive fifth root `9`. -/
@[simp]
theorem alternatingGroupFive_centralCharacterSearch_eq_modularCentralRows :
    alternatingGroupFiveClassData.centralCharacterSearch (F := ZMod 61) =
      alternatingGroupFiveModularCentralRows :=
  alternatingGroupFive_centralCharacterSearch 9 isPrimitiveRoot_alternatingGroupFive_modularRoot

/-- Every exact central-character coefficient of A₅ fits in the balanced residue window
modulo `61`. This includes the trivial row's entry `20`. -/
theorem alternatingGroupFiveCandidateCentralCharacterTable_two_mul_natAbs_coeff_lt
    (i j : AlternatingGroupFiveClassIndex) (k : Fin (5 : ℕ).totient) :
    2 * ((alternatingGroupFiveCandidateCentralCharacterTable i j).coeff k).natAbs < 61 := by
  rw [alternatingGroupFiveCandidateCentralCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide

/-- The structured cyclotomic lift recovers each exact central-character entry of A₅ from
its residues at all conjugates of any primitive fifth root modulo `61`. -/
theorem alternatingGroupFiveCandidateCentralCharacterTable_lift_conjugateResidues
    (i j : AlternatingGroupFiveClassIndex) {α : ZMod 61} (hα : IsPrimitiveRoot α 5) :
    Cyclotomic.lift 5 α
        (Cyclotomic.conjugateResidues α (alternatingGroupFiveCandidateCentralCharacterTable i j)) =
      alternatingGroupFiveCandidateCentralCharacterTable i j :=
  Cyclotomic.lift_conjugateResidues hα
    (alternatingGroupFiveCandidateCentralCharacterTable_two_mul_natAbs_coeff_lt i j)

end TauCeti
