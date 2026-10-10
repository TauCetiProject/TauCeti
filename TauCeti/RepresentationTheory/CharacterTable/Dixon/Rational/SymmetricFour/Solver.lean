/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.SymmetricFour.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.Solver

/-!
# Rational Dixon search for the symmetric group on four letters

The displayed character table of `S₄` has degrees `1, 1, 2, 3, 3`. This file identifies the
output of the modular central-character search with the reductions of its five central rows,
then proves that the signed integer lift recovers those rows exactly. The prime `37` is large
enough for every central entry, including `8`, to lie in the signed residue window. The smaller
good prime `13` would not have this property.

The existing integer certificate then proves success of the assembled rational Dixon solver.
The modular search and lift admit direct execution. Success of the assembled solver is
proved from its completeness characterization, rather than by evaluating its enumeration of
all possible row numberings and degree assignments.

Columns retain the cycle-type order `1⁴`, `2·1²`, `2²`, `3·1`, `4`. In particular, the two
degree-three rows remain distinct: their values on the odd classes have opposite signs.

## Main results

* `TauCeti.symmetricGroupFour_centralCharacterSearch`: the modular search returns precisely
  the reductions of the displayed central rows.
* `TauCeti.symmetricGroupFour_liftedCentralRows`: the signed lift recovers the integral rows.
* `TauCeti.isSome_dixonRationalCharacterTable_symmetricGroupFour`: the rational solver succeeds.

## References

* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik 10 (1967),
  446--450.
* G. J. A. Schneider, *Dixon's character table algorithm revisited*, Journal of Symbolic
  Computation 9 (1990), 601--606.
-/

public section

namespace TauCeti

/-- The prime `37` is a good Dixon prime for the symmetric group on four letters. -/
theorem isGoodDixonPrime_symmetricGroup_four_thirtySeven :
    IsGoodDixonPrime (Equiv.Perm (Fin 4)) 37 := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · rw [Nat.card_perm, Nat.card_fin]
    decide
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    decide +kernel
  · rw [Nat.card_perm, Nat.card_fin]
    have hsqrt : Nat.sqrt (Nat.factorial 4) < 5 := Nat.sqrt_lt.mpr (by norm_num)
    omega

local instance fact_prime_thirtySeven_symmetricFour : Fact (Nat.Prime 37) :=
  isGoodDixonPrime_symmetricGroup_four_thirtySeven.fact_prime

/-- The modular Dixon search at prime `37` returns exactly the reductions of the five
displayed integral central-character rows of `S₄`. -/
theorem symmetricGroupFour_centralCharacterSearch :
    symmetricGroupFourClassData.centralCharacterSearch (F := ZMod 37) =
      symmetricGroupFourClassData.rowsOfMap (fun x : ℤ => (x : ZMod 37))
        symmetricGroupFourCentralCharacterTable := by
  apply symmetricGroupFourClassData.centralCharacterSearch_eq_rowsOfMap_of_isGoodDixonPrime
    isGoodDixonPrime_symmetricGroup_four_thirtySeven
  · intro i
    rw [isIntegerCharacterTableSpec_symmetricGroupFour.central_one, Int.cast_one]
  · intro i
    exact (isModularEigenrow_symmetricGroupFourCentralCharacterTable_int i).map
      (Int.castRingHom (ZMod 37))
  · rw [ClassData.rowsOfMap, Finset.card_image_of_injective]
    · simp
    · exact isIntegerCharacterTableSpec_symmetricGroupFour.map_central_injective
        (Int.castRingHom (ZMod 37)) (by
          simpa only [Nat.card_eq_fintype_card] using
            isGoodDixonPrime_symmetricGroup_four_thirtySeven.natCast_natCard_ne_zero)

/-- The signed integer lift of the modular search recovers the five displayed central rows
of `S₄`, independently of their numbering. -/
theorem symmetricGroupFour_liftedCentralRows :
    symmetricGroupFourClassData.liftedCentralRows 37 =
      Finset.univ.image (fun i => symmetricGroupFourCentralCharacterTable i) := by
  apply symmetricGroupFourClassData.liftedCentralRows_eq_image_of_centralCharacterSearch_eq
    symmetricGroupFourCentralCharacterTable symmetricGroupFour_centralCharacterSearch
  intro i j
  simp only [symmetricGroupFourCentralCharacterTable_apply]
  fin_cases i <;> fin_cases j <;> decide +kernel

/-- The assembled rational Dixon solver succeeds for `S₄` at prime `37`. The returned table
is certified by the general solver soundness theorem. -/
theorem isSome_dixonRationalCharacterTable_symmetricGroupFour :
    (symmetricGroupFourClassData.dixonRationalCharacterTable? 37).isSome = true := by
  rw [symmetricGroupFourClassData.isSome_dixonRationalCharacterTable_iff]
  refine ⟨⟨symmetricGroupFourCentralCharacterTable, symmetricGroupFourCharacterTable,
    symmetricGroupFourCharacterDegrees⟩, ?_, isIntegerCharacterTableSpec_symmetricGroupFour⟩
  intro i
  rw [symmetricGroupFour_liftedCentralRows]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

end TauCeti
