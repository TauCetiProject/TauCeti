/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.Dihedral.Three
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.SymmetricFour
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.TotallyOrthogonal

/-!
# The symmetric groups `S₃` and `S₄` are totally orthogonal

Every irreducible complex representation of `S₃` and of `S₄` is orthogonal: its Frobenius-Schur
indicator is `1`. By `TauCeti.card_squareRoot_one_eq_sum_characterDegree_iff` this is the
numerical coincidence

`#{g : g² = 1} = ∑_χ χ(1)`,

which is checked here on both groups. The square roots of `1` are counted by evaluation, and the
character degrees are read off the certified character tables
(`TauCeti.isIntegerCharacterTableSpec_dihedralGroupThree` and
`TauCeti.isIntegerCharacterTableSpec_symmetricGroupFour`) through
`TauCeti.ClassData.IsIntegerCharacterTableSpec.sum_characterDegree_eq_sum_degree`:

* `S₃`, realized as `DihedralGroup 3`, has the identity and three transpositions, and degrees
  `1 + 1 + 2 = 4`;
* `S₄ = Equiv.Perm (Fin 4)` has the identity, six transpositions and three double transpositions,
  and degrees `1 + 1 + 2 + 3 + 3 = 10`.

## Main statements

* `TauCeti.frobeniusSchurIndicatorRow_dihedralGroupThree_eq_one`: every row of the character table
  of `S₃` has Frobenius-Schur indicator `1`.
* `TauCeti.frobeniusSchurIndicatorRow_symmetricGroupFour_eq_one`: the same for `S₄`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §5.8 and §13.2.
-/

public section

namespace TauCeti

/-- `S₃`, realized as `DihedralGroup 3`, has four solutions of `g² = 1`: the identity and the three
reflections. -/
theorem card_squareRoot_one_dihedralGroupThree :
    Nat.card {g : DihedralGroup 3 // g * g = 1} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The character degrees of `S₃`, realized as `DihedralGroup 3`, sum to `4`. -/
@[simp]
theorem sum_characterDegree_dihedralGroupThree :
    ∑ i, characterDegree ℂ (G := DihedralGroup 3) i = 4 := by
  rw [isIntegerCharacterTableSpec_dihedralGroupThree.sum_characterDegree_eq_sum_degree]
  simp only [dihedralGroupThreeCharacterDegrees_apply]
  decide

/-- **`S₃` is totally orthogonal**: every row of the character table of `DihedralGroup 3` has
Frobenius-Schur indicator `1`. -/
@[simp]
theorem frobeniusSchurIndicatorRow_dihedralGroupThree_eq_one
    (i : Fin (Nat.card (ConjClasses (DihedralGroup 3)))) :
    frobeniusSchurIndicatorRow ℂ i = 1 :=
  (card_squareRoot_one_eq_sum_characterDegree_iff ℂ (DihedralGroup 3)).mp
    (by rw [card_squareRoot_one_dihedralGroupThree, sum_characterDegree_dihedralGroupThree]) i

/-- `S₄` has ten solutions of `g² = 1`: the identity, the six transpositions and the three double
transpositions. -/
theorem card_squareRoot_one_symmetricGroupFour :
    Nat.card {g : Equiv.Perm (Fin 4) // g * g = 1} = 10 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The character degrees of `S₄` sum to `10`. -/
@[simp]
theorem sum_characterDegree_symmetricGroupFour :
    ∑ i, characterDegree ℂ (G := Equiv.Perm (Fin 4)) i = 10 := by
  rw [isIntegerCharacterTableSpec_symmetricGroupFour.sum_characterDegree_eq_sum_degree]
  simp only [symmetricGroupFourCharacterDegrees_apply]
  decide

/-- **`S₄` is totally orthogonal**: every row of the character table of `Equiv.Perm (Fin 4)` has
Frobenius-Schur indicator `1`. -/
@[simp]
theorem frobeniusSchurIndicatorRow_symmetricGroupFour_eq_one
    (i : Fin (Nat.card (ConjClasses (Equiv.Perm (Fin 4))))) :
    frobeniusSchurIndicatorRow ℂ i = 1 :=
  (card_squareRoot_one_eq_sum_characterDegree_iff ℂ (Equiv.Perm (Fin 4))).mp
    (by rw [card_squareRoot_one_symmetricGroupFour, sum_characterDegree_symmetricGroupFour]) i

end TauCeti
