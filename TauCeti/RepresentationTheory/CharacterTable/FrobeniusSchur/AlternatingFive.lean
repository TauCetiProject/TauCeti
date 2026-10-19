/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.AlternatingFive.Basic
public import TauCeti.RepresentationTheory.CharacterTable.FrobeniusSchur.TotallyOrthogonal

/-!
# The alternating group `A₅` is totally orthogonal

Every irreducible complex representation of `A₅` is orthogonal: its Frobenius--Schur indicator is
`1`. By `TauCeti.card_squareRoot_one_eq_sum_characterDegree_iff`, this follows from the equality

`#{g : g² = 1} = ∑_χ χ(1)`.

The left side is `16`, consisting of the identity and the fifteen double transpositions. The right
side is `1 + 3 + 3 + 4 + 5 = 16`, read from the certified exact cyclotomic character table in
`TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.AlternatingFive.Basic`.

## Main statements

* `TauCeti.card_squareRoot_one_alternatingGroupFive`: `A₅` has sixteen elements whose square is
  one.
* `TauCeti.sum_characterDegree_alternatingGroupFive`: its irreducible character degrees sum to
  sixteen.
* `TauCeti.frobeniusSchurIndicatorRow_alternatingGroupFive_eq_one`: every character-table row has
  Frobenius--Schur indicator `1`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, GTM 42 (1977), §5.8 and §13.2.
-/

public section

namespace TauCeti

/-- `A₅` has sixteen solutions of `g² = 1`: the identity and the fifteen double
transpositions. -/
theorem card_squareRoot_one_alternatingGroupFive :
    Nat.card {g : alternatingGroup (Fin 5) // g * g = 1} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

/-- The character degrees of `A₅` sum to `16`. -/
@[simp]
theorem sum_characterDegree_alternatingGroupFive :
    ∑ i, characterDegree ℂ (G := alternatingGroup (Fin 5)) i = 16 := by
  rw [isCyclotomicCharacterTableSpec_alternatingGroupFive.sum_characterDegree_eq_sum_degree]
  simp only [alternatingGroupFiveCandidateCharacterDegrees_apply]
  decide

/-- **`A₅` is totally orthogonal**: every row of its character table has Frobenius--Schur
indicator `1`. -/
@[simp]
theorem frobeniusSchurIndicatorRow_alternatingGroupFive_eq_one
    (i : Fin (Nat.card (ConjClasses (alternatingGroup (Fin 5))))) :
    frobeniusSchurIndicatorRow ℂ i = 1 :=
  (card_squareRoot_one_eq_sum_characterDegree_iff ℂ (alternatingGroup (Fin 5))).mp
    (by rw [card_squareRoot_one_alternatingGroupFive,
      sum_characterDegree_alternatingGroupFive]) i

end TauCeti
