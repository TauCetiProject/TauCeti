/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Cyclotomic.Integer
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.SymmetricFour

/-!
# Cyclotomic Dixon recovery for S₄

The integer certificate for `S₄` also certifies recovery by the general cyclotomic solver.
The largest absolute central-character entry is `8`, so every Dixon prime greater than `16`
has a sufficiently large balanced residue window. Both distinct degree-three rows are retained.

`TauCeti.isSome_dixonCyclotomicCharacterTable_symmetricGroupFour` proves success for any such
prime data, independently of its chosen primitive root. The ordinary table, central table,
and degrees are those already certified in
`TauCeti.RepresentationTheory.CharacterTable.Dixon.Rational.SymmetricFour`.

## References

* G. James and M. Liebeck, *Representations and Characters of Groups*, Section 11.3.
* J. D. Dixon, *High speed computation of group characters*, Numerische Mathematik **10**
  (1967), 446–450.
-/

public section

namespace TauCeti

/-- The general cyclotomic Dixon solver recovers a certified character table of `S₄` at every
Dixon prime greater than `16`. The bound concerns central characters, including their entry `8`,
rather than just the smaller ordinary character values. -/
theorem isSome_dixonCyclotomicCharacterTable_symmetricGroupFour
    (e : ℕ) (he : e = Monoid.exponent (Equiv.Perm (Fin 4)))
    (q : DixonPrimeData (Equiv.Perm (Fin 4))) (hq : 16 < q.p) :
    (symmetricGroupFourClassData.dixonCyclotomicCharacterTable? e q).isSome = true := by
  apply isIntegerCharacterTableSpec_symmetricGroupFour.isSome_dixonCyclotomicCharacterTable
    e he q
  intro i j
  have hbound : 2 * (symmetricGroupFourCentralCharacterTable i j).natAbs ≤ 16 := by
    rw [symmetricGroupFourCentralCharacterTable_apply]
    fin_cases i <;> fin_cases j <;> decide
  exact hbound.trans_lt hq

end TauCeti
