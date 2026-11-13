/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.AntipodalPairs.ModTwo
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.AntipodalPairs

/-!
# Leech minimal pairs in the mod-two module

The type-2 classes of the Leech lattice are the classes in `Λ / 2Λ` represented by vectors
of norm four. They form the set `leechLattice.normClassesModTwo 4`, not a second model
of the mod-two module. The minimum-norm bound identifies these classes with the 98280
antipodal pairs of minimal vectors: the class of a vector determines precisely its sign pair.

`leechAntipodalPairsEquivModTwo` gives this identification and intertwines the full
lattice-isometry action with its existing reduction homomorphism. In particular, the two
actions have the same stabilizers under this equivalence. No quotient of the isometry
group or identification with a sporadic presentation is assumed here.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 10.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti

open IntegralLattice

/-- The antipodal minimal-vector pairs of the Leech lattice identify with its type-2 residue
classes modulo twice the lattice. -/
noncomputable def leechAntipodalPairsEquivModTwo :
    leechLattice.antipodalPairs 4 ≃ leechLattice.normClassesModTwo 4 :=
  leechLattice.antipodalPairsEquivModTwo (by norm_num) fun z hz ↦
    four_le_norm_leechLattice z.property fun h ↦ hz (Subtype.ext h)

/-- The Leech identification is the sign-independent pair-to-residue map. -/
@[simp]
theorem leechAntipodalPairsEquivModTwo_apply (p : leechLattice.antipodalPairs 4) :
    leechAntipodalPairsEquivModTwo p = leechLattice.antipodalPairsToModTwo 4 p := by
  unfold leechAntipodalPairsEquivModTwo
  rw [antipodalPairsEquivModTwo_apply]

/-- There are exactly 98280 type-2 classes in the Leech mod-two module. -/
theorem ncard_normClassesModTwo_four_leechLattice :
    (leechLattice.normClassesModTwo 4).ncard = 98280 :=
  (Nat.card_congr leechAntipodalPairsEquivModTwo).symm.trans
    ncard_antipodalPairs_four_leechLattice

/-- The identification of minimal pairs with type-2 classes is equivariant for the actual
Leech lattice isometry group and its reduction on `Λ / 2Λ`. -/
theorem leechAntipodalPairsEquivModTwo_isometry (g : Isometry leechLattice leechLattice)
    (p : leechLattice.antipodalPairs 4) :
    (leechAntipodalPairsEquivModTwo (g.antipodalPairsEquiv 4 p) :
      QuotSMulTop (2 : ℤ) leechLattice) =
      Isometry.reductionHom leechLattice 2 g (leechAntipodalPairsEquivModTwo p) := by
  simpa only [leechAntipodalPairsEquivModTwo_apply] using
    leechLattice.antipodalPairsToModTwo_isometry 4 g p

/-- A Leech isometry fixes a minimal pair exactly when it fixes the corresponding type-2
class. This compares the actual stabilizers, not just their cardinalities. -/
theorem leechAntipodalPairsEquivModTwo_isometry_eq_iff
    (g : Isometry leechLattice leechLattice) (p : leechLattice.antipodalPairs 4) :
    g.antipodalPairsEquiv 4 p = p ↔
      Isometry.reductionHom leechLattice 2 g (leechAntipodalPairsEquivModTwo p) =
        (leechAntipodalPairsEquivModTwo p : QuotSMulTop (2 : ℤ) leechLattice) := by
  rw [← leechAntipodalPairsEquivModTwo.injective.eq_iff, Subtype.ext_iff,
    leechAntipodalPairsEquivModTwo_isometry]

end TauCeti
