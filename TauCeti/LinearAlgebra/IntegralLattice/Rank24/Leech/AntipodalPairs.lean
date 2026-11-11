/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.AntipodalPairs
public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.MinimalVectors

/-!
# The 98280 antipodal pairs of Leech minimal vectors

Negation acts without fixed points on the norm-four vectors of the canonical Construction-B
Leech lattice. Its 196560 minimal vectors therefore give exactly 98280 unordered antipodal
pairs. This supplies the underlying finite set for the Conway action on minimal-vector pairs.
The pairs are actual unordered pairs in the existing lattice carrier, with no choice of sign.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti

/-- The antipodal pairs of Leech minimal vectors form a finite set. -/
instance instFiniteAntipodalPairsFourLeechLattice :
    Finite (leechLattice.antipodalPairs 4) :=
  (IntegralLattice.finite_antipodalPairs
    (isPosDef_leechLattice.finite_vectorsOfNorm 4)).to_subtype

/-- The Leech lattice has exactly 98280 antipodal pairs of minimal vectors. -/
theorem ncard_antipodalPairs_four_leechLattice :
    (leechLattice.antipodalPairs 4).ncard = 98280 := by
  rw [IntegralLattice.ncard_antipodalPairs (by norm_num)
    (isPosDef_leechLattice.finite_vectorsOfNorm 4), ncard_vectorsOfNorm_four_leechLattice]

end TauCeti
