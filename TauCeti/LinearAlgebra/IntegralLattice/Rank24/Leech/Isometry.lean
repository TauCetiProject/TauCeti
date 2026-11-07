/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.MinimalVectors
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.NormShell

/-!
# The faithful minimal-vector action of the Leech isometry group

The full lattice isometry group acts faithfully on the 196560 minimal vectors, since they
span the rational ambient space by `TauCeti.span_vectorsOfNorm_four_leechLattice`.
This gives a faithful permutation representation of the group usually denoted `Co₀`, without
assuming that any proposed list of Conway generators generates all lattice isometries.
Finiteness of the group already follows from the general positive-definite lattice API.
This is the action on vectors, not the action on antipodal pairs used for `Co₁`.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 10.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti

/-- The full Leech isometry group's action on the norm-four vectors is faithful. -/
theorem normShellHom_leechLattice_injective :
    Function.Injective (IntegralLattice.Isometry.normShellHom leechLattice 4) :=
  IntegralLattice.Isometry.normShellHom_injective 4 span_vectorsOfNorm_four_leechLattice

/-- The full Leech lattice isometry group is finite, since the lattice is positive definite. -/
instance instFiniteIsometryLeechLattice :
    Finite (IntegralLattice.Isometry leechLattice leechLattice) :=
  isPosDef_leechLattice.finite_isometry

end TauCeti
