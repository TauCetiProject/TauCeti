/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Reductive
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.LieContainment
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Central.Tangent
public import Mathlib.Algebra.Lie.Semisimple.Defs

/-!
# The Lie algebra of a reductive group in characteristic zero

Over an algebraically closed field of characteristic zero, the tangent Lie algebra of a
reductive affine group is reductive: its solvable radical equals its center. This connects
the group-theoretic definition using the unipotent radical with the Lie-algebra structure
theorem. In particular the Lie algebra is the direct sum of its center and its derived ideal,
and that derived ideal has nondegenerate Killing form.

The group radical is central by
`TauCeti.reductiveCommHopfAlgProperty.isCentral_solvableRadicalDefiningIdeal`.
Its Lie algebra is the Lie radical by
`TauCeti.FiniteTypeCommHopfAlgCat.lieIdeal_solvableRadicalDefiningIdeal_eq_radical`.
Centrality of the tangent image then gives the required inclusion; the center of any Lie
algebra lies in its solvable radical.

Import `TauCeti.Algebra.Lie.Reductive.Basic` and install `hG.hasCentralRadical_lieAlgebra` as a
local instance to apply
`TauCeti.isCompl_center_derivedSeries` and `TauCeti.isKilling_derivedSeries` to the tangent
Lie algebra. These statements concern the derived ideal of the Lie algebra; comparison
with the Lie algebra of the group-theoretic derived subgroup is a further step.

## References

* J. E. Humphreys, *Linear Algebraic Groups*, §13.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 19 and 22.
-/

public section

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The Lie algebra of a reductive affine group over an algebraically closed field of
characteristic zero has solvable radical equal to its center. -/
theorem hasCentralRadical_lieAlgebra (hH : reductiveCommHopfAlgProperty k H) :
    LieAlgebra.HasCentralRadical k
      (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  let _ : ConnectedSpace (PrimeSpectrum H) :=
    hH.geometricallyConnected.connectedSpace k H.obj
  apply LieAlgebra.hasCentralRadical_of_radical_le
  rw [← FiniteTypeCommHopfAlgCat.lieIdeal_solvableRadicalDefiningIdeal_eq_radical H]
  intro d hd
  exact hH.isCentral_solvableRadicalDefiningIdeal.lieSubalgebra_le_center
    ((HopfIdeal.mem_lieSubalgebra_iff _ d).mpr
      ((HopfIdeal.IsNormal.mem_lieIdeal_iff _ d).mp hd))

end TauCeti.reductiveCommHopfAlgProperty
