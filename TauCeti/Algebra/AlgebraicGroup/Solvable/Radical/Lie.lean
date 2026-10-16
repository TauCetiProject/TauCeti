/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Basic
public import TauCeti.Algebra.AlgebraicGroup.Solvable.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Normal.Tangent
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Dimension

/-!
# The Lie algebra of a solvable-radical candidate

The tangent Lie ideal of a smooth geometrically connected solvable normal closed subgroup
lies in the solvable radical of the ambient Lie algebra. This applies in particular to the
group's solvable radical, using
`FiniteTypeCommHopfAlgCat.isSolvableRadicalCandidate_solvableRadicalDefiningIdeal`.

Normality makes the tangent image an ideal. Its solvability follows from
`geometricallySolvablePointsCommHopfAlgProperty.isSolvable_lieAlgebra`, and the universal
property of the Lie radical gives the containment. No characteristic assumption or
smoothness of the ambient group is needed. Equality with the Lie radical is not asserted.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 10 and 16.
-/

public section

namespace TauCeti.HopfIdeal.IsSolvableRadicalCandidate

universe u

/-- The tangent Lie ideal of a connected smooth solvable normal closed subgroup is contained
in the radical of the ambient tangent Lie algebra, in every characteristic. -/
theorem lieIdeal_le_radical {k : Type u} [Field k]
    {H : FiniteTypeCommHopfAlgCat.{u, u} k} {I : HopfIdeal k H}
    (hI : IsSolvableRadicalCandidate H I) :
    hI.isNormal.lieIdeal (B := k) ≤
      LieAlgebra.radical k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by
  let Q := FiniteTypeCommHopfAlgCat.quotient H I
  let _ : Algebra.Smooth k Q := hI.smooth
  let _ : Algebra.IsGeometricallyReduced k Q := isGeometricallyReduced_of_smooth k Q
  have hQ := hI.geometricallySolvable.isSolvable_lieAlgebra hI.geometricallyConnected
  have hsub : LieAlgebra.IsSolvable
      (LieIdeal.toLieSubalgebra k _ (hI.isNormal.lieIdeal (B := k))) := by
    rw [hI.isNormal.lieIdeal_toLieSubalgebra]
    exact (LieAlgebra.solvable_iff_equiv_solvable (I.quotientLieEquiv (B := k))).mp hQ
  exact (LieAlgebra.LieIdeal.solvable_iff_le_radical k _ _).mp hsub

end TauCeti.HopfIdeal.IsSolvableRadicalCandidate
