/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Solvable.Radical.Construction
public import TauCeti.Algebra.AlgebraicGroup.Reductive.Solvable
import TauCeti.Algebra.AlgebraicGroup.Reductive.NormalSubgroup
import TauCeti.Algebra.AlgebraicGroup.MultiplicativeType.Normal
import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# The radical of a reductive group

The solvable radical of a reductive affine group over any field is a central torus, in every
characteristic. The torus need not split over the ground field, and centrality is
scheme-theoretic: it controls points over arbitrary commutative value algebras.

The radical is a smooth geometrically connected normal subgroup, so
`TauCeti.reductiveCommHopfAlgProperty.quotient_of_isNormal` makes it reductive.
The classification of solvable reductive groups in
`TauCeti.reductiveCommHopfAlgProperty.torus_of_geometricallySolvable` identifies it as a torus.
Centrality then follows from
`TauCeti.HopfIdeal.IsNormal.isCentral_of_multiplicativeType`.

These results supply the central torus in the reduction of a reductive group to its semisimple
quotient.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapters 12 and 19.
* A. Borel, *Linear Algebraic Groups*, §§11 and 14.
-/

public section

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

variable {k : Type u} [Field k]
variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- The solvable radical of a reductive affine group is a torus, in every characteristic and
including over fields over which the group does not split. -/
theorem torus_solvableRadical (hH : reductiveCommHopfAlgProperty k H) :
    torusCommHopfAlgProperty k (FiniteTypeCommHopfAlgCat.solvableRadical H) := by
  have hR := FiniteTypeCommHopfAlgCat.isSolvableRadicalCandidate_solvableRadicalDefiningIdeal H
  have hred := hH.quotient_of_isNormal
    (FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal H)
    hR.isNormal hR.smooth hR.geometricallyConnected
  exact hred.torus_of_geometricallySolvable hR.geometricallySolvable

/-- The solvable radical of a reductive affine group is contained in the scheme-theoretic center,
in every characteristic. The defining Hopf ideal represents the radical as a closed subgroup. -/
theorem isCentral_solvableRadicalDefiningIdeal (hH : reductiveCommHopfAlgProperty k H) :
    (FiniteTypeCommHopfAlgCat.solvableRadicalDefiningIdeal H).IsCentral := by
  let _ : Algebra.Smooth k H := hH.smooth
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  exact HopfIdeal.IsNormal.isCentral_of_multiplicativeType
    (FiniteTypeCommHopfAlgCat.isNormal_solvableRadicalDefiningIdeal H)
    hH.geometricallyConnected (hH.torus_solvableRadical.multiplicativeType k _)

end TauCeti.reductiveCommHopfAlgProperty
