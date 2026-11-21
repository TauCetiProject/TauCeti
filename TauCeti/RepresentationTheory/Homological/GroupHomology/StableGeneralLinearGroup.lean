/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.StabilizationDiagram
public import TauCeti.RepresentationTheory.Homological.GroupHomology.FilteredColimit

/-!
# Homology of the stable general linear group

The inclusions of the finite general linear groups identify the homology of the stable group
with the colimit of the finite-rank homology groups under block-diagonal stabilization. This
is the colimit comparison used in van der Kallen, *Homology stability for linear groups*, §4.6.
It holds with coefficients in any representation of the stable group, restricted to the stages.
-/

public noncomputable section

open CategoryTheory.Limits

namespace TauCeti.StableGeneralLinearGroup

/-- With coefficients restricted from a representation `A` of the stable group, its homology in
 degree `m` is the colimit of the homology of the finite general linear groups. In particular,
 `A = Rep.trivial ℤ (StableGeneralLinearGroup R) ℤ` gives the integral comparison. -/
def isColimitGroupHomology (R : Type) [Ring R] {k : Type} [CommRing k]
    (A : Rep k (StableGeneralLinearGroup R)) (m : ℕ) :
    IsColimit (A.groupHomologyCocone (c := stabilizationCocone R) m) :=
  Rep.isColimitGroupHomologyCocone (c := stabilizationCocone R) A m
    (of_injective (A := R)) (exists_of (A := R))

end TauCeti.StableGeneralLinearGroup

end
