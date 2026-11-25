/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Group.PhaseShift.Basic
public import TauCeti.Analysis.Semigroups.Group.Unitary

/-!
# Phase shifts of unitary strongly continuous groups

A phase shift `U.phaseShift hU b` of a unitary C₀-group `U` remains unitary, because multiplying
every operator by the unimodular scalar `exp (-(b * t) * I)` preserves complex linearity and the
unitary growth bound `(0, 1)`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousGroup.IsUnitary.phaseShift`: a phase shift of a unitary
  C₀-group is unitary.
-/

public section

noncomputable section

namespace TauCeti.Semigroups.StronglyContinuousGroup

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A phase shift of a unitary C₀-group is again unitary. -/
theorem IsUnitary.phaseShift {U : StronglyContinuousGroup H} (hU : U.IsUnitary) (b : ℝ) :
    (U.phaseShift hU.isComplexLinear b).IsUnitary :=
  isUnitary_of_isComplexLinear_of_opNorm_le_one _
    (U.isComplexLinear_phaseShift hU.isComplexLinear b)
    ((U.phaseShift hU.isComplexLinear b).hasGrowthBound_zero_one_iff.mp
      (hU.hasGrowthBound_zero_one.phaseShift hU.isComplexLinear b))

end TauCeti.Semigroups.StronglyContinuousGroup

end
