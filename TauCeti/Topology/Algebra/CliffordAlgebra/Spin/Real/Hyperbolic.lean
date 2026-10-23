/-
Copyright (c) 2026 Tau Ceti Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.SquareClassGroup.Real
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.Hyperbolic
public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Hyperbolic

/-!
# The real Spin image of the hyperbolic plane

The real Spin image of the hyperbolic plane is the identity component of its proper orthogonal
group. The proof uses the identity-component result for the real hyperbolic orthogonal group,
identifies the Spin image with square-unit parameters through the general spinor-norm calculation,
and uses that a real unit is a square exactly when it is positive.
-/

public section

open Set
open TauCeti.QuadraticMap

namespace TauCeti

/-- The real Spin image of the hyperbolic plane is the identity component of its proper
orthogonal group. -/
theorem range_spinToSpecialOrthogonal_hyperbolicPlane_real :
    (CliffordAlgebra.spinToSpecialOrthogonal (hyperbolicPlane ℝ)).range =
      Subgroup.connectedComponentOfOne (specialOrthogonalGroup (hyperbolicPlane ℝ)) := by
  rw [CliffordAlgebra.range_spinToSpecialOrthogonal_hyperbolicPlane,
    connectedComponentOfOne_specialOrthogonalGroup_hyperbolicPlane_real,
    Units.square_eq_posSubgroup_real]

end TauCeti
