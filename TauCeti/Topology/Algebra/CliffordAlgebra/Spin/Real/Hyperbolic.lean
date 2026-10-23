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

The image of the real Spin group of the hyperbolic plane is the identity component of its
proper orthogonal group. Thus the Spin action distinguishes the component containing the identity
from the remaining proper orthogonal transformations. This identifies the indefinite-signature
Spin image with its natural connected target in the split real two-dimensional case.
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
