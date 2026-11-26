/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.ClosedCylinder
public import TauCeti.Dynamics.Billiard.Measure
public import TauCeti.Dynamics.NonwanderingSet
import TauCeti.MeasureTheory.Measure.Subtype

/-!
# The billiard map has no wandering points

Let `χ` be a twice differentiable arclength parametrization of the boundary of a strictly convex
billiard table (`TauCeti.StrictConvexBilliardTable`). The billiard map `T` of the open cylinder
`AddCircle L × (-1, 1)` preserves a finite area of full support
(`TauCeti.StrictConvexBilliardTable.measurePreserving_billiardMap`), so by Poincaré recurrence
(`MeasureTheory.MeasurePreserving.nonwanderingSet_eq_univ`) every state is non-wandering
(`TauCeti.StrictConvexBilliardTable.nonwanderingSet_billiardMap`).

The extension `T'` of `T` to the closed cylinder `AddCircle L × [-1, 1]`
(`TauCeti.StrictConvexBilliardTable.closedBilliardMap`) restricts to `T` on the open cylinder,
which is dense in the closed one, so every point of the closed cylinder is non-wandering for `T'`
(`TauCeti.StrictConvexBilliardTable.nonwanderingSet_closedBilliardMap`, from
`Function.Semiconj.nonwanderingSet_eq_univ`); the points of the two boundary circles are moreover
fixed by `T'`.

Both results assume that `χ` is twice differentiable, because the invariance of the area is only
available in that case; tables whose boundary is merely `C¹` are not covered here.
-/

public section

open Set Module

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2)]

namespace StrictConvexBilliardTable

variable {o : Orientation ℝ E (Fin 2)} {χ : StrictConvexBilliardTable o}

/-- **Every state of a convex billiard is non-wandering.** If the arclength parametrization `χ`
is twice differentiable, the non-wandering set of the billiard map of the open cylinder is the
whole cylinder. -/
theorem nonwanderingSet_billiardMap (hχ : Differentiable ℝ (deriv χ)) :
    nonwanderingSet χ.billiardMap = univ :=
  (measurePreserving_billiardMap hχ).nonwanderingSet_eq_univ

/-- **Every point of the closed cylinder is non-wandering.** If the arclength parametrization `χ`
is twice differentiable, the non-wandering set of the billiard map extended to the closed cylinder
is the whole closed cylinder. -/
theorem nonwanderingSet_closedBilliardMap (hχ : Differentiable ℝ (deriv χ)) :
    nonwanderingSet χ.closedBilliardMap = univ :=
  χ.semiconj_cylinderInclusion.nonwanderingSet_eq_univ χ.continuous_cylinderInclusion
    χ.denseRange_cylinderInclusion (nonwanderingSet_billiardMap hχ)

end StrictConvexBilliardTable

end TauCeti
