/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Angle
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Between

/-!
# The angle at a point between the geodesics towards two other points

`UpperHalfPlane.interiorAngle A B C` is the angle at `A` between the geodesics from `A` to `B` and
from `A` to `C`: the angle `geodesicAngle` between the geodesic lines `geodesicBetween A B` and
`geodesicBetween A C`. It is symmetric in `B` and `C` (`UpperHalfPlane.interiorAngle_comm`), lies
in `[0, π]` (`UpperHalfPlane.interiorAngle_nonneg`, `UpperHalfPlane.interiorAngle_le_pi`), and is
invariant under `PSL(2, ℝ)` when `A ≠ B` and `A ≠ C` (`interiorAngle_smul`). It is the interior
angle of hyperbolic triangles and polygons.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup UpperHalfPlane
open scoped MatrixGroups Real

namespace UpperHalfPlane

open TauCeti.UpperHalfPlane

/-- The interior angle at `A` between the directions to `B` and to `C`: the angle between the
geodesics from `A` to `B` and from `A` to `C`. -/
def interiorAngle (A B C : ℍ) : ℝ :=
  geodesicAngle (geodesicBetween A B) (geodesicBetween A C)

-- The body of `interiorAngle` is not `@[expose]`d, so downstream modules rewrite with this.
/-- `interiorAngle` is the angle between the geodesics from `A` to `B` and from `A` to `C`. -/
theorem interiorAngle_def (A B C : ℍ) :
    interiorAngle A B C = geodesicAngle (geodesicBetween A B) (geodesicBetween A C) := by rfl

/-- The interior angle at `A` does not depend on the order of the other two vertices. -/
theorem interiorAngle_comm (A B C : ℍ) : interiorAngle A C B = interiorAngle A B C :=
  geodesicAngle_comm _ _

/-- Interior angles are nonnegative. -/
theorem interiorAngle_nonneg (A B C : ℍ) : 0 ≤ interiorAngle A B C :=
  geodesicAngle_nonneg _ _

/-- Interior angles are at most `π`. -/
theorem interiorAngle_le_pi (A B C : ℍ) : interiorAngle A B C ≤ π :=
  geodesicAngle_le_pi _ _

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-- Interior angles at `A` are invariant under the action, for `A ≠ B` and `A ≠ C`. -/
theorem interiorAngle_smul (h : PSL(2, ℝ)) {A B C : ℍ} (hAB : A ≠ B) (hAC : A ≠ C) :
    interiorAngle (h • A) (h • B) (h • C) = interiorAngle A B C := by
  rw [interiorAngle_def, interiorAngle_def, geodesicBetween_smul h hAB, geodesicBetween_smul h hAC,
    geodesicAngle_mul _ _ _ (by rw [geodesicLine_geodesicBetween_zero,
      geodesicLine_geodesicBetween_zero])]

end TauCeti.UpperHalfPlane
