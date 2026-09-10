/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Circle.EilenbergMacLane
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Basic
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Zero
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.HigherHomotopy

/-!
# Asphericity of real projective space

Real projective space `RPⁿ` is aspherical exactly when every homotopy group of its covering
sphere `Sⁿ` in dimension at least two vanishes, because the antipodal projection is a covering
map and so an isomorphism on all homotopy groups in dimensions at least two.

Two dimensions are settled outright. `RP⁰` is a point, hence a `K(1, 1)`; `RP¹` is a circle,
hence a `K(ℤ, 1)`, joining the circles and tori already recorded as Eilenberg--Mac Lane spaces.
For `2 ≤ n` the criterion below is as far as this library reaches: `RPⁿ` is a `K(ℤ/2, 1)`
precisely when every homotopy group of `Sⁿ` above dimension one vanishes, which is a statement
about `π_n(Sⁿ)` that is not proved here in either direction.

## Main declarations

* `TauCeti.RealProjectiveSpace.Zero.isEilenbergMacLaneSpaceOne`: `RP⁰` is a `K(1, 1)`.
* `TauCeti.RealProjectiveSpace.Line.isEilenbergMacLaneSpaceOne`: **`RP¹` is a `K(ℤ, 1)`**.
* `TauCeti.RealProjectiveSpace.isEilenbergMacLaneSpaceOne_iff_sphere`: for `2 ≤ n`, `RPⁿ` is a
  `K(ℤ/2, 1)` exactly when the higher homotopy groups of `Sⁿ` vanish.

The recognition criteria used here are in `TauCeti.AlgebraicTopology.EilenbergMacLane.Basic`
and `TauCeti.AlgebraicTopology.EilenbergMacLane.Covering`.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.B and Example 4.2.
-/

public section

open Metric
open scoped Topology Topology.Homotopy Real

namespace TauCeti

namespace RealProjectiveSpace

namespace Zero

/-- Zero-dimensional real projective space is aspherical: it is a single point. -/
theorem isAspherical (x : RealProjectiveSpace 0) : IsAspherical (RealProjectiveSpace 0) x :=
  IsAspherical.mk inferInstance fun _ ↦ inferInstance

/-- **`RP⁰` is an Eilenberg--Mac Lane space `K(1, 1)`** for the trivial group. -/
theorem isEilenbergMacLaneSpaceOne (x : RealProjectiveSpace 0) :
    IsEilenbergMacLaneSpaceOne PUnit (RealProjectiveSpace 0) x :=
  IsEilenbergMacLaneSpaceOne.mk (isAspherical x) ⟨fundamentalGroupMulEquiv x⟩

end Zero

namespace Line

/-- The real projective line is aspherical, transported from the additive circle `ℝ ⧸ 2πℤ`
along `TauCeti.RealProjectiveSpace.Line.homeomorphAddCircle`. -/
theorem isAspherical (x : RealProjectiveSpace 1) : IsAspherical (RealProjectiveSpace 1) x :=
  (AddCircle.isAspherical (2 * π) (homeomorphAddCircle x)).of_homeomorph
    homeomorphAddCircle.symm (homeomorphAddCircle.symm_apply_apply x)

/-- **`RP¹` is an Eilenberg--Mac Lane space `K(ℤ, 1)`**, transported from the additive circle
`ℝ ⧸ 2πℤ` along `TauCeti.RealProjectiveSpace.Line.homeomorphAddCircle`. -/
theorem isEilenbergMacLaneSpaceOne (x : RealProjectiveSpace 1) :
    IsEilenbergMacLaneSpaceOne (Multiplicative ℤ) (RealProjectiveSpace 1) x :=
  (AddCircle.isEilenbergMacLaneSpaceOne (2 * π) Real.two_pi_pos.ne'
    (homeomorphAddCircle x)).of_homeomorph homeomorphAddCircle.symm
    (homeomorphAddCircle.symm_apply_apply x)

end Line

/-- **For `2 ≤ n`, real projective space is a `K(ℤ/2, 1)` exactly when every homotopy group of
its covering sphere in dimension at least two vanishes.** The fundamental group is `ℤˣ` in
this range, so the only remaining condition is asphericity, and that transfers along the
antipodal cover. Neither side is decided here: it amounts to knowing `π_n(Sⁿ)`, which this
library does not compute. -/
theorem isEilenbergMacLaneSpaceOne_iff_sphere {n : ℕ} (hn : 2 ≤ n)
    (x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) (y : RealProjectiveSpace n) :
    IsEilenbergMacLaneSpaceOne ℤˣ (RealProjectiveSpace n) y ↔
      ∀ k : ℕ, Subsingleton (π_ (k + 2) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) x) := by
  refine ⟨fun h ↦ (isAspherical_iff_sphere (by omega) x y).mp h.isAspherical, fun h ↦ ?_⟩
  exact IsEilenbergMacLaneSpaceOne.mk ((isAspherical_iff_sphere (by omega) x y).mpr h)
    ⟨fundamentalGroupMulEquivAt n hn y⟩

end RealProjectiveSpace

end TauCeti
