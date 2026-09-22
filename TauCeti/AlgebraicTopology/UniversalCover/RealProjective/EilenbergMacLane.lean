/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.EilenbergMacLane.Covering
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.FundamentalGroup.Line
public import TauCeti.AlgebraicTopology.UniversalCover.RealProjective.HigherHomotopy

/-!
# Asphericity of real projective space

Real projective space is path connected, so it is aspherical exactly when all its homotopy
groups in dimensions at least two vanish. Those groups are the homotopy groups of the covering
sphere, so `RPⁿ` is aspherical exactly when `Sⁿ` is weakly contractible in dimensions at least
two.

For `n = 1` this happens: the projective line is homeomorphic to the circle, so it is aspherical
and, its fundamental group being infinite cyclic, it is a `K(ℤ, 1)`. This adds the projective
line to the circles and tori already recorded as Eilenberg--Mac Lane spaces. For `n ≥ 2` the
criterion turns on the higher homotopy groups of `Sⁿ`, whose computation rests on a degree or
Hurewicz argument.

## Main declarations

* `TauCeti.RealProjectiveSpace.isAspherical_iff`: **`RPⁿ` is aspherical exactly when the higher
  homotopy groups of the covering sphere vanish.**
* `TauCeti.RealProjectiveSpace.Line.isAspherical`: **the real projective line is aspherical.**
* `TauCeti.RealProjectiveSpace.Line.isEilenbergMacLaneSpaceOne`: **the real projective line is a
  `K(ℤ, 1)`**, with `ℤ` written multiplicatively to match the fundamental group.

## References

* A. Hatcher, *Algebraic Topology*, Section 1.B.
-/

public section

namespace TauCeti

namespace RealProjectiveSpace

open Metric
open scoped Topology Topology.Homotopy

/-- **Real projective space is aspherical exactly when its covering sphere has vanishing
homotopy groups in dimensions at least two.** The two spaces have the same homotopy groups in
those dimensions, and `RPⁿ` is path connected for every `n`. -/
theorem isAspherical_iff (n : ℕ) (y : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    IsAspherical (RealProjectiveSpace n) (mk n y) ↔
      ∀ k : ℕ, Subsingleton (π_ (k + 2) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) y) :=
  ⟨fun h k ↦ ((isCoveringMap_mk n).subsingleton_homotopyGroup_iff (e := y) rfl k).mpr
      (h.subsingleton_homotopyGroup k),
    fun h ↦ IsAspherical.mk inferInstance fun k ↦
      ((isCoveringMap_mk n).subsingleton_homotopyGroup_iff (e := y) rfl k).mp (h k)⟩

namespace Line

/-- **The real projective line is aspherical.** -/
theorem isAspherical (x : RealProjectiveSpace 1) :
    IsAspherical (RealProjectiveSpace 1) x :=
  IsAspherical.mk inferInstance fun _ ↦ inferInstance

/-- **The real projective line is an Eilenberg--Mac Lane space of type `K(ℤ, 1)`**, with `ℤ`
written multiplicatively to match the fundamental group. -/
theorem isEilenbergMacLaneSpaceOne (x : RealProjectiveSpace 1) :
    IsEilenbergMacLaneSpaceOne (Multiplicative ℤ) (RealProjectiveSpace 1) x :=
  IsEilenbergMacLaneSpaceOne.mk (isAspherical x) ⟨fundamentalGroupMulEquiv x⟩

end Line

end RealProjectiveSpace

end TauCeti
