/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
import TauCeti.AlgebraicTopology.UniversalCover.Circle.NotSimplyConnected
import TauCeti.Topology.JordanCurve.Basic

/-!
# The circle does not fill a sphere of dimension at least two

A continuous injection of the unit circle of `ℂ` into the unit sphere of a real normed space of
rank greater than two is not surjective
(`TauCeti.not_surjective_of_continuous_injective_circle_sphere`). Being a continuous bijection from
a compact space to a Hausdorff space, a surjective one would be a homeomorphism, but the sphere is
simply connected (`TauCeti.simplyConnectedSpace_sphere`) and the circle is not
(`Circle.not_simplyConnectedSpace`). So such a circle always misses a point of the sphere; for
the 2-sphere this is the point from which a Jordan curve is projected stereographically into the
plane.
-/

public section

open Function Metric

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A continuous injection of the unit circle of `ℂ` into the unit sphere of a real normed space
of rank greater than two is not surjective. -/
theorem not_surjective_of_continuous_injective_circle_sphere (h : 2 < Module.rank ℝ E)
    {γ : sphere (0 : ℂ) 1 → sphere (0 : E) 1} (hγ : Continuous γ) (hγi : Injective γ) :
    ¬ Surjective γ := by
  intro hsurj
  have : SimplyConnectedSpace (sphere (0 : E) 1) := simplyConnectedSpace_sphere h 0 zero_le_one
  let e : sphere (0 : ℂ) 1 ≃ₜ sphere (0 : E) 1 :=
    Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective γ ⟨hγi, hsurj⟩) hγ
  have : SimplyConnectedSpace (sphere (0 : ℂ) 1) := e.toHomotopyEquiv.simplyConnectedSpace
  exact Circle.not_simplyConnectedSpace
    (sphereCircleHomeomorph 0 one_pos).symm.toHomotopyEquiv.simplyConnectedSpace

end TauCeti
