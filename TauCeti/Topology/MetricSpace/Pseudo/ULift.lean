/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions

/-!
# Closed balls in a universe lift

The distance on `ULift X` is the distance of the underlying points, so `Homeomorph.ulift`
restricts to a homeomorphism from the closed ball of `ULift X` about `x` onto the closed ball of
`X` about `x.down` (`Homeomorph.uliftClosedBall`). It moves a disk such as the closed unit ball
of `Fin n → ℝ` to a higher universe without changing it as a space.
-/

public section

open Metric

namespace Homeomorph

variable {X : Type*} [PseudoMetricSpace X]

/-- The closed ball of `ULift X` about `x` is homeomorphic to the closed ball of `X` about
`x.down` of the same radius, by forgetting the universe lift. -/
def uliftClosedBall (x : ULift X) (r : ℝ) : closedBall x r ≃ₜ closedBall x.down r :=
  Homeomorph.ulift.subtype fun _ ↦ Iff.rfl

@[simp]
lemma coe_uliftClosedBall_apply (x : ULift X) (r : ℝ) (y : closedBall x r) :
    (uliftClosedBall x r y : X) = (y : ULift X).down :=
  (rfl)

@[simp]
lemma coe_uliftClosedBall_symm_apply (x : ULift X) (r : ℝ) (y : closedBall x.down r) :
    ((uliftClosedBall x r).symm y : ULift X) = ULift.up (y : X) :=
  (rfl)

end Homeomorph
