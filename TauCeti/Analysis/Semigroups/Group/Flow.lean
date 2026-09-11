/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Dynamics.Flow
public import TauCeti.Analysis.Semigroups.Group.Basic

/-!
# Linear flows from strongly continuous groups

A strongly continuous one-parameter group of bounded linear operators acts continuously on its
underlying normed space, and hence determines a `Flow`. This file supplies that bridge between the
operator-valued semigroup API and the point-valued dynamical API.

The construction forgets only linear structure: its time maps are the operators of the group.
Consequently it commutes with time reversal, and its orbits are definitionally the group orbits.

## Main declarations

* `TauCeti.Semigroups.StronglyContinuousGroup.toFlow`: the flow underlying a strongly continuous
  group.
* `TauCeti.Semigroups.StronglyContinuousGroup.toFlow_reflect`: time reversal commutes with passage
  to the underlying flow.
-/

public section

noncomputable section

namespace TauCeti.Semigroups

namespace StronglyContinuousGroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- The continuous flow on `X` underlying a strongly continuous one-parameter group of bounded
linear operators. -/
def toFlow (U : StronglyContinuousGroup X) : _root_.Flow ℝ X where
  toFun t x := U t x
  cont' := by
    rw [continuous_iff_continuousAt]
    intro p
    exact U.tendsto_apply continuousAt_fst continuousAt_snd
  map_add' s t x := U.map_add_apply s t x
  map_zero' x := U.map_zero_apply x

@[simp]
theorem toFlow_apply (U : StronglyContinuousGroup X) (t : ℝ) (x : X) :
    U.toFlow t x = U t x := by
  rw [toFlow]

/-- Passing to the underlying flow commutes with reversing time. -/
@[simp]
theorem toFlow_reflect (U : StronglyContinuousGroup X) :
    U.reflect.toFlow = U.toFlow.reverse := by
  apply _root_.Flow.ext
  intro t x
  rw [toFlow_apply, _root_.Flow.reverse_apply, toFlow_apply, reflect_apply]

end StronglyContinuousGroup

end TauCeti.Semigroups

end
