/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Continuous maps from group quotients

This file records continuity results for maps out of group quotients that do not require
transitivity of an action.

## Main results

* `TauCeti.continuous_ofQuotientStabilizer` proves continuity of the orbit map descended to a
  stabilizer quotient when the corresponding orbit map is continuous.
-/

public section

open MulAction

namespace TauCeti

variable (G : Type*) {X : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace X]
  [MulAction G X]

/-- The orbit map descended to the stabilizer quotient is continuous when the orbit map is. -/
@[fun_prop]
theorem continuous_ofQuotientStabilizer (b : X) (hb : Continuous fun g : G => g • b) :
    Continuous (ofQuotientStabilizer G b) := by
  unfold ofQuotientStabilizer
  exact hb.quotient_liftOn' _

end TauCeti
