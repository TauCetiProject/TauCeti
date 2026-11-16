/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Functions on an additive circle read on the real line

A function `g` on `AddCircle d` gives the function `t ↦ g t` on `ℝ` by composing with the quotient
map `ℝ → AddCircle d`. This file records that this function is `d`-periodic, and continuous when
`g` is.

## Main results

* `TauCeti.AddCircle.periodic_comp_coe`: `t ↦ g t` is `d`-periodic.
* `TauCeti.AddCircle.continuous_comp_coe`: `t ↦ g t` is continuous for a continuous `g`.
-/

public section

namespace TauCeti.AddCircle

variable {d : ℝ} {Y : Type*}

/-- A map on `AddCircle d`, regarded as a map on `ℝ`, is `d`-periodic. -/
theorem periodic_comp_coe (g : AddCircle d → Y) : Function.Periodic (fun t : ℝ => g t) d :=
  fun t => by simp only [AddCircle.coe_add_period]

/-- A continuous map on `AddCircle d`, regarded as a map on `ℝ`, is continuous. -/
theorem continuous_comp_coe [TopologicalSpace Y] (g : C(AddCircle d, Y)) :
    Continuous fun t : ℝ => g t :=
  g.continuous.comp (AddCircle.continuous_mk' d)

end TauCeti.AddCircle
