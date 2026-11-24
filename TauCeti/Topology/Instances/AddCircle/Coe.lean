/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.Topology.ContinuousMap.Defs
public import Mathlib.Topology.Instances.AddCircle.Defs

/-!
# Functions on an additive circle read on the underlying group

A function `g` on `AddCircle p` gives the function `t ↦ g t` on `𝕜` by composing with the quotient
map `𝕜 → AddCircle p`. This file records that this function is `p`-periodic, and continuous when
`g` is, and that continuous maps on `AddCircle p` agreeing at every element of `𝕜` are equal.

## Main results

* `TauCeti.AddCircle.periodic_comp_coe`: `t ↦ g t` is `p`-periodic.
* `TauCeti.AddCircle.continuous_comp_coe`: `t ↦ g t` is continuous for a continuous `g`.
* `TauCeti.AddCircle.continuousMap_ext_coe`: continuous maps on `AddCircle p` are determined by
  their values at elements of `𝕜`.
-/

public section

namespace TauCeti.AddCircle

variable {𝕜 : Type*} [AddCommGroup 𝕜] {p : 𝕜} {Y : Type*}

/-- A map on `AddCircle p`, regarded as a map on `𝕜`, is `p`-periodic. -/
theorem periodic_comp_coe (g : AddCircle p → Y) : Function.Periodic (fun t : 𝕜 => g t) p :=
  fun t => by simp only [AddCircle.coe_add_period]

variable [TopologicalSpace 𝕜] [TopologicalSpace Y]

/-- A continuous map on `AddCircle p`, regarded as a map on `𝕜`, is continuous. -/
theorem continuous_comp_coe (g : C(AddCircle p, Y)) : Continuous fun t : 𝕜 => g t :=
  g.continuous.comp (AddCircle.continuous_mk' p)

/-- Two continuous maps on `AddCircle p` are equal if they agree at every element of `𝕜`. -/
theorem continuousMap_ext_coe {g g' : C(AddCircle p, Y)} (h : ∀ t : 𝕜, g t = g' t) : g = g' :=
  ContinuousMap.ext <| QuotientAddGroup.mk_surjective.forall.2 h

end TauCeti.AddCircle
