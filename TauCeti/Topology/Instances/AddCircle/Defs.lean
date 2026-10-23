/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.AddCircle.Defs
public import Mathlib.Order.Interval.Set.Infinite

/-!
# Basic facts about the additive circle

For a positive period `p` in a densely ordered archimedean group, `AddCircle p` is in bijection
with the half-open interval `[0, p)` (`AddCircle.equivIco`), which is infinite. In particular the
unit circle `UnitAddCircle` is infinite.

A continuous periodic function descends to a continuous function on the quotient by its period,
such as `AddCircle p`; for instance `Real.cos_periodic.lift` is the continuous cosine of a point
of `AddCircle (2 * π)`.

## Main results

* `AddCircle.infinite`: `AddCircle p` is infinite, as an instance.
* `Function.Periodic.continuous_lift`: the descent of a continuous periodic function is
  continuous.
-/

public section

namespace AddCircle

variable {𝕜 : Type*} [AddCommGroup 𝕜] [LinearOrder 𝕜] [IsOrderedAddMonoid 𝕜] [Archimedean 𝕜]
  [DenselyOrdered 𝕜] {p : 𝕜} [Fact (0 < p)]

/-- The additive circle of a positive period in a densely ordered archimedean group is infinite,
being in bijection with the interval `[0, p)`. -/
instance infinite : Infinite (AddCircle p) :=
  (equivIco p 0).infinite_iff.2 (Set.Ico_infinite (by simpa using Fact.out)).to_subtype

end AddCircle

namespace Function.Periodic

variable {α β : Type*} [AddGroup α] [TopologicalSpace α] [TopologicalSpace β] {f : α → β} {c : α}

/-- A continuous `c`-periodic function descends to a continuous function on the quotient
`α ⧸ AddSubgroup.zmultiples c`, for instance on `AddCircle c`. -/
theorem continuous_lift (h : Periodic f c) (hf : Continuous f) : Continuous h.lift :=
  hf.quotient_liftOn' _

end Function.Periodic
