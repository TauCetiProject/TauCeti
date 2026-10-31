/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Algebra.Support

/-!
# Topological support of a translate

The topological support of a right translate of a function on a topological group, next to
Mathlib's `mulTSupport_comp_eq_preimage`.

## Main results

* `TauCeti.mulTSupport_comp_div_right`: the topological multiplicative support of
  `fun y => f (y / x)` is the preimage of that of `f` under `(· / x)`, with additive version
  `TauCeti.tsupport_comp_sub_right`.
-/

public section

namespace TauCeti

variable {X G : Type*} [TopologicalSpace X] [Group X] [SeparatelyContinuousMul X] [One G]

/-- The topological multiplicative support of a right translate is the preimage of the
topological multiplicative support under the opposite translation. -/
@[to_additive /-- The topological support of a translate is the translated topological
support. -/]
theorem mulTSupport_comp_div_right (f : X → G) (x : X) :
    (mulTSupport fun y => f (y / x)) = (· / x) ⁻¹' mulTSupport f := by
  simpa [div_eq_mul_inv, Function.comp_def] using
    mulTSupport_comp_eq_preimage f (Homeomorph.mulRight x⁻¹)

end TauCeti
