/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Pointwise evaluation of `Ring.inverse` on continuous maps

When a bundled continuous map `f : C(X, M₀)` into a topological monoid with zero is a unit,
evaluating `f⁻¹ʳ` at `x : X` agrees with `(f x)⁻¹ʳ` (`ContinuousMap.ringInverse_apply`). Without
`IsUnit f`, `f⁻¹ʳ` vanishes globally even at points where `f x` is individually invertible.
-/

public section

open scoped Ring

namespace ContinuousMap

/-- Evaluating `f⁻¹ʳ` at a point `x` gives `(f x)⁻¹ʳ` whenever `f : C(X, M₀)` is a unit. -/
theorem ringInverse_apply {X M₀ : Type*} [TopologicalSpace X] [MonoidWithZero M₀]
    [TopologicalSpace M₀] [ContinuousMul M₀] {f : C(X, M₀)} (hf : IsUnit f) (x : X) :
    f⁻¹ʳ x = (f x)⁻¹ʳ :=
  hf.map_ringInverse ((Pi.evalMonoidHom (fun _ ↦ M₀) x).comp coeFnMonoidHom)

end ContinuousMap
