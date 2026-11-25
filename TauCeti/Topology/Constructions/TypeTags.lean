/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Constructions

/-!
# Pointwise continuity through the additive type tag

The topology of `Additive X` is that of `X`, and `Additive.ofMul`, `Additive.toMul` are the
identity on points. So a function is continuous at a point exactly when it is after its values
are read additively (`TauCeti.continuousAt_ofMul_iff`) or read back multiplicatively
(`TauCeti.continuousAt_toMul_iff`). These are the pointwise counterparts of Mathlib's
`continuous_ofMul` and `continuous_toMul`, needed when a cochain with multiplicative values is
only continuous at some points.
-/

public section

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

/-- Continuity at a point is unchanged by reading the values additively. -/
@[simp]
theorem continuousAt_ofMul_iff {f : X → Y} :
    ContinuousAt (fun y => Additive.ofMul (f y)) x ↔ ContinuousAt f x :=
  ⟨fun h => continuous_toMul.continuousAt.comp h, fun h => continuous_ofMul.continuousAt.comp h⟩

/-- Continuity at a point is unchanged by reading additive values back multiplicatively. -/
@[simp]
theorem continuousAt_toMul_iff {f : X → Additive Y} :
    ContinuousAt (fun y => (f y).toMul) x ↔ ContinuousAt f x :=
  ⟨fun h => continuous_ofMul.continuousAt.comp h, fun h => continuous_toMul.continuousAt.comp h⟩

end TauCeti
