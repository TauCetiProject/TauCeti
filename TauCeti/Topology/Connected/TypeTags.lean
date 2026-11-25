/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Constructions

/-!
# Preconnectedness through the type tags

The topologies of `Additive X` and `Multiplicative X` are that of `X`, so they are preconnected
when `X` is. These instances let a preconnected additive group, such as a torus `(ℝ / 2πℤ)^ι`,
act through its multiplicative copy in the Lie group results, which are stated for multiplicative
groups. They mirror Mathlib's `CompactSpace` and `TotallyDisconnectedSpace` instances on the type
tags.
-/

public section

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

instance [PreconnectedSpace X] : PreconnectedSpace (Additive X) := ‹PreconnectedSpace X›

instance [PreconnectedSpace X] : PreconnectedSpace (Multiplicative X) := ‹PreconnectedSpace X›

end TauCeti
