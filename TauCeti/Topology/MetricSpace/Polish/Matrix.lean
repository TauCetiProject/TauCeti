/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.MetricSpace.Polish

/-!
# Matrices over a Polish space

Mathlib gives `Matrix m n α` the product topology of `m → n → α`. A countable product of Polish
spaces is Polish, so matrices with countably many rows and columns over a Polish space form a
Polish space. Through `Units.instPolishSpace`, so does the general linear group `GL n R` of a
Polish topological ring `R` for finite `n`.
-/

public section

namespace TauCeti

/-- Matrices with countably many rows and columns over a Polish space form a Polish space. -/
instance {m n α : Type*} [Countable m] [Countable n] [TopologicalSpace α] [PolishSpace α] :
    PolishSpace (Matrix m n α) :=
  -- The topology of `Matrix m n α` is by definition the product topology on `m → n → α`.
  inferInstanceAs (PolishSpace (m → n → α))

end TauCeti
