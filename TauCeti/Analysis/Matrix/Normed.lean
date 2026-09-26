/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed

/-!
# Topologies from matrix norms

This file exposes the topology underlying Mathlib's `L∞` operator norm on finite matrices. Since
matrix norms are scoped, consumers can select this topology locally without reconstructing the
instance projection chain.

## Main definitions

* `Matrix.linftyOpTopologicalSpace`: the topology induced by the `L∞` operator norm.
-/

public section

namespace Matrix

/-- The topology underlying the `L∞` operator norm on finite matrices. -/
protected noncomputable abbrev linftyOpTopologicalSpace
    (m n : Type*) [Fintype m] [Fintype n]
    (α : Type*) [NormedAddCommGroup α] : TopologicalSpace (Matrix m n α) :=
  (Matrix.linftyOpNormedAddCommGroup (m := m) (n := n) (α := α)).toPseudoMetricSpace
    |>.toUniformSpace |>.toTopologicalSpace

end Matrix
