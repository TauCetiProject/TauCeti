/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Instances.Matrix

/-!
# Topologies from matrix norms

This file exposes the topology underlying Mathlib's `L∞` operator norm on finite matrices. Since
matrix norms are scoped, consumers can select this topology locally without reconstructing the
instance projection chain.

Mathlib's `ContinuousStar` instance for matrices is stated for the entrywise topology, which is
the same topology but not the same instance, so continuity of the conjugate transpose has to be
restated for the topology selected here.

## Main definitions

* `Matrix.linftyOpTopologicalSpace`: the topology induced by the `L∞` operator norm.
* `Matrix.linftyOpContinuousStar`: conjugate transposition is continuous for that topology.
-/

public section

namespace Matrix

/-- The topology underlying the `L∞` operator norm on finite matrices. -/
protected noncomputable abbrev linftyOpTopologicalSpace
    (m n : Type*) [Fintype m] [Fintype n]
    (α : Type*) [NormedAddCommGroup α] : TopologicalSpace (Matrix m n α) :=
  (Matrix.linftyOpNormedAddCommGroup (m := m) (n := n) (α := α)).toPseudoMetricSpace
    |>.toUniformSpace |>.toTopologicalSpace

section

attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- Conjugate transposition is continuous for the topology of the `L∞` operator norm. -/
protected abbrev linftyOpContinuousStar (n : Type*) [Fintype n]
    (α : Type*) [NormedAddCommGroup α] [Star α] [ContinuousStar α] :
    ContinuousStar (Matrix n n α) where
  continuous_star := Continuous.matrix_conjTranspose continuous_id

end

end Matrix
