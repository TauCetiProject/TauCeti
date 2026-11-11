/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.UniformSpace.Matrix

/-!
# Topologies from matrix norms

This file exposes the topology underlying Mathlib's `L∞` operator norm on finite matrices. Since
matrix norms are scoped, consumers can select this topology locally without reconstructing the
instance projection chain.

Mathlib's `ContinuousStar` instance for matrices is stated for the entrywise topology. The `L∞`
operator topology agrees with it definitionally (`Matrix.linftyOpTopologicalSpace_eq`), but it is
not syntactically the same instance, so continuity of the conjugate transpose is transported along
that equality to the topology selected here.

The operator uniformity also agrees with the complete product uniformity when the entries are
complete. Its completeness instance is activated by `Matrix.Norms.Operator`, alongside the norm.

## Main declarations

* `Matrix.linftyOpTopologicalSpace`: the topology induced by the `L∞` operator norm.
* `Matrix.linftyOpTopologicalSpace_eq`: that topology is the entrywise topology on matrices.
* `Matrix.linftyOpContinuousStar`: conjugate transposition is continuous for that topology.
* `Matrix.linftyOpCompleteSpace`: completeness for the operator uniformity, scoped with the norm.
-/

public section

namespace Matrix

/-- The topology underlying the `L∞` operator norm on finite matrices. -/
protected noncomputable abbrev linftyOpTopologicalSpace
    (m n : Type*) [Fintype m] [Fintype n]
    (α : Type*) [SeminormedAddCommGroup α] : TopologicalSpace (Matrix m n α) :=
  (Matrix.linftyOpSeminormedAddCommGroup (m := m) (n := n) (α := α)).toPseudoMetricSpace
    |>.toUniformSpace |>.toTopologicalSpace

/-- The topology of the `L∞` operator norm is the entrywise topology on matrices.

This holds by `rfl` by design of Mathlib's `PiLp.pseudoMetricSpaceToPi`, which underlies
`Matrix.linftyOpSeminormedAddCommGroup`: it pulls back the `L^p` distance along `WithLp.toLp`
and then replaces the uniformity by the product uniformity, so the induced topology is the
product topology, which is Mathlib's topology on matrices. -/
theorem linftyOpTopologicalSpace_eq (m n : Type*) [Fintype m] [Fintype n]
    (α : Type*) [SeminormedAddCommGroup α] :
    Matrix.linftyOpTopologicalSpace m n α = (inferInstance : TopologicalSpace (Matrix m n α)) :=
  rfl

/-- Finite matrices over a complete normed additive group are complete for the
operator uniformity. -/
protected theorem linftyOpCompleteSpace {R p q : Type*} [NormedAddCommGroup R]
    [CompleteSpace R] [Fintype p] [Fintype q] :
    @CompleteSpace (Matrix p q R)
      (Matrix.linftyOpNormedAddCommGroup (m := p) (n := q) (α := R)).toUniformSpace :=
  inferInstanceAs (CompleteSpace (p → q → R))

namespace Norms.Operator
attribute [scoped instance] Matrix.linftyOpCompleteSpace
end Norms.Operator

section

attribute [local instance] Matrix.linftyOpTopologicalSpace

/-- Conjugate transposition is continuous for the topology of the `L∞` operator norm. -/
protected theorem linftyOpContinuousStar (n : Type*) [Fintype n]
    (α : Type*) [SeminormedAddCommGroup α] [Star α] [ContinuousStar α] :
    ContinuousStar (Matrix n n α) :=
  linftyOpTopologicalSpace_eq n n α ▸ inferInstance

end

end Matrix
