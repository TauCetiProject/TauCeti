/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.Topology.Instances.Matrix

/-!
# Paths of symmetric matrices

The catenation and the reversal of paths of symmetric matrices consist of symmetric matrices
(`Matrix.isSymm_path_trans`, `Matrix.isSymm_path_symm`), and so does the straight-line path between
two symmetric matrices with entries in a real topological vector space
(`Matrix.isSymm_segment`).
-/

public section

open scoped unitInterval

namespace Matrix

variable {n : Type*}

/-- The catenation of two paths of symmetric matrices consists of symmetric matrices. -/
theorem isSymm_path_trans {α : Type*} [TopologicalSpace α] {S₀ S₁ S₂ : Matrix n n α}
    {S : Path S₀ S₁} {T : Path S₁ S₂} (hS : ∀ t, (S t).IsSymm) (hT : ∀ t, (T t).IsSymm)
    (t : I) : ((S.trans T) t).IsSymm := by
  rw [Path.trans_apply]
  split_ifs
  exacts [hS _, hT _]

/-- The reversal of a path of symmetric matrices consists of symmetric matrices. -/
theorem isSymm_path_symm {α : Type*} [TopologicalSpace α] {S₀ S₁ : Matrix n n α}
    {S : Path S₀ S₁} (hS : ∀ t, (S t).IsSymm) (t : I) : (S.symm t).IsSymm := by
  rw [Path.symm_apply]
  exact hS _

/-- The matrices along the segment between two symmetric matrices are symmetric. -/
theorem isSymm_segment {α : Type*} [AddCommGroup α] [Module ℝ α] [TopologicalSpace α]
    [ContinuousAdd α] [ContinuousSMul ℝ α] {S₀ S₁ : Matrix n n α} (hS₀ : S₀.IsSymm)
    (hS₁ : S₁.IsSymm) (t : I) : (Path.segment S₀ S₁ t).IsSymm := by
  rw [Path.segment_apply, AffineMap.lineMap_apply_module]
  exact (hS₀.smul _).add (hS₁.smul _)

end Matrix
