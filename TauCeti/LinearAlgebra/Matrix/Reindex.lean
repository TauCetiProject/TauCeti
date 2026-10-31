/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Algebra.Group.End

/-!
# Powers of matrix relabellings

A simultaneous permutation of rows and columns fixing a matrix continues to fix it
under every power. This applies in particular to automorphisms of an integral Gram matrix.
-/

public section

namespace Matrix

/-- Powers of a simultaneous row and column relabelling fixing a matrix still fix it. -/
theorem reindex_pow_eq_self {I J R : Type*} (B : Matrix I J R)
    (σ : Equiv.Perm I) (τ : Equiv.Perm J) (h : B.reindex σ τ = B) (n : ℕ) :
    B.reindex (σ ^ n) (τ ^ n) = B := by
  induction n with
  | zero => exact reindex_refl_refl B
  | succ n ih =>
    rw [pow_succ', pow_succ', Equiv.Perm.mul_def, Equiv.Perm.mul_def, ← reindex_trans]
    exact (congrArg (reindex σ τ) ih).trans h

end Matrix
