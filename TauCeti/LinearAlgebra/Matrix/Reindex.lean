/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Algebra.Group.End
public import Mathlib.LinearAlgebra.Matrix.Notation

import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Relabellings of matrices

A simultaneous permutation of rows and columns fixing a matrix continues to fix it
under every power. This applies in particular to automorphisms of an integral Gram matrix.
A matrix with constant diagonal that is related to a `2 × 2` matrix by a relabelling of its index
type is determined by the two off-diagonal entries at the two relabelled nodes.

## Main results

* `Matrix.reindex_pow_eq_self`: powers of a relabelling fixing a matrix fix it.
* `Matrix.forall_eq_of_apply_offDiag`, `Matrix.forall_eq_of_apply_offDiag_two`: entrywise
  agreement with a `2 × 2` matrix through a relabelling, from the two off-diagonal entries.
-/

public section

open scoped Matrix

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

/-- **Entrywise agreement with a two-node matrix is four equations, and two of them are
automatic.** If `A` and `C` both have constant diagonal `d`, only the two off-diagonal entries have
to be matched by hand. -/
theorem forall_eq_of_apply_offDiag {B R : Type*} {A : Matrix B B R} {C : Matrix (Fin 2) (Fin 2) R}
    {d : R} (hA : ∀ i, A i i = d) (e : B ≃ Fin 2) (hC : ∀ i, C i i = d)
    (h01 : A (e.symm 0) (e.symm 1) = C 0 1) (h10 : A (e.symm 1) (e.symm 0) = C 1 0) (i j : B) :
    A i j = C (e i) (e j) := by
  suffices key : ∀ i j : Fin 2, A (e.symm i) (e.symm j) = C i j by simpa using key (e i) (e j)
  intro i j
  fin_cases i <;> fin_cases j
  · simpa using (hA _).trans (hC 0).symm
  · simpa using h01
  · simpa using h10
  · simpa using (hA _).trans (hC 1).symm

/-- **Entrywise agreement with a standard two-node matrix.** Given a relabelling `e : B ≃ Fin 2`
and the two off-diagonal entries `a`, `b` of `A` at the nodes `e.symm 0`, `e.symm 1`, a matrix `A`
with constant diagonal `d` agrees with `!![d, a; b, d]` through `e`. -/
theorem forall_eq_of_apply_offDiag_two {B R : Type*} {A : Matrix B B R} {d a b : R}
    (hA : ∀ i, A i i = d) (e : B ≃ Fin 2) (h01 : A (e.symm 0) (e.symm 1) = a)
    (h10 : A (e.symm 1) (e.symm 0) = b) (i j : B) :
    A i j = !![d, a; b, d] (e i) (e j) :=
  forall_eq_of_apply_offDiag hA e (fun i ↦ by fin_cases i <;> rfl) (by simpa using h01)
    (by simpa using h10) i j

end Matrix
