/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Diagonal

/-!
# Matrices with at most one nonzero entry in each column

A *step matrix* is a matrix each of whose columns is a scalar multiple of a coordinate vector:
the `b`th column is `c b` times the `t b`th coordinate vector, for a target function `t` and a
coefficient function `c`. Permutation matrices, diagonal matrices and the matrix units are step
matrices, and so is the matrix of any linear map that carries each vector of a basis to a
multiple of a vector of another basis, a situation common in explicit representation theory.

The property is columnwise, so the row and column index types are allowed to differ: a step
matrix in `Matrix m n R` has target function `n → m`. The identity and the diagonal matrices are
of course square.

This file records the property as `Matrix.IsStep` and the closure properties that make it useful
for computation: a product of step matrices is the step matrix of the composed targets and the
coefficients multiplied along the way, and entrywise application of a ring morphism preserves the
property. Since each entry of such a product is a single product of table lookups rather than a
sum over an index type, identities between explicitly tabulated step matrices reduce to finitely
many entrywise identities that need no summation.

The target of a column with coefficient zero is unconstrained, so the pair `(t, c)` is not
determined by the matrix; every statement below takes the witnessing pair as data.

## Main definitions

* `Matrix.IsStep`: the property, witnessed by a target function and a coefficient function.

## Main results

* `Matrix.isStep_iff`, `Matrix.isStep_of_apply` and `Matrix.IsStep.apply`: the characterization
  of the property and its introduction and elimination forms, through which the definition is
  used; its body is not exposed.
* `Matrix.IsStep.mul`: a product of step matrices is a step matrix.
* `Matrix.isStep_one`, `Matrix.isStep_diagonal`: the identity and the diagonal matrices.
* `Matrix.IsStep.map`: entrywise application of a zero-preserving map.
-/

public section

namespace Matrix

variable {l m n R S : Type*}

/-- A matrix is a *step matrix* for a target function `t` and a coefficient function `c` when
its `b`th column is `c b` times the `t b`th coordinate vector. -/
def IsStep [DecidableEq m] [Zero R] (M : Matrix m n R) (t : n → m) (c : n → R) : Prop :=
  ∀ a b, M a b = if a = t b then c b else 0

section Zero

variable [DecidableEq m] [Zero R] {M : Matrix m n R} {t : n → m} {c : n → R}

/-- **The defining entrywise description of a step matrix.** -/
theorem isStep_iff : M.IsStep t c ↔ ∀ a b, M a b = if a = t b then c b else 0 :=
  Iff.rfl

/-- **The introduction form**: a matrix whose entries are the table lookups is a step matrix. -/
theorem isStep_of_apply (h : ∀ a b, M a b = if a = t b then c b else 0) : M.IsStep t c :=
  h

/-- **The elimination form**: every entry of a step matrix is a table lookup. -/
theorem IsStep.apply (h : M.IsStep t c) (a : m) (b : n) :
    M a b = if a = t b then c b else 0 :=
  h a b

/-- The entry of a step matrix at a row other than the target of its column is zero. -/
theorem IsStep.apply_of_ne (h : M.IsStep t c) {a : m} {b : n} (hab : a ≠ t b) : M a b = 0 := by
  rw [h.apply a b]
  exact ite_eq_right_iff.mpr fun hc => absurd hc hab

/-- The entry of a step matrix at the target of its column is the coefficient of that column. -/
theorem IsStep.apply_target (h : M.IsStep t c) (b : n) : M (t b) b = c b := by
  rw [h.apply (t b) b]
  simp

end Zero

/-- A diagonal matrix is the step matrix of the identity target and its own diagonal. -/
theorem isStep_diagonal [DecidableEq n] [Zero R] (d : n → R) : (diagonal d).IsStep id d := by
  refine isStep_of_apply fun a b => ?_
  rw [diagonal_apply, Function.id_def]
  split_ifs with h
  · rw [h]
  · rfl

/-- The identity matrix is the step matrix of the identity target and the constant coefficient
one. -/
theorem isStep_one [DecidableEq n] [Zero R] [One R] : (1 : Matrix n n R).IsStep id 1 :=
  isStep_of_apply fun _ _ => one_apply

/-- **A product of step matrices is a step matrix**, with the composite target function and with
each coefficient the product of the two coefficients met along the way. -/
theorem IsStep.mul [DecidableEq l] [DecidableEq m] [Fintype m] [NonUnitalNonAssocSemiring R]
    {M : Matrix l m R} {N : Matrix m n R} {t : m → l} {t' : n → m} {c : m → R} {c' : n → R}
    (hM : M.IsStep t c) (hN : N.IsStep t' c') :
    (M * N).IsStep (t ∘ t') fun b => c (t' b) * c' b := by
  refine isStep_of_apply fun a b => ?_
  rw [mul_apply, Finset.sum_eq_single (t' b)]
  · rw [hM.apply a (t' b), hN.apply_target b, Function.comp_apply]
    split_ifs
    · rfl
    · rw [zero_mul]
  · intro i _ hi
    rw [hN.apply_of_ne hi, mul_zero]
  · intro hb
    exact absurd (Finset.mem_univ (t' b)) hb

/-- Entrywise application of a zero-preserving map to a step matrix gives the step matrix of the
same target and the transformed coefficients. Only the value at zero is used, so no additive or
multiplicative structure is required of the map. -/
theorem IsStep.map [DecidableEq m] [Zero R] [Zero S] {M : Matrix m n R} {t : n → m} {c : n → R}
    (h : M.IsStep t c) (f : R → S) (hf : f 0 = 0) :
    (M.map f).IsStep t fun b => f (c b) := by
  refine isStep_of_apply fun a b => ?_
  rw [map_apply, h.apply a b]
  split_ifs
  · rfl
  · exact hf

end Matrix
