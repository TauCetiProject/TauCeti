/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Basic

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

The property is stated as the conjunction of the value at the target of each column and the
vanishing of that column elsewhere, so that it needs no decidable equality on the rows; the
entrywise description by a table lookup is recovered as `Matrix.isStep_iff` over rows that do
have decidable equality.

The target of a column with coefficient zero is unconstrained, so the pair `(t, c)` is not
determined by the matrix; every statement below takes the witnessing pair as data.

## Main definitions

* `Matrix.IsStep`: the property, witnessed by a target function and a coefficient function.

## Main results

* `Matrix.IsStep.apply_target`, `Matrix.IsStep.apply_of_ne` and
  `Matrix.isStep_of_apply_target_of_apply_of_ne`: the elimination and introduction forms through
  which the definition is used; its body is not exposed.
* `Matrix.isStep_iff`, `Matrix.isStep_of_apply` and `Matrix.IsStep.apply`: the entrywise table
  lookup description, over rows with decidable equality.
* `Matrix.IsStep.mul`: a product of step matrices is a step matrix.
* `Matrix.isStep_one`, `Matrix.isStep_diagonal`: the identity and the diagonal matrices.
* `Matrix.IsStep.map`: entrywise application of a zero-preserving map.
-/

public section

namespace Matrix

variable {l m n R S : Type*}

/-- A matrix is a *step matrix* for a target function `t` and a coefficient function `c` when
its `b`th column is `c b` times the `t b`th coordinate vector. -/
def IsStep [Zero R] (M : Matrix m n R) (t : n → m) (c : n → R) : Prop :=
  (∀ b, M (t b) b = c b) ∧ ∀ a b, a ≠ t b → M a b = 0

section Zero

variable [Zero R] {M : Matrix m n R} {t : n → m} {c : n → R}

/-- The entry of a step matrix at the target of its column is the coefficient of that column. -/
theorem IsStep.apply_target (h : M.IsStep t c) (b : n) : M (t b) b = c b :=
  h.1 b

/-- The entry of a step matrix at a row other than the target of its column is zero. -/
theorem IsStep.apply_of_ne (h : M.IsStep t c) {a : m} {b : n} (hab : a ≠ t b) : M a b = 0 :=
  h.2 a b hab

/-- **The introduction form**: a matrix that takes the prescribed coefficient at the target of
each column and vanishes elsewhere in that column is a step matrix. -/
theorem isStep_of_apply_target_of_apply_of_ne (ht : ∀ b, M (t b) b = c b)
    (h0 : ∀ a b, a ≠ t b → M a b = 0) : M.IsStep t c :=
  ⟨ht, h0⟩

variable [DecidableEq m]

/-- **The entrywise description of a step matrix** by a table lookup. -/
theorem isStep_iff : M.IsStep t c ↔ ∀ a b, M a b = if a = t b then c b else 0 := by
  constructor
  · intro h a b
    split_ifs with hab
    · rw [hab, h.apply_target]
    · exact h.apply_of_ne hab
  · intro h
    exact isStep_of_apply_target_of_apply_of_ne (fun b => by simpa using h (t b) b)
      fun a b hab => by simpa [hab] using h a b

/-- **The introduction form**: a matrix whose entries are the table lookups is a step matrix. -/
theorem isStep_of_apply (h : ∀ a b, M a b = if a = t b then c b else 0) : M.IsStep t c :=
  isStep_iff.mpr h

/-- **The elimination form**: every entry of a step matrix is a table lookup. -/
theorem IsStep.apply (h : M.IsStep t c) (a : m) (b : n) :
    M a b = if a = t b then c b else 0 :=
  isStep_iff.mp h a b

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
theorem IsStep.mul [Fintype m] [NonUnitalNonAssocSemiring R]
    {M : Matrix l m R} {N : Matrix m n R} {t : m → l} {t' : n → m} {c : m → R} {c' : n → R}
    (hM : M.IsStep t c) (hN : N.IsStep t' c') :
    (M * N).IsStep (t ∘ t') fun b => c (t' b) * c' b := by
  refine isStep_of_apply_target_of_apply_of_ne (fun b => ?_) fun a b hab => ?_
  · rw [mul_apply, Finset.sum_eq_single (t' b)]
    · rw [Function.comp_apply, hM.apply_target, hN.apply_target]
    · intro i _ hi
      rw [hN.apply_of_ne hi, mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ (t' b)) hb
  · have hab' : a ≠ t (t' b) := hab
    rw [mul_apply, Finset.sum_eq_single (t' b)]
    · rw [hM.apply_of_ne hab', zero_mul]
    · intro i _ hi
      rw [hN.apply_of_ne hi, mul_zero]
    · intro hb
      exact absurd (Finset.mem_univ (t' b)) hb

/-- Entrywise application of a zero-preserving map to a step matrix gives the step matrix of the
same target and the transformed coefficients. Only the value at zero is used, so no additive or
multiplicative structure is required of the map. -/
theorem IsStep.map [Zero R] [Zero S] {M : Matrix m n R} {t : n → m} {c : n → R}
    (h : M.IsStep t c) (f : R → S) (hf : f 0 = 0) :
    (M.map f).IsStep t fun b => f (c b) :=
  isStep_of_apply_target_of_apply_of_ne (fun b => by rw [map_apply, h.apply_target])
    fun a b hab => by rw [map_apply, h.apply_of_ne hab, hf]

end Matrix
