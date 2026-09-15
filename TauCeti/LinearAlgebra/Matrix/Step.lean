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

The same file records `Matrix.IsDoubleStep`, the property of having at most two nonzero entries
in each column, witnessed by two target functions and two coefficient functions. It arises for a
linear map carrying each vector of a basis into the span of at most two others, as happens in a
weight basis of a module all of whose weight spaces have dimension at most two. A product with a
double step matrix has each entry a sum of two products of table lookups, on either side once the
step structure of the other factor is known, and a linear combination indexed by the columns of a
double step matrix collapses to two terms.

The target of a column with coefficient zero is unconstrained, so the pair `(t, c)` is not
determined by the matrix; every statement below takes the witnessing pair as data.

## Main definitions

* `Matrix.IsStep`: the property, witnessed by a target function and a coefficient function.
* `Matrix.IsDoubleStep`: at most two nonzero entries in each column, witnessed by two target
  functions and two coefficient functions.

## Main results

* `Matrix.isStep_iff`, `Matrix.isStep_of_apply` and `Matrix.IsStep.apply`: the characterization
  of the property and its introduction and elimination forms, through which the definition is
  used; its body is not exposed.
* `Matrix.IsStep.mul`: a product of step matrices is a step matrix.
* `Matrix.isStep_one`, `Matrix.isStep_diagonal`: the identity and the diagonal matrices.
* `Matrix.IsStep.map`: entrywise application of a zero-preserving map.
* `Matrix.IsDoubleStep.mul_apply` and `Matrix.IsDoubleStep.transpose_mul_apply`, together with
  `Matrix.IsStep.mul_apply` and `Matrix.IsStep.transpose_mul_apply`: an entry of a product with a
  double step or a step matrix, on the right and on the left.
* `Matrix.IsDoubleStep.sum_smul` and `Matrix.IsStep.sum_smul`: a linear combination indexed by a
  column.
* `Matrix.IsDoubleStep.map`: entrywise application of a ring morphism. A transposed form is not
  needed: `Matrix.transpose_map` turns the transpose of a mapped matrix into the mapped
  transpose, so `h.map f` already covers it.
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

/-! ## Matrices with at most two nonzero entries in each column -/

/-- A matrix is a *double step matrix* for two target functions `t₁, t₂` and two coefficient
functions `c₁, c₂` when its `b`th column is `c₁ b` times the `t₁ b`th coordinate vector plus
`c₂ b` times the `t₂ b`th coordinate vector. The two targets of a column are allowed to
coincide. -/
@[expose] def IsDoubleStep [DecidableEq n] [AddZeroClass R] (M : Matrix n n R) (t₁ : n → n)
    (c₁ : n → R) (t₂ : n → n) (c₂ : n → R) : Prop :=
  ∀ a b, M a b = (if a = t₁ b then c₁ b else 0) + (if a = t₂ b then c₂ b else 0)

/-- A step matrix is a double step matrix whose second coefficient vanishes. -/
theorem IsStep.isDoubleStep [DecidableEq n] [AddZeroClass R] {M : Matrix n n R} {t : n → n}
    {c : n → R} (h : M.IsStep t c) : M.IsDoubleStep t c t 0 := fun a b => by
  rw [h.apply a b]
  split_ifs <;> simp

/-- Entrywise application of a ring morphism to a double step matrix gives the double step matrix
of the same targets and the transformed coefficients. -/
theorem IsDoubleStep.map [DecidableEq n] [NonAssocSemiring R] [NonAssocSemiring S]
    {M : Matrix n n R}
    {t₁ t₂ : n → n} {c₁ c₂ : n → R} (h : M.IsDoubleStep t₁ c₁ t₂ c₂) (f : R →+* S) :
    (M.map f).IsDoubleStep t₁ (fun b => f (c₁ b)) t₂ fun b => f (c₂ b) := by
  intro a b
  rw [map_apply, h a b, map_add]
  split_ifs <;> simp

/-- **An entry of a product whose right factor is a double step matrix**: the sum of two products
of table lookups. -/
theorem IsDoubleStep.mul_apply [DecidableEq n] [Fintype n] [NonUnitalNonAssocSemiring R]
    {N : Matrix n n R}
    {t₁ t₂ : n → n} {c₁ c₂ : n → R} (hN : N.IsDoubleStep t₁ c₁ t₂ c₂) (M : Matrix n n R)
    (a b : n) : (M * N) a b = M a (t₁ b) * c₁ b + M a (t₂ b) * c₂ b := by
  rw [Matrix.mul_apply]
  have hsplit : ∀ l, M a l * N l b =
      (if l = t₁ b then M a l * c₁ b else 0) + (if l = t₂ b then M a l * c₂ b else 0) := fun l => by
    rw [hN l b, mul_add]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun l _ => hsplit l, Finset.sum_add_distrib, Finset.sum_ite_eq' ,
    Finset.sum_ite_eq']
  simp

/-- **An entry of a product whose left factor has a double step transpose**: the sum of two
products of table lookups. -/
theorem IsDoubleStep.transpose_mul_apply [DecidableEq n] [Fintype n]
    [NonUnitalNonAssocSemiring R] {M : Matrix n n R} {t₁ t₂ : n → n} {c₁ c₂ : n → R}
    (hM : Mᵀ.IsDoubleStep t₁ c₁ t₂ c₂) (N : Matrix n n R) (a b : n) :
    (M * N) a b = c₁ a * N (t₁ a) b + c₂ a * N (t₂ a) b := by
  rw [Matrix.mul_apply]
  have hsplit : ∀ l, M a l * N l b =
      (if l = t₁ a then c₁ a * N l b else 0) + (if l = t₂ a then c₂ a * N l b else 0) := fun l => by
    rw [show M a l = Mᵀ l a from rfl, hM l a, add_mul]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun l _ => hsplit l, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp

/-- **A linear combination indexed by a column of a double step matrix collapses to two terms.** -/
theorem IsDoubleStep.sum_smul [DecidableEq n] [Fintype n] [Semiring R] {M : Matrix n n R}
    {t₁ t₂ : n → n}
    {c₁ c₂ : n → R} (hM : M.IsDoubleStep t₁ c₁ t₂ c₂) {M₀ : Type*} [AddCommMonoid M₀]
    [Module R M₀] (f : n → M₀) (b : n) :
    ∑ a, M a b • f a = c₁ b • f (t₁ b) + c₂ b • f (t₂ b) := by
  have hsplit : ∀ a, M a b • f a =
      (if a = t₁ b then c₁ b • f a else 0) + (if a = t₂ b then c₂ b • f a else 0) := fun a => by
    rw [hM a b, add_smul]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq']
  simp

/-- **An entry of a product whose right factor is a step matrix**: a single product of table
lookups. -/
theorem IsStep.mul_apply [DecidableEq n] [Fintype n] [NonUnitalNonAssocSemiring R]
    {N : Matrix n n R} {t : n → n} {c : n → R} (hN : N.IsStep t c) (M : Matrix n n R)
    (a b : n) :
    (M * N) a b = M a (t b) * c b := by
  rw [hN.isDoubleStep.mul_apply M a b, Pi.zero_apply, mul_zero, add_zero]

/-- **An entry of a product whose left factor has a step transpose**: a single product of table
lookups. -/
theorem IsStep.transpose_mul_apply [DecidableEq n] [Fintype n]
    [NonUnitalNonAssocSemiring R] {M : Matrix n n R} {t : n → n} {c : n → R} (hM : Mᵀ.IsStep t c)
    (N : Matrix n n R) (a b : n) :
    (M * N) a b = c a * N (t a) b := by
  rw [hM.isDoubleStep.transpose_mul_apply N a b, Pi.zero_apply, zero_mul, add_zero]

/-- **A linear combination indexed by a column of a step matrix is a single term.** -/
theorem IsStep.sum_smul [DecidableEq n] [Fintype n] [Semiring R] {M : Matrix n n R}
    {t : n → n} {c : n → R}
    (hM : M.IsStep t c) {M₀ : Type*} [AddCommMonoid M₀] [Module R M₀] (f : n → M₀) (b : n) :
    ∑ a, M a b • f a = c b • f (t b) := by
  rw [hM.isDoubleStep.sum_smul f b]
  simp

end Matrix
