/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Matrix.Basis
public import TauCeti.LinearAlgebra.Matrix.Submatrix

/-!
# Corner embeddings of general linear Lie algebras

An injection `f : m ↪ n` of finite index types embeds `gl m` in `gl n` as the matrices supported
on the rows and columns in the range of `f`: a matrix `A : Matrix m m R` goes to the matrix with
`A a b` in position `(f a, f b)` and zeros elsewhere. For `Fin k ↪ Fin n` given by `Fin.castLE`
this is the upper-left corner `gl k ⊆ gl n`, and the chain of these corners
`gl 1 ⊆ gl 2 ⊆ ⋯ ⊆ gl n` is the one along which Gelfand-Tsetlin theory restricts.

The map is conjugation `A ↦ P * A * Pᵀ` by the `n × m` matrix `P` of the embedding, whose column
`a` is the standard basis vector at `f a`. Since `f` is injective, `Pᵀ * P = 1`, so this is
multiplicative and in particular preserves commutators. It does not preserve the identity
unless `f` is surjective, so it is a Lie algebra homomorphism but not an algebra homomorphism.

## Main definitions

* `TauCeti.glEmbedding`: the Lie algebra homomorphism `gl m → gl n` induced by `f : m ↪ n`.

## Main results

* `TauCeti.glEmbedding_single`: a matrix unit goes to the matrix unit at the image indices.
* `TauCeti.glEmbedding_apply_apply`: the entries in the range of `f` are those of the source.
* `TauCeti.glEmbedding_eq_sum_single`: the image as a sum of matrix units.
* `TauCeti.glEmbedding_injective`: the embedding is injective.
* `TauCeti.glEmbedding_refl` and `TauCeti.glEmbedding_trans`: the embeddings compose along
  composites of injections.
-/

public section

namespace TauCeti

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable (R : Type*) [CommRing R]
variable {l m n : Type*} [Fintype l] [DecidableEq l] [Fintype m] [DecidableEq m]
  [Fintype n] [DecidableEq n]

/-- The **corner embedding** `gl m → gl n` of an injection `f : m ↪ n`, sending a matrix `A` to the
matrix with `A a b` in position `(f a, f b)` and zeros elsewhere. -/
def glEmbedding (f : m ↪ n) : Matrix m m R →ₗ⁅R⁆ Matrix n n R where
  toFun A := (1 : Matrix n n R).submatrix id f * A * (1 : Matrix n n R).submatrix f id
  map_add' A B := by rw [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by rw [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply]
  map_lie' {A B} := by
    have h (X : Matrix m n R) :
        (1 : Matrix n n R).submatrix f id * ((1 : Matrix n n R).submatrix id f * X) = X := by
      rw [← Matrix.mul_assoc, submatrix_one_mul_submatrix_one, Matrix.one_mul]
    simp only [LieRing.of_associative_ring_bracket, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_assoc, h]

variable {R}

/-- The corner embedding is conjugation by the `n × m` matrix of the injection, whose column `a` is
the standard basis vector at `f a`. -/
theorem glEmbedding_apply (f : m ↪ n) (A : Matrix m m R) :
    glEmbedding R f A =
      (1 : Matrix n n R).submatrix id f * A * (1 : Matrix n n R).submatrix f id :=
  (rfl)

/-- The corner embedding sends a matrix unit to the matrix unit at the image indices. -/
@[simp]
theorem glEmbedding_single (f : m ↪ n) (a b : m) (c : R) :
    glEmbedding R f (single a b c) = single (f a) (f b) c := by
  ext i j
  simp only [glEmbedding_apply, mul_apply, submatrix_apply, id_eq, one_apply,
    single_apply, ite_and, mul_ite, ite_mul, mul_zero, zero_mul, one_mul, mul_one]
  rw [Fintype.sum_eq_single b fun x hx => by simp [Ne.symm hx]]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  grind

/-- The corner embedding of `A` is the sum of the matrix units at the image indices, weighted by
the entries of `A`. -/
theorem glEmbedding_eq_sum_single (f : m ↪ n) (A : Matrix m m R) :
    glEmbedding R f A = ∑ a, ∑ b, single (f a) (f b) (A a b) := by
  conv_lhs => rw [matrix_eq_sum_single A]
  simp only [map_sum, glEmbedding_single]

/-- The entries of the corner embedding at the image indices are those of the source matrix. -/
@[simp]
theorem glEmbedding_apply_apply (f : m ↪ n) (A : Matrix m m R) (a b : m) :
    glEmbedding R f A (f a) (f b) = A a b := by
  simp [glEmbedding_eq_sum_single, Matrix.sum_apply, single_apply, ite_and]

/-- The corner embedding is injective. -/
theorem glEmbedding_injective (f : m ↪ n) : Function.Injective (glEmbedding R f) := by
  intro A B h
  ext a b
  rw [← glEmbedding_apply_apply f A, h, glEmbedding_apply_apply]

/-- The corner embedding of the identity injection is the identity. -/
@[simp]
theorem glEmbedding_refl : glEmbedding R (Function.Embedding.refl m) = LieHom.id := by
  ext A : 1
  rw [glEmbedding_eq_sum_single, LieHom.id_apply]
  simp only [Function.Embedding.refl_apply]
  exact (matrix_eq_sum_single A).symm

/-- The corner embedding of a composite of injections is the composite of the corner
embeddings. -/
theorem glEmbedding_trans (f : l ↪ m) (g : m ↪ n) :
    glEmbedding R (f.trans g) = (glEmbedding R g).comp (glEmbedding R f) := by
  ext A : 1
  simp only [LieHom.comp_apply, glEmbedding_eq_sum_single f A, map_sum, glEmbedding_single,
    glEmbedding_eq_sum_single (f.trans g), Function.Embedding.trans_apply]

end TauCeti
