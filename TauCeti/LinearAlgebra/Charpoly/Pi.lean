/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import TauCeti.LinearAlgebra.Pi

/-!
# Characteristic polynomials on finite products

The characteristic polynomial of a coordinatewise endomorphism `LinearMap.piMap f` of a finite
product of finite free modules is the product of the characteristic polynomials of its
components (`LinearMap.charpoly_piMap`). This extends Mathlib's `LinearMap.charpoly_prodMap` from
two factors to finitely many. In a product basis `piMap f` has the block-diagonal matrix of the
`f i` (`LinearMap.toMatrix_piMap`), its characteristic matrix is block diagonal with the
characteristic matrices of the `f i` as blocks (`Matrix.charmatrix_blockDiagonal'`), and the
determinant of a block-diagonal matrix is the product of the determinants of its blocks
(`Matrix.det_blockDiagonal'`).

## Main results

* `Matrix.charpoly_blockDiagonal'`: the characteristic polynomial of a block-diagonal matrix is
  the product of the characteristic polynomials of its blocks.
* `LinearMap.charpoly_piMap`: the characteristic polynomial of `piMap f` is `∏ i, (f i).charpoly`.
-/

public section

open Polynomial

namespace Matrix

variable {R o : Type*} [CommRing R] [Fintype o] [DecidableEq o] {m : o → Type*}
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- The characteristic matrix of a block-diagonal matrix is block diagonal, with the
characteristic matrices of the blocks as blocks. -/
theorem charmatrix_blockDiagonal' (B : ∀ i, Matrix (m i) (m i) R) :
    charmatrix (blockDiagonal' B) = blockDiagonal' fun i => charmatrix (B i) := by
  refine Matrix.ext fun ⟨i, a⟩ ⟨j, c⟩ => ?_
  rcases eq_or_ne i j with rfl | h
  · rcases eq_or_ne a c with rfl | hac
    · simp [charmatrix_apply_eq]
    · simp [hac]
  · simp [h, blockDiagonal'_apply_ne _ _ _ h]

/-- The characteristic polynomial of a block-diagonal matrix with blocks of possibly different
sizes is the product of the characteristic polynomials of the blocks. -/
@[simp]
theorem charpoly_blockDiagonal' (B : ∀ i, Matrix (m i) (m i) R) :
    (blockDiagonal' B).charpoly = ∏ i, (B i).charpoly := by
  rw [charpoly, charmatrix_blockDiagonal', det_blockDiagonal']
  rfl

end Matrix

namespace LinearMap

variable {R ι : Type*} [CommRing R] [Fintype ι] {M : ι → Type*} [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)] [∀ i, Module.Finite R (M i)]

/-- **The characteristic polynomial is multiplicative on finite products.** The characteristic
polynomial of a coordinatewise endomorphism `piMap f` of a finite product of finite free modules
is the product of the characteristic polynomials of its components. -/
theorem charpoly_piMap (f : ∀ i, Module.End R (M i)) :
    (piMap f).charpoly = ∏ i, (f i).charpoly := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (M i)
  rw [← charpoly_toMatrix _ (Pi.basis b), toMatrix_piMap b b, Matrix.charpoly_blockDiagonal']
  exact Finset.prod_congr rfl fun i _ => charpoly_toMatrix (f i) (b i)

end LinearMap
