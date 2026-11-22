/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Block

import TauCeti.LinearAlgebra.Matrix.Block

/-!
# The characteristic polynomial of a coordinatewise endomorphism

A family of endomorphisms `fᵢ` of free modules of finite rank `Mᵢ`, indexed by a finite type,
acts coordinatewise on the product `∀ i, Mᵢ` (`LinearMap.piMap`). Its characteristic polynomial is
the product of the characteristic polynomials of the `fᵢ`. In the product basis its matrix is the
block-diagonal matrix `Matrix.blockDiagonal'` of the matrices of the `fᵢ`, whose blocks may have
different sizes, and the characteristic polynomial of a block-diagonal matrix is the product of
those of its blocks. This extends Mathlib's `LinearMap.charpoly_prodMap` from two factors to
finitely many.

## Main results

* `Matrix.charpoly_blockDiagonal'`: the characteristic polynomial of `blockDiagonal' A` is
  `∏ i, (A i).charpoly`.
* `LinearMap.charpoly_piMap`: the characteristic polynomial of `LinearMap.piMap f` is
  `∏ i, (f i).charpoly`.
-/

public section

namespace Matrix

variable {R : Type*} [CommRing R] {o : Type*} {m : o → Type*} [Fintype o] [DecidableEq o]
  [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]

/-- The characteristic polynomial of a block-diagonal matrix, whose blocks may have different
sizes, is the product of the characteristic polynomials of its blocks. -/
@[simp]
theorem charpoly_blockDiagonal' (A : ∀ i, Matrix (m i) (m i) R) :
    (blockDiagonal' A).charpoly = ∏ i, (A i).charpoly := by
  have h : charmatrix (blockDiagonal' A) = blockDiagonal' fun i ↦ charmatrix (A i) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rcases eq_or_ne i j with rfl | h
    · simp [charmatrix_apply, blockDiagonal'_apply_eq, diagonal_apply]
    · simp [blockDiagonal'_apply_ne _ _ _ h, h]
  simp only [charpoly, h, det_blockDiagonal']

end Matrix

namespace LinearMap

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {M : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, Module.Free R (M i)]
  [∀ i, Module.Finite R (M i)]

/-- The characteristic polynomial of an endomorphism of a finite product of free modules of finite
rank acting coordinatewise is the product of the characteristic polynomials of its coordinates. -/
@[simp]
theorem charpoly_piMap (f : ∀ i, Module.End R (M i)) :
    (piMap f).charpoly = ∏ i, (f i).charpoly := by
  classical
  let b (i : ι) := Module.Free.chooseBasis R (M i)
  -- In the product basis, `piMap f` has the block-diagonal matrix of the matrices of the `f i`.
  have h : toMatrix (Pi.basis b) (Pi.basis b) (piMap f) =
      Matrix.blockDiagonal' fun i ↦ toMatrix (b i) (b i) (f i) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rcases eq_or_ne i j with rfl | h
    · simp [toMatrix_apply, Matrix.blockDiagonal'_apply_eq]
    · simp [toMatrix_apply, Matrix.blockDiagonal'_apply_ne _ _ _ h, Pi.single_eq_of_ne h]
  rw [← charpoly_toMatrix _ (Pi.basis b), h, Matrix.charpoly_blockDiagonal']
  simp only [charpoly_toMatrix]

end LinearMap
