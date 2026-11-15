/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The characteristic polynomial of the transpose

Over a commutative ring, the transpose `f.dualMap` of an endomorphism `f` of a finite free module
has the characteristic polynomial of `f` (`LinearMap.charpoly_dualMap`): in the dual basis its
matrix is the transposed matrix of `f`. Over a field, their kernels also have the same dimension
(`LinearMap.finrank_ker_dualMap`).
-/

public section

open Module

namespace LinearMap

/-- Over a commutative ring, the transpose of an endomorphism of a finite free module has the
same characteristic polynomial. -/
@[simp]
theorem charpoly_dualMap {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] (f : Module.End R M) :
    f.dualMap.charpoly = f.charpoly := by
  nontriviality R
  let b := Module.Free.chooseBasis R M
  rw [← charpoly_toMatrix f b, ← charpoly_toMatrix f.dualMap b.dualBasis, dualMap_def,
    toMatrix_transpose, Matrix.charpoly_transpose]

/-- An endomorphism of a finite-dimensional vector space and its transpose have kernels of the
same dimension. -/
@[simp]
theorem finrank_ker_dualMap {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) :
    finrank K (ker f.dualMap) = finrank K (ker f) := by
  have h₁ := finrank_range_add_finrank_ker f.dualMap
  have h₂ := finrank_range_add_finrank_ker f
  rw [finrank_range_dualMap_eq_finrank_range, Subspace.dual_finrank_eq] at h₁
  omega

end LinearMap
