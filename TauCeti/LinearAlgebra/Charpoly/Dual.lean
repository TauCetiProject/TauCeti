/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# The characteristic polynomial of the transpose

Over a field, the transpose `f.dualMap` of an endomorphism `f` of a finite-dimensional space has
the characteristic polynomial of `f` (`LinearMap.charpoly_dualMap`): in the dual basis its
matrix is the transposed matrix of `f`.
-/

public section

open Module

namespace LinearMap

/-- Over a field, the transpose of an endomorphism of a finite-dimensional space has the same
characteristic polynomial. -/
theorem charpoly_dualMap {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) : f.dualMap.charpoly = f.charpoly := by
  let b := Module.finBasis K V
  rw [← charpoly_toMatrix f b, ← charpoly_toMatrix f.dualMap b.dualBasis, dualMap,
    toMatrix_transpose, Matrix.charpoly_transpose]

end LinearMap
