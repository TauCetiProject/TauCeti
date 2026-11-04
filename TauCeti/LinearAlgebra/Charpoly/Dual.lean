/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# Characteristic polynomials of dual endomorphisms

An endomorphism and its dual have the same characteristic polynomial. This allows
computations with differentials, which naturally lie in a dual space, to recover the
characteristic polynomial on the original space.
-/

public section

namespace LinearMap

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Module.Free R M] [Module.Finite R M]

/-- Dualizing a finite free endomorphism preserves its characteristic polynomial. -/
@[simp]
theorem charpoly_dualMap (f : M →ₗ[R] M) : f.dualMap.charpoly = f.charpoly := by
  let b := Module.Free.chooseBasis R M
  let := Module.Free.ChooseBasisIndex.fintype R M
  rw [← f.charpoly_toMatrix b, ← f.dualMap.charpoly_toMatrix b.dualBasis]
  simp [dualMap_def, toMatrix_transpose]

end LinearMap
