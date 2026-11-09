/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange

/-!
# Lie subalgebra inclusions after restricting scalars

A Lie subalgebra over an algebra `A` includes into its ambient Lie algebra over the smaller
scalar ring `R`. The domain uses `RestrictScalars`, so this inclusion can be composed with
Lie homomorphisms defined on the underlying `R`-Lie algebra.
-/

public section

namespace LieSubalgebra

variable {A L : Type*} [CommRing A] [LieRing L] [LieAlgebra A L]
  (K : LieSubalgebra A L) (R : Type*) [CommRing R] [Algebra R A]
  [LieAlgebra R L] [IsScalarTower R A L]

/-- The inclusion of a Lie subalgebra, viewed as a Lie homomorphism over the smaller scalars. -/
def restrictScalarsIncl : RestrictScalars R A K →ₗ⁅R⁆ L where
  toFun x := K.incl (RestrictScalars.addEquiv R A K x)
  map_add' x y := by rw [map_add, map_add]
  map_smul' r x := by
    rw [RestrictScalars.addEquiv_map_smul, map_smul, algebraMap_smul, RingHom.id_apply]
  map_lie' {x y} := K.incl.map_lie x y

/-- Scalar restriction preserves the underlying inclusion into the ambient Lie algebra. -/
@[simp]
theorem restrictScalarsIncl_apply (x : RestrictScalars R A K) :
    K.restrictScalarsIncl R x = (RestrictScalars.addEquiv R A K x : L) := by
  rfl

end LieSubalgebra
