/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Scalar multiplication by `±1` after restricting scalars

For a scalar tower `R → A → M`, scalar multiplication `LinearMap.lsmul A M a` by `a = 1` or
`a = -1`, viewed as an `R`-linear map, is the identity or its negative.

## Main declarations

* `LinearMap.lsmul_one_restrictScalars`: `(lsmul A M 1).restrictScalars R = id`.
* `LinearMap.lsmul_neg_one_restrictScalars`: `(lsmul A M (-1)).restrictScalars R = -id`.
-/

public section

namespace LinearMap

variable {R A M : Type*}

/-- Scalar multiplication by `1`, viewed as an `R`-linear map, is the identity. -/
@[simp]
theorem lsmul_one_restrictScalars [CommSemiring R] [CommSemiring A] [AddCommMonoid M] [Module R M]
    [Module A M] [SMul R A] [IsScalarTower R A M] :
    (lsmul A M (1 : A)).restrictScalars R = LinearMap.id := by
  ext x
  simp

/-- Scalar multiplication by `-1`, viewed as an `R`-linear map, is minus the identity. Not
`@[simp]`: simp derives it from `LinearMap.lsmul_one_restrictScalars` and `map_neg`. -/
theorem lsmul_neg_one_restrictScalars [CommSemiring R] [CommRing A] [AddCommGroup M] [Module R M]
    [Module A M] [SMul R A] [IsScalarTower R A M] :
    (lsmul A M (-1 : A)).restrictScalars R = -LinearMap.id := by
  ext x
  simp

end LinearMap
