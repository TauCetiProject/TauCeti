/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Corestrict

/-!
# Matrix coefficients under corestriction

Corestriction along a coalgebra morphism applies that morphism to each matrix
coefficient. This gives the coordinate formula for restricting a representation
along a morphism of affine group schemes, without requiring a finite basis.

The calculation follows `Comodule.coefficientMatrix_corestrict`, using the same
tensor-product naturality identity for an arbitrary functional and vector.

## References

* M. E. Sweedler, *Hopf Algebras*, Chapter 2.
-/

public section

open TauCeti TauCeti.Comodule

namespace CoalgHom

variable {R C D M : Type*} [CommSemiring R]
  [AddCommMonoid C] [Module R C] [Coalgebra R C]
  [AddCommMonoid D] [Module R D] [Coalgebra R D]
  [AddCommMonoid M] [Module R M] [Comodule R C M]

/-- Corestriction applies the coalgebra morphism to each matrix coefficient. -/
@[simp]
theorem matrixCoefficient_corestrict (f : C →ₗc[R] D) (φ : Module.Dual R M) (m : M) :
    (letI : Comodule R D M := Corestrict f
     matrixCoefficient (C := D) φ m) = f (matrixCoefficient (C := C) φ m) := by
  let : Comodule R D M := Corestrict f
  rw [matrixCoefficient_def, matrixCoefficient_def, corestrict_coact_apply]
  rw [TensorProduct.map_map, LinearMap.id_comp, LinearMap.comp_id]
  exact LinearMap.congr_fun (CoassocSimps.lid_comp_map φ f.toLinearMap)
    (coact (R := R) (C := C) m)

end CoalgHom
