/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.Cotangent

/-!
# Linear relations for the cotangent displacement

The Leibniz relations of a bialgebra are the image of a linear map from its tensor square.
They vanish under the cotangent displacement.
-/

public noncomputable section

open Coalgebra TensorProduct

namespace TauCeti.Bialgebra

variable (R A : Type*) [CommRing R] [CommRing A] [Bialgebra R A]

/-- The linear map generating the Leibniz relations for displacement at the counit. -/
def cotangentRelation : A ⊗[R] A →ₗ[R] A :=
  LinearMap.mul' R A -
    (TensorProduct.rid R A).toLinearMap.comp ((counit (R := R)).lTensor A) -
    (TensorProduct.lid R A).toLinearMap.comp ((counit (R := R)).rTensor A)

/-- A pure tensor gives the Leibniz relation at the counit. -/
@[simp]
theorem cotangentRelation_tmul (a b : A) :
    cotangentRelation R A (a ⊗ₜ[R] b) =
      a * b - counit (R := R) b • a - counit (R := R) a • b := by
  simp [cotangentRelation]

/-- The cotangent displacement annihilates the Leibniz relations. -/
@[simp]
theorem cotangentMap_comp_cotangentRelation :
    (cotangentMap R A).comp (cotangentRelation R A) = 0 := by
  ext a b
  simp [cotangentMap_mul]

/-- The cotangent displacement of every Leibniz relation is zero. -/
@[simp]
theorem cotangentMap_cotangentRelation (t : A ⊗[R] A) :
    cotangentMap R A (cotangentRelation R A t) = 0 := by
  simpa only [LinearMap.comp_apply, LinearMap.zero_apply] using
    LinearMap.congr_fun (cotangentMap_comp_cotangentRelation R A) t

end TauCeti.Bialgebra
