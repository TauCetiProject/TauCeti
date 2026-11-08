/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Algebra.Group.End

/-!
# Linear isometries acting on the additive group

`LinearIsometryEquiv.multiplicativeAutHom` bundles the evaluation action of linear
isometries on the additive group. It uses `Multiplicative` to supply the action homomorphism
required by `SemidirectProduct`, in particular for the affine isometry group decomposition.
The construction reuses `AddEquiv.toMultiplicative` and forgets the scalar and norm structure
of each linear isometry.
-/

public section

namespace LinearIsometryEquiv

variable {R E : Type*} [Semiring R] [SeminormedAddCommGroup E] [Module R E]

/-- The usual action of linear isometries on the additive group, written multiplicatively
for use in a semidirect product. -/
def multiplicativeAutHom : (E ≃ₗᵢ[R] E) →* MulAut (Multiplicative E) where
  toFun L := AddEquiv.toMultiplicative L.toLinearEquiv.toAddEquiv
  map_one' := by ext x; rfl
  map_mul' L K := by ext x; rfl

/-- The multiplicative action is evaluation of the linear isometry. -/
@[simp]
theorem multiplicativeAutHom_apply (L : E ≃ₗᵢ[R] E) (v : Multiplicative E) :
    multiplicativeAutHom L v = Multiplicative.ofAdd (L v.toAdd) := (rfl)

end LinearIsometryEquiv
