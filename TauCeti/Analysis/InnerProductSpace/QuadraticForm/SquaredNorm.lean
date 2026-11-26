/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# The negative squared norm as a quadratic form

This form specifies the convention in which multiplication by a real Clifford generator
squares to minus its squared length.
-/

public noncomputable section

namespace TauCeti

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The negative squared length as a quadratic form on a real inner product space. -/
def negNormSqForm : QuadraticForm ℝ V :=
  -LinearMap.BilinMap.toQuadraticMap (innerₗ V)

@[simp]
theorem negNormSqForm_apply (v : V) : negNormSqForm V v = -‖v‖ ^ 2 := by
  simp [negNormSqForm]

/-- Negating the negative squared length gives a positive definite quadratic form. -/
theorem posDef_neg_negNormSqForm : (-negNormSqForm V).PosDef := by
  intro v hv
  simpa using sq_pos_of_pos (norm_pos_iff.mpr hv)

variable {V}

/-- The bilinear form associated to the negative squared length is minus the real inner product. -/
theorem associated_negNormSqForm :
    QuadraticMap.associated (negNormSqForm V) = -(innerₗ V) := by
  rw [negNormSqForm, map_neg]
  exact congrArg Neg.neg (QuadraticMap.associated_left_inverse ℕ
    (B₁ := innerₗ V) fun x y ↦ real_inner_comm y x)

end TauCeti
