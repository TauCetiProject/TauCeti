/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv

/-!
# The negative squared norm as a quadratic form

This form specifies the convention in which multiplication by a real Clifford generator
squares to minus its squared length. Linear isometries preserve the form.
-/

public noncomputable section

namespace TauCeti

variable (V : Type*) [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The negative squared length as a quadratic form on a real inner product space. -/
def negNormSqForm : QuadraticForm ℝ V :=
  -LinearMap.BilinMap.toQuadraticMap (innerₗ V)

/-- Evaluating the negative squared-norm form gives minus the squared norm. -/
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

namespace LinearIsometryEquiv

open TauCeti

variable {V W U : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

/-- A real linear isometry preserves the negative squared length. -/
def negNormSqFormIsometryEquiv (e : V ≃ₗᵢ[ℝ] W) :
    (negNormSqForm V).IsometryEquiv (negNormSqForm W) where
  toLinearEquiv := e.toLinearEquiv
  map_app' v := by simp

@[simp]
theorem negNormSqFormIsometryEquiv_apply (e : V ≃ₗᵢ[ℝ] W) (v : V) :
    e.negNormSqFormIsometryEquiv v = e v := (rfl)

@[simp]
theorem negNormSqFormIsometryEquiv_refl :
    (LinearIsometryEquiv.refl ℝ V).negNormSqFormIsometryEquiv =
      QuadraticMap.IsometryEquiv.refl (negNormSqForm V) := (rfl)

@[simp]
theorem negNormSqFormIsometryEquiv_trans (e : V ≃ₗᵢ[ℝ] W) (f : W ≃ₗᵢ[ℝ] U) :
    (e.trans f).negNormSqFormIsometryEquiv =
      e.negNormSqFormIsometryEquiv.trans f.negNormSqFormIsometryEquiv := (rfl)

end LinearIsometryEquiv
