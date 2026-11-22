/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import TauCeti.Topology.Algebra.Module.ComplexSmulI
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Multiplication by `i` as a real linear isometry

On a complex normed space `X` with `IsScalarTower ℝ ℂ X`, multiplication by `i` preserves norms
since `‖i‖ = 1`, upgrading `Complex.smulIEquiv` to
`Complex.smulILinearIsometryEquiv : X ≃ₗᵢ[ℝ] X`.
-/

public section

namespace Complex

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℂ X]
  [IsScalarTower ℝ ℂ X]

/-- Multiplication by `i` as a real linear isometry equivalence of a complex normed space. -/
noncomputable def smulILinearIsometryEquiv : X ≃ₗᵢ[ℝ] X :=
  ⟨(smulIEquiv X).toLinearEquiv, fun _ ↦ by simp [norm_smul]⟩

variable {X}

/-- `Complex.smulILinearIsometryEquiv` acts by scalar multiplication by `I`. -/
@[simp] theorem smulILinearIsometryEquiv_apply (x : X) : smulILinearIsometryEquiv X x = I • x :=
  smulIEquiv_apply x

/-- The inverse of `Complex.smulILinearIsometryEquiv` acts by scalar multiplication by `-I`. -/
@[simp] theorem smulILinearIsometryEquiv_symm_apply (x : X) :
    (smulILinearIsometryEquiv X).symm x = -I • x := smulIEquiv_symm_apply x

/-- Forgetting the isometry property recovers `Complex.smulIEquiv`. -/
@[simp] theorem toContinuousLinearEquiv_smulILinearIsometryEquiv :
    (smulILinearIsometryEquiv X).toContinuousLinearEquiv = smulIEquiv X := by ext; simp

end Complex

end
