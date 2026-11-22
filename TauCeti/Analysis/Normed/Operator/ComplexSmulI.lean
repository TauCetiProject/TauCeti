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
since `‖i‖ = 1`. Upgrading `Complex.smulIEquiv` to `Complex.smulILinearIsometryEquiv : X ≃ₗᵢ[ℝ] X`
shows `‖(Complex.I • L).inverse‖ = ‖L.inverse‖` (`ContinuousLinearMap.norm_inverse_I_smul`) for any
`L : Y →L[ℝ] X`, as needed when passing between a first-order ODE operator `L` and `i • L`.
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

namespace ContinuousLinearMap

/-- Multiplying `L : Y →L[ℝ] X` by `I` preserves the operator norm of its totalized inverse. -/
@[simp] theorem norm_inverse_I_smul {X Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℂ X] [IsScalarTower ℝ ℂ X]
    (L : Y →L[ℝ] X) : ‖(Complex.I • L).inverse‖ = ‖L.inverse‖ := by
  rw [← Complex.smulIEquiv_comp, inverse_equiv_comp,
    ← Complex.toContinuousLinearEquiv_smulILinearIsometryEquiv,
    ← LinearIsometryEquiv.toContinuousLinearEquiv_symm]
  exact L.inverse.opNorm_comp_linearIsometryEquiv (Complex.smulILinearIsometryEquiv X).symm

end ContinuousLinearMap

end
