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

On a complex normed space `X` with a compatible real scalar action (`IsScalarTower ℝ ℂ X`),
multiplication by `i` preserves norms because `‖i‖ = 1`. Upgrading `Complex.smulIEquiv` to a real
linear isometry equivalence (`Complex.smulILinearIsometryEquiv`) shows that multiplying a continuous
real-linear operator `L : Y →L[ℝ] X` on the left by `i` preserves the operator norm of its
totalized inverse (`ContinuousLinearMap.norm_inverse_I_smul`), as needed when passing between a
first-order ODE operator `L` and the rotated self-adjoint operator `i • L`.

## Main definitions and results

* `Complex.smulILinearIsometryEquiv`: multiplication by `i` as a real linear isometry equivalence
  `X ≃ₗᵢ[ℝ] X`, with `smulILinearIsometryEquiv_apply` and `smulILinearIsometryEquiv_symm_apply`.
* `ContinuousLinearMap.norm_inverse_I_smul`: `‖(Complex.I • L).inverse‖ = ‖L.inverse‖` for a
  continuous real-linear operator `L : Y →L[ℝ] X`.
-/

public section

namespace Complex

variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℂ X]
  [IsScalarTower ℝ ℂ X]

/-- Multiplication by `i` as a real linear isometry equivalence of a complex normed space with a
compatible real scalar action. -/
noncomputable def smulILinearIsometryEquiv : X ≃ₗᵢ[ℝ] X :=
  ⟨(smulIEquiv X).toLinearEquiv, fun x ↦ by simp [norm_smul]⟩

variable {X}

/-- `Complex.smulILinearIsometryEquiv` acts by scalar multiplication by `I`. -/
@[simp]
theorem smulILinearIsometryEquiv_apply (x : X) : smulILinearIsometryEquiv X x = I • x :=
  smulIEquiv_apply x

/-- The inverse of `Complex.smulILinearIsometryEquiv` acts by scalar multiplication by `-I`. -/
@[simp]
theorem smulILinearIsometryEquiv_symm_apply (x : X) :
    (smulILinearIsometryEquiv X).symm x = -I • x :=
  smulIEquiv_symm_apply x

/-- Forgetting the isometry property of `Complex.smulILinearIsometryEquiv` recovers
`Complex.smulIEquiv`. -/
@[simp]
theorem toContinuousLinearEquiv_smulILinearIsometryEquiv :
    (smulILinearIsometryEquiv X).toContinuousLinearEquiv = smulIEquiv X := by
  ext x
  simp

end Complex

namespace ContinuousLinearMap

/-- Multiplying a continuous real-linear operator into a complex normed space by `I` preserves the
operator norm of its totalized inverse. -/
@[simp]
theorem norm_inverse_I_smul {X Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedSpace ℂ X] [IsScalarTower ℝ ℂ X]
    (L : Y →L[ℝ] X) :
    ‖(Complex.I • L).inverse‖ = ‖L.inverse‖ := by
  rw [← Complex.smulIEquiv_comp, inverse_equiv_comp,
    ← Complex.toContinuousLinearEquiv_smulILinearIsometryEquiv,
    ← LinearIsometryEquiv.toContinuousLinearEquiv_symm]
  exact L.inverse.opNorm_comp_linearIsometryEquiv (Complex.smulILinearIsometryEquiv X).symm

end ContinuousLinearMap

end
