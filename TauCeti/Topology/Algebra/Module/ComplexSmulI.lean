/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Algebra.Module.Equiv.Basic

/-!
# Multiplication by `i` on complex modules

Multiplication by `i` is a real continuous linear automorphism of any complex module with a
compatible real scalar action (`IsScalarTower ℝ ℂ X`) and continuous multiplication by constant
scalars, with inverse multiplication by `-i`. It is the conjugating operator by which complex
linearity of a real-linear map is tested: a continuous real-linear map between complex modules that
commutes with it is continuous complex-linear.

## Main definitions and results

* `Complex.smulIEquiv`: multiplication by `i` as a real continuous linear equivalence, with
  `smulIEquiv_apply` and `smulIEquiv_symm_apply`.
* `ContinuousLinearMap.complexOfMapISmul`: a continuous real-linear map between complex modules
  that commutes with multiplication by `i`, as a continuous complex-linear map.
-/

public section

namespace Complex

variable (X : Type*) [AddCommGroup X] [TopologicalSpace X] [Module ℝ X] [Module ℂ X]
  [IsScalarTower ℝ ℂ X] [ContinuousConstSMul ℂ X]

/-- Multiplication by `i` as a real continuous linear equivalence of a complex module with a
compatible real scalar action and continuous multiplication by constant scalars. -/
noncomputable def smulIEquiv : X ≃L[ℝ] X where
  toFun x := I • x
  map_add' := smul_add I
  map_smul' r x := smul_comm I r x
  invFun x := -I • x
  left_inv := neg_I_smul_I_smul
  right_inv := I_smul_neg_I_smul
  continuous_toFun := continuous_const_smul I
  continuous_invFun := continuous_const_smul (-I)

variable {X}

@[simp]
theorem smulIEquiv_apply (x : X) : smulIEquiv X x = I • x := (rfl)

@[simp]
theorem smulIEquiv_symm_apply (x : X) : (smulIEquiv X).symm x = -I • x := (rfl)

end Complex

section ComplexOfMapISmul

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [Module ℂ V] [IsScalarTower ℝ ℂ V]
  [AddCommGroup W] [Module ℝ W] [Module ℂ W] [IsScalarTower ℝ ℂ W]

namespace ContinuousLinearMap

variable [TopologicalSpace V] [TopologicalSpace W]

/-- A continuous real-linear map between complex modules that commutes with multiplication by
`I`, as a continuous complex-linear map. -/
def complexOfMapISmul (u : V →L[ℝ] W) (h : ∀ v, u (Complex.I • v) = Complex.I • u v) :
    V →L[ℂ] W :=
  ⟨u.toLinearMap.complexOfMapISmul h, by
    simpa only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.coe_complexOfMapISmul]
      using u.cont⟩

@[simp]
theorem coe_complexOfMapISmul (u : V →L[ℝ] W) (h : ∀ v, u (Complex.I • v) = Complex.I • u v) :
    ⇑(u.complexOfMapISmul h) = u :=
  u.toLinearMap.coe_complexOfMapISmul h

@[simp]
theorem restrictScalars_complexOfMapISmul (u : V →L[ℝ] W)
    (h : ∀ v, u (Complex.I • v) = Complex.I • u v) :
    (u.complexOfMapISmul h).restrictScalars ℝ = u :=
  ContinuousLinearMap.ext fun v ↦ congrFun (coe_complexOfMapISmul u h) v

end ContinuousLinearMap


end ComplexOfMapISmul

end
