/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.Module
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.Module.Complement
import Mathlib.Tactic.Module

/-!
# Multiplication by `i` on complex modules

Multiplication by `i` is a real continuous linear automorphism of any complex module with a
compatible real scalar action (`IsScalarTower ℝ ℂ X`) and continuous multiplication by constant
scalars, with inverse multiplication by `-i`. It is the conjugating operator by which complex
linearity of a real-linear map is tested: a continuous real-linear map between complex modules that
commutes with it is continuous complex-linear. Averaging over multiplication by `i` likewise turns
a continuous real-linear projection onto a complex submodule into a complex-linear one, so a
complex submodule complemented over the reals is complemented over the complex numbers.

## Main definitions and results

* `Complex.smulIEquiv`: multiplication by `i` as a real continuous linear equivalence, with
  `smulIEquiv_apply` and `smulIEquiv_symm_apply`.
* `ContinuousLinearMap.complexOfMapISmul`: a continuous real-linear map between complex modules
  that commutes with multiplication by `i`, as a continuous complex-linear map.
* `Submodule.ClosedComplemented.of_restrictScalars`: a complex submodule with a continuous
  real-linear projection onto it has a continuous complex-linear one.
-/

public section

namespace Complex

variable (X : Type*) [AddCommGroup X] [TopologicalSpace X] [Module ℝ X] [Module ℂ X]
  [IsScalarTower ℝ ℂ X] [ContinuousConstSMul ℂ X]

/-- Multiplication by `i` as a real continuous linear equivalence of a complex module with a
compatible real scalar action and continuous multiplication by constant scalars. -/
noncomputable def smulIEquiv : X ≃L[ℝ] X :=
  ContinuousLinearEquiv.smulLeft (Units.mk0 I I_ne_zero)

variable {X}

@[simp]
theorem smulIEquiv_apply (x : X) : smulIEquiv X x = I • x := by
  simp [smulIEquiv, Units.smul_def]

@[simp]
theorem smulIEquiv_symm_apply (x : X) : (smulIEquiv X).symm x = -I • x := by
  rw [ContinuousLinearEquiv.symm_apply_eq, smulIEquiv_apply, I_smul_neg_I_smul]

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

section ClosedComplemented

open Complex

variable {V : Type*} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [Module ℝ V]
  [Module ℂ V] [IsScalarTower ℝ ℂ V] [ContinuousConstSMul ℂ V]

/-- **Complex complements from real ones.** A complex submodule `K` that is the range of a
continuous real-linear projection `P` is the range of a continuous complex-linear projection,
the average `x ↦ (P x - i • P (i • x)) / 2` of `P` over multiplication by `i`. -/
theorem Submodule.ClosedComplemented.of_restrictScalars {K : Submodule ℂ V}
    (hK : (K.restrictScalars ℝ).ClosedComplemented) : K.ClosedComplemented := by
  obtain ⟨P, hP⟩ := hK
  -- `P` lands in `K.restrictScalars ℝ`, whose carrier is definitionally that of `K`, so `P` is
  -- retyped as a map into `K` by definitional unfolding.
  let P' : V →L[ℝ] K := P
  have hP' (x : K) : P' x = x := hP x
  -- `R x = P x - i • P (i • x)` commutes with `i`, and `R x = 2 x` on `K`.
  let R : V →L[ℝ] K := P' - (smulIEquiv K : K →L[ℝ] K) ∘L P' ∘L (smulIEquiv V : V →L[ℝ] V)
  have hR (v : V) : R v = P' v - I • P' (I • v) := by simp [R]
  have hRI (v : V) : R (I • v) = I • R v := by
    have hIIv : P' (I • I • v) = -P' v := by rw [smul_smul, I_mul_I, neg_one_smul, map_neg]
    rw [hR, hR, hIIv]
    match_scalars <;> simp [I_mul_I]
  refine ⟨(2⁻¹ : ℂ) • R.complexOfMapISmul hRI, fun x ↦ ?_⟩
  have hIx : P' (I • (x : V)) = I • x := hP' (I • x)
  rw [smul_apply, ContinuousLinearMap.coe_complexOfMapISmul, hR, hP', hIx]
  match_scalars
  norm_num [I_mul_I]

end ClosedComplemented

end
