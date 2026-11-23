/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
public import TauCeti.LinearAlgebra.Complex.Module

/-!
# Multiplication by `i` on complex modules

Multiplication by `i` is a real continuous linear automorphism of any complex module with a
compatible real scalar action (`IsScalarTower ℝ ℂ X`) and continuous multiplication by constant
scalars, with inverse multiplication by `-i`. It is the conjugating operator by which complex
linearity of a real-linear map is tested: a continuous real-linear map between complex modules that
commutes with it is continuous complex-linear, and post-composing any continuous real-linear map
with multiplication by `i` preserves invertibility.

## Main definitions and results

* `Complex.smulIEquiv`: multiplication by `i` as a real continuous linear equivalence, with
  `smulIEquiv_apply`, `smulIEquiv_symm_apply`, and `smulIEquiv_comp`.
* `ContinuousLinearMap.isInvertible_I_smul_iff`: `(Complex.I • L).IsInvertible ↔ L.IsInvertible`
  for a continuous real-linear map `L : Y →L[ℝ] X`.
* `ContinuousLinearMap.complexOfMapISmul`: a continuous real-linear map between complex modules
  that commutes with multiplication by `i`, as a continuous complex-linear map.
* `ContinuousLinearMap.commute_I_smul_one_iff`: a continuous real-linear endomorphism commutes
  with the operator `I • 1` exactly when it commutes with multiplication by `i` on vectors.
* `ContinuousLinearEquiv.complexOfMapISmul`: the corresponding conversion of continuous
  real-linear equivalences, preserving their forward and inverse maps.
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

/-- Post-composing a continuous real-linear map with `Complex.smulIEquiv` multiplies it by `I`. -/
@[simp]
theorem smulIEquiv_comp {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [Module ℝ Y]
    (L : Y →L[ℝ] X) :
    (smulIEquiv X : X →L[ℝ] X).comp L = I • L := by
  ext y
  simp

end Complex

namespace ContinuousLinearMap

/-- Multiplying a continuous real-linear map into a complex module by `I` preserves
invertibility. -/
@[simp]
theorem isInvertible_I_smul_iff {X Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [Module ℝ Y]
    [AddCommGroup X] [TopologicalSpace X] [Module ℝ X] [Module ℂ X] [IsScalarTower ℝ ℂ X]
    [ContinuousConstSMul ℂ X] (L : Y →L[ℝ] X) :
    (Complex.I • L).IsInvertible ↔ L.IsInvertible := by
  rw [← Complex.smulIEquiv_comp, isInvertible_equiv_comp]

end ContinuousLinearMap

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

/-- A continuous real-linear endomorphism commutes with multiplication by `I` as an operator
exactly when it commutes with `I` on vectors. -/
theorem commute_I_smul_one_iff [ContinuousConstSMul ℂ V] {A : V →L[ℝ] V} :
    Commute (Complex.I • (1 : V →L[ℝ] V)) A ↔ ∀ v, A (Complex.I • v) = Complex.I • A v := by
  simp [Commute, SemiconjBy, ContinuousLinearMap.ext_iff, eq_comm]

end ContinuousLinearMap

namespace ContinuousLinearEquiv

variable [TopologicalSpace V] [TopologicalSpace W]

/-- A continuous real-linear equivalence commuting with multiplication by `I`, viewed as a
continuous complex-linear equivalence with the same forward and inverse maps. -/
def complexOfMapISmul (e : V ≃L[ℝ] W)
    (h : ∀ v, e (Complex.I • v) = Complex.I • e v) : V ≃L[ℂ] W where
  toEquiv := e.toEquiv
  map_add' := e.map_add
  map_smul' c v := by
    let u := e.toContinuousLinearMap.complexOfMapISmul h
    have hu (v : V) : u v = e v :=
      congrFun (ContinuousLinearMap.coe_complexOfMapISmul e.toContinuousLinearMap h) v
    -- `toEquiv := e.toEquiv` fixes the forward map to `e`. The promoted CLM has an
    -- opaque linear-map constructor, so its explicit coercion law `hu` is needed to
    -- transfer the scalar identity to this equivalence field.
    change e (c • v) = c • e v
    exact (hu _).symm.trans ((u.map_smul c v).trans (congrArg (c • ·) (hu v)))
  continuous_toFun := e.continuous
  continuous_invFun := e.symm.continuous

@[simp]
theorem complexOfMapISmul_apply (e : V ≃L[ℝ] W) (h) (v : V) :
    e.complexOfMapISmul h v = e v := by rfl

@[simp]
theorem complexOfMapISmul_symm_apply (e : V ≃L[ℝ] W) (h) (w : W) :
    (e.complexOfMapISmul h).symm w = e.symm w := by rfl

@[simp]
theorem restrictScalars_complexOfMapISmul (e : V ≃L[ℝ] W)
    (h : ∀ v, e (Complex.I • v) = Complex.I • e v) :
    (e.complexOfMapISmul h).toContinuousLinearMap.restrictScalars ℝ =
      e.toContinuousLinearMap := by
  ext v
  exact e.complexOfMapISmul_apply h v

end ContinuousLinearEquiv

end ComplexOfMapISmul

end
