/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
public import Mathlib.Analysis.Complex.Basic
public import TauCeti.Geometry.Symplectic.ComplexModuleHom
public import TauCeti.Geometry.Symplectic.JHolomorphic

/-!
# Complex differentiability and the standard almost complex structure

This file connects the map-level `J`-holomorphic predicate with ordinary complex
differentiability in the basic model case of complex normed spaces. A complex normed space has
the standard almost complex structure `AlmostComplexStructure.ofComplexModule`, where `J v = i • v`.
For these structures, a map is `J`-holomorphic exactly when its real Frechet derivative is
complex-linear; equivalently, by Mathlib's restrict-scalars calculus, it is complex differentiable.

The statements here are deliberately model-space statements. They are the chart-level bridge
needed by the analytic Heegaard Floer roadmap before the later manifold version of
`J`-holomorphicity is introduced.

## Main declarations

* `TauCeti.isComplexLinearMap_restrictScalars_ofComplexModule`: a complex-linear map, restricted
  to real scalars, intertwines the standard almost complex structures.
* `TauCeti.IsComplexLinearMap.toComplexContinuousLinearMap_ofComplexModule`: a continuous
  real-linear map intertwining the standard structures, repackaged as a complex continuous-linear
  map.
* `TauCeti.isJHolomorphicAt_ofComplexModule_iff_differentiableAt`: pointwise
  `J`-holomorphicity for the standard structures is complex differentiability.
* Within-set, setwise, and global variants of the same dictionary.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: for the standard complex structure on a complex vector space, the Cauchy--Riemann
condition on the real derivative is precisely complex-linearity.
-/

public section

namespace TauCeti

variable {V W : Type*}

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace ℂ V] [IsScalarTower ℝ ℂ V]
variable [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace ℂ W] [IsScalarTower ℝ ℂ W]

section Linear

private lemma complex_smul_eq_re_add_im (z : ℂ) (v : V) :
    z • v = z.re • v + z.im • (Complex.I • v) := by
  conv_lhs =>
    rw [← Complex.re_add_im z, add_smul, mul_smul]
  rw [← IsScalarTower.algebraMap_smul ℂ z.re v,
    ← IsScalarTower.algebraMap_smul ℂ z.im (Complex.I • v)]
  rw [Complex.coe_algebraMap]

/-- A complex-linear map, restricted to real scalars, intertwines the standard almost complex
structures `v ↦ i • v`. -/
lemma isComplexLinearMap_restrictScalars_ofComplexModule (F : V →ₗ[ℂ] W) :
    IsComplexLinearMap (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) (F.restrictScalars ℝ) := by
  refine (isComplexLinearMap_iff_apply _ _ _).mpr fun v => ?_
  simp [AlmostComplexStructure.ofComplexModule_apply, map_smul]

/-- A complex continuous-linear map, restricted to real scalars, intertwines the standard almost
complex structures `v ↦ i • v`. -/
lemma isComplexLinearMap_continuousLinearMap_restrictScalars_ofComplexModule (F : V →L[ℂ] W) :
    IsComplexLinearMap (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) (F.restrictScalars ℝ).toLinearMap :=
  isComplexLinearMap_restrictScalars_ofComplexModule F.toLinearMap

/-- A continuous real-linear map that intertwines the standard almost complex structures can be
regarded as a complex continuous-linear map. -/
@[expose] noncomputable def IsComplexLinearMap.toComplexContinuousLinearMap_ofComplexModule
    {F : V →L[ℝ] W}
    (hF : IsComplexLinearMap (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) F.toLinearMap) :
    V →L[ℂ] W where
  toFun := F
  map_add' := F.map_add
  map_smul' := by
    intro z v
    have hI : F (Complex.I • v) = Complex.I • F v := by
      have h := (isComplexLinearMap_iff_apply _ _ _).mp hF v
      simpa [AlmostComplexStructure.ofComplexModule_apply] using h
    have hcalc : F (z • v) = z • F v := by
      calc
        F (z • v) = F (z.re • v + z.im • (Complex.I • v)) := by
          rw [complex_smul_eq_re_add_im (V := V) z v]
        _ = z.re • F v + z.im • F (Complex.I • v) := by
          rw [map_add, map_smul, map_smul]
        _ = z.re • F v + z.im • (Complex.I • F v) := by
          rw [hI]
        _ = z • F v := by
          rw [complex_smul_eq_re_add_im (V := W) z (F v)]
    simpa using hcalc
  cont := F.cont

@[simp]
lemma IsComplexLinearMap.toComplexContinuousLinearMap_ofComplexModule_apply {F : V →L[ℝ] W}
    (hF : IsComplexLinearMap (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) F.toLinearMap) (v : V) :
    hF.toComplexContinuousLinearMap_ofComplexModule v = F v :=
  rfl

@[simp]
lemma IsComplexLinearMap.toComplexContinuousLinearMap_ofComplexModule_restrictScalars
    {F : V →L[ℝ] W}
    (hF : IsComplexLinearMap (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) F.toLinearMap) :
    hF.toComplexContinuousLinearMap_ofComplexModule.restrictScalars ℝ = F :=
  ContinuousLinearMap.ext fun _ => rfl

end Linear

section Differentiability

variable {f : V → W} {s : Set V} {x : V}

/-- Complex differentiability implies pointwise `J`-holomorphicity for the standard almost complex
structures on complex normed spaces. -/
lemma DifferentiableAt.isJHolomorphicAt_ofComplexModule (hf : DifferentiableAt ℂ f x) :
    IsJHolomorphicAt (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f x :=
  ⟨(fderiv ℂ f x).restrictScalars ℝ, hf.hasFDerivAt.restrictScalars ℝ,
    isComplexLinearMap_continuousLinearMap_restrictScalars_ofComplexModule (fderiv ℂ f x)⟩

/-- Pointwise `J`-holomorphicity for the standard almost complex structures is equivalent to
ordinary complex differentiability. -/
@[simp]
lemma isJHolomorphicAt_ofComplexModule_iff_differentiableAt :
    IsJHolomorphicAt (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f x ↔ DifferentiableAt ℂ f x := by
  constructor
  · intro hf
    refine ⟨hf.derivative_isComplexLinear.toComplexContinuousLinearMap_ofComplexModule, ?_⟩
    exact hasFDerivAt_of_restrictScalars ℝ hf.hasFDerivAt
      hf.derivative_isComplexLinear.toComplexContinuousLinearMap_ofComplexModule_restrictScalars
  · exact fun hf => DifferentiableAt.isJHolomorphicAt_ofComplexModule hf

/-- Complex differentiability within a set implies within-set `J`-holomorphicity for the standard
almost complex structures on complex normed spaces. -/
lemma DifferentiableWithinAt.isJHolomorphicWithinAt_ofComplexModule
    (hf : DifferentiableWithinAt ℂ f s x) :
    IsJHolomorphicWithinAt (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f s x :=
  ⟨(fderivWithin ℂ f s x).restrictScalars ℝ, hf.hasFDerivWithinAt.restrictScalars ℝ,
    isComplexLinearMap_continuousLinearMap_restrictScalars_ofComplexModule (fderivWithin ℂ f s x)⟩

/-- Within-set `J`-holomorphicity for the standard almost complex structures is equivalent to
ordinary complex differentiability within the set. -/
@[simp]
lemma isJHolomorphicWithinAt_ofComplexModule_iff_differentiableWithinAt :
    IsJHolomorphicWithinAt (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f s x ↔ DifferentiableWithinAt ℂ f s x := by
  constructor
  · intro hf
    refine ⟨hf.derivative_isComplexLinear.toComplexContinuousLinearMap_ofComplexModule, ?_⟩
    exact hf.hasFDerivWithinAt.of_restrictScalars ℝ
      hf.derivative_isComplexLinear.toComplexContinuousLinearMap_ofComplexModule_restrictScalars
  · exact fun hf => DifferentiableWithinAt.isJHolomorphicWithinAt_ofComplexModule hf

/-- Complex differentiability on a set implies `J`-holomorphicity on that set for the standard
almost complex structures. -/
lemma DifferentiableOn.isJHolomorphicOn_ofComplexModule (hf : DifferentiableOn ℂ f s) :
    IsJHolomorphicOn (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f s :=
  fun x hx => DifferentiableWithinAt.isJHolomorphicWithinAt_ofComplexModule (hf x hx)

/-- Setwise `J`-holomorphicity for the standard almost complex structures is equivalent to
ordinary complex differentiability on the set. -/
@[simp]
lemma isJHolomorphicOn_ofComplexModule_iff_differentiableOn :
    IsJHolomorphicOn (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f s ↔ DifferentiableOn ℂ f s :=
  ⟨fun hf x hx => (isJHolomorphicWithinAt_ofComplexModule_iff_differentiableWithinAt).mp
      (hf x hx),
    fun hf => DifferentiableOn.isJHolomorphicOn_ofComplexModule hf⟩

/-- Complex differentiability implies global `J`-holomorphicity for the standard almost complex
structures. -/
lemma Differentiable.isJHolomorphic_ofComplexModule (hf : Differentiable ℂ f) :
    IsJHolomorphic (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f :=
  fun x => DifferentiableAt.isJHolomorphicAt_ofComplexModule (hf x)

/-- Global `J`-holomorphicity for the standard almost complex structures is equivalent to ordinary
complex differentiability. -/
@[simp]
lemma isJHolomorphic_ofComplexModule_iff_differentiable :
    IsJHolomorphic (AlmostComplexStructure.ofComplexModule V)
      (AlmostComplexStructure.ofComplexModule W) f ↔ Differentiable ℂ f :=
  ⟨fun hf x => (isJHolomorphicAt_ofComplexModule_iff_differentiableAt).mp (hf x),
    fun hf => Differentiable.isJHolomorphic_ofComplexModule hf⟩

end Differentiability

end TauCeti
