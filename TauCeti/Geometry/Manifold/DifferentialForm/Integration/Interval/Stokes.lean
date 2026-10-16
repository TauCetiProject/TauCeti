/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Interval.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ZeroDim
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The fundamental theorem of calculus as interval Stokes

The actual exterior derivative of a function on a closed interval integrates to its endpoint
difference. Stokes identifies this with the integral over its outward-oriented zero-dimensional
boundary. Direct zero-dimensional integration separately verifies the endpoint signs,
without using Stokes, for arbitrary functions on the two-point boundary.
-/

public section

noncomputable section

open Set Fact.Manifold MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {a b : ℝ} [hab : Fact (a < b)]

private theorem interval_function_derivative (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    mextDeriv (RoughForm.ofFunction (𝓡∂ 1) (fun t : Icc a b ↦ f t)) =
      mpullback (𝓡∂ 1) 𝓘(ℝ) Subtype.val (mextDeriv (RoughForm.ofFunction 𝓘(ℝ) f)) := by
  ext t v
  rw [mextDeriv_ofFunction, mpullback_apply, mextDeriv_ofFunction]
  change mvfderiv (𝓡∂ 1) (fun t : Icc a b ↦ f t) t (v 0) =
    mvfderiv 𝓘(ℝ) f (t : ℝ) (mfderiv (𝓡∂ 1) 𝓘(ℝ) Subtype.val t (v 0))
  exact mvfderiv_comp_apply t (hf.contMDiff.mdifferentiable one_ne_zero _)
    ((contMDiff_subtypeVal_Icc (x := a) (y := b) (n := 1)).mdifferentiable one_ne_zero _) (v 0)

/-- The integral of the actual exterior derivative of a C1 real function on an increasing
closed interval is its endpoint difference. -/
theorem integralTopForm_mextDeriv_ofFunction_Icc (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) :
    IntegrableTopForm
      (mextDeriv (RoughForm.ofFunction (𝓡∂ 1) (fun t : Icc a b ↦ f t))) ∧
      integralTopForm (Manifold.Orientation.interval a b)
        (mextDeriv (RoughForm.ofFunction (𝓡∂ 1) (fun t : Icc a b ↦ f t))) = f b - f a := by
  let η := mextDeriv (RoughForm.ofFunction 𝓘(ℝ) f)
  have he (t : ℝ) : η t (fun _ ↦ (1 : TangentSpace 𝓘(ℝ) t)) = deriv f t := by
    change mextDeriv (RoughForm.ofFunction 𝓘(ℝ) f) t _ = _
    rw [mextDeriv_ofFunction]
    change mvfderiv 𝓘(ℝ) f t (1 : TangentSpace 𝓘(ℝ) t) = deriv f t
    rw [mvfderiv_eq_fderiv]
    change fderiv ℝ f t (1 : ℝ) = deriv f t
    exact fderiv_apply_one_eq_deriv
  have hi : IntervalIntegrable (fun t ↦ η t (fun _ ↦ 1)) volume a b := by
    simpa only [he] using hf.continuous_deriv (by simp) |>.intervalIntegrable a b
  have h := integralTopForm_mpullback_subtypeVal_Icc η hi
  rw [← interval_function_derivative f hf] at h
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [he]
  exact intervalIntegral.integral_deriv_eq_sub (fun _ _ ↦ hf.differentiable one_ne_zero _)
    ((hf.continuous_deriv (by simp)).intervalIntegrable a b)

attribute [local instance] intervalSuccessorChartedSpace intervalBoundaryChartedSpace

local instance : IsManifold (𝓡∂ (0 + 1)) ∞ (Icc a b) := instIsManifoldIcc a b


local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) 1
    ((𝓡∂ (0 + 1)).boundary (Icc a b)) := isManifold_boundary (n := 0) (Icc a b) one_ne_zero

/-- Direct integration over the zero-dimensional interval boundary: its right endpoint has
mass +1 and its left endpoint mass -1. No regularity of the endpoint function is needed. -/
theorem integralTopForm_ofFunction_boundary_Icc
    (g : (𝓡∂ (0 + 1)).boundary (Icc a b) → ℝ) :
    integralTopForm (boundaryOrientation (n := 0) (Manifold.Orientation.interval a b))
      (RoughForm.ofFunction 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) g) =
      g ⟨⊤, Icc_isBoundaryPoint_top⟩ - g ⟨⊥, Icc_isBoundaryPoint_bot⟩ := by
  classical
  let L : (𝓡∂ (0 + 1)).boundary (Icc a b) := ⟨⊥, Icc_isBoundaryPoint_bot⟩
  let R : (𝓡∂ (0 + 1)).boundary (Icc a b) := ⟨⊤, Icc_isBoundaryPoint_top⟩
  have hpoints (x : (𝓡∂ (0 + 1)).boundary (Icc a b)) : x = L ∨ x = R := by
    have hx := x.property
    change x.val ∈ (𝓡∂ 1).boundary (Icc a b) at hx
    have he : (𝓡∂ 1).boundary (Icc a b) = {⊥, ⊤} := boundary_Icc
    have hx' : x.val ∈ ({⊥, ⊤} : Set (Icc a b)) := he ▸ hx
    rcases hx' with hx | hx
    · exact Or.inl (Subtype.ext hx)
    · exact Or.inr (Subtype.ext hx)
  let : Fintype ((𝓡∂ (0 + 1)).boundary (Icc a b)) :=
    ⟨{L, R}, by intro x; simpa using hpoints x⟩
  have hne : L ≠ R := by
    intro he
    have h := congrArg (fun x : (𝓡∂ (0 + 1)).boundary (Icc a b) ↦ (x.val : ℝ)) he
    exact hab.out.ne h
  have hu : (Finset.univ : Finset ((𝓡∂ (0 + 1)).boundary (Icc a b))) = {L, R} := by
    ext x
    simpa using hpoints x
  let B := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis
  rw [integralTopForm_ofFunction_finite_zeroDim (b := B), hu, Finset.sum_pair hne]
  have hp : (Orientation.signBasis B.orientation B : ℝ) = 1 := by
    rw [_root_.Orientation.signBasis_orientation]
    norm_num
  have hn : (Orientation.signBasis (-B.orientation) B : ℝ) = -1 := by
    rw [_root_.Orientation.signBasis_neg, _root_.Orientation.signBasis_orientation]
    norm_num
  simp only [L, R, orientationAt_boundaryOrientation_interval_left,
    orientationAt_boundaryOrientation_interval_right]
  change (Orientation.signBasis (-B.orientation) B : ℝ) * g L +
    (Orientation.signBasis B.orientation B : ℝ) * g R = g R - g L
  rw [hp, hn]
  ring

/-- The actual canonical outward-boundary integral on a closed interval is the right endpoint
value minus the left endpoint value, directly by zero-dimensional integration. -/
theorem integralTopForm_boundaryRestriction_ofFunction_Icc (f : ℝ → ℝ) :
    integralTopForm (boundaryOrientation (n := 0) (Manifold.Orientation.interval a b))
      (boundaryRestriction (RoughForm.ofFunction (𝓡∂ 1) (fun t : Icc a b ↦ f t))) =
      f b - f a := by
  have he : boundaryRestriction (RoughForm.ofFunction (𝓡∂ 1)
      (fun t : Icc a b ↦ f t)) =
      RoughForm.ofFunction 𝓘(ℝ, EuclideanSpace ℝ (Fin 0))
        (fun x : (𝓡∂ (0 + 1)).boundary (Icc a b) ↦ f x.val) := by
    ext x v
    rw [boundaryRestriction_apply, RoughForm.ofFunction_apply, RoughForm.ofFunction_apply]
  rw [he, integralTopForm_ofFunction_boundary_Icc]
  rfl

end TauCeti
