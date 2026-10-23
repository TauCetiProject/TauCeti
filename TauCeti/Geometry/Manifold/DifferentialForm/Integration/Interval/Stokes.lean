/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Interval.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.ZeroDim
public import TauCeti.Geometry.Manifold.Boundary.Restriction
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The fundamental theorem of calculus as interval Stokes

The actual exterior derivative of a function on a closed interval integrates to its endpoint
difference, using the interval pullback identity and the ordinary fundamental theorem of
calculus. Direct zero-dimensional integration identifies the outward-oriented boundary integral
with the same endpoint difference, for arbitrary functions on the two-point boundary.
-/

public section

noncomputable section

open Set Fact.Manifold MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti

variable {a b : ℝ} [hab : Fact (a < b)]

/-- The integral of the actual exterior derivative of a function that is `C¹` on an increasing
closed interval is its endpoint difference. No regularity outside the interval is required. -/
theorem integralTopForm_mextDeriv_ofFunction_Icc (f : ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Icc a b)) :
    IntegrableTopForm
      (mextDeriv (RoughForm.ofFunction (𝓡∂ 1) (fun t : Icc a b ↦ f t))) ∧
      integralTopForm (Manifold.Orientation.interval a b)
        (mextDeriv (RoughForm.ofFunction (𝓡∂ 1) (fun t : Icc a b ↦ f t))) = f b - f a := by
  let η := mextDeriv (RoughForm.ofFunction 𝓘(ℝ) (id : ℝ → ℝ))
  have hη (t : ℝ) (v : Fin 1 → TangentSpace 𝓘(ℝ) t) :
      η t v = NormedSpace.fromTangentSpace (𝕜 := ℝ) t (v 0) := by
    dsimp only [η]
    rw [mextDeriv_ofFunction]
    simp [mvfderiv_eq_fderiv]
  have hi : IntervalIntegrable (deriv f) volume a b := by
    have hwithin := (hf.derivWithin (m := 0) (uniqueDiffOn_Icc hab.out) (by simp)).continuousOn
    apply (hwithin.intervalIntegrable_of_Icc (μ := volume) hab.out.le).congr_uIoo
    intro t ht
    rw [uIoo_of_le hab.out.le] at ht
    exact derivWithin_of_mem_nhds (Icc_mem_nhds ht.1 ht.2)
  have hp : IntervalIntegrable (fun t ↦ η (f t)
      (fun _ ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (f t)).symm (deriv f t))) volume a b := by
    simpa only [hη, ContinuousLinearEquiv.apply_symm_apply] using hi
  have h := integralTopForm_mpullback_curve_Icc η f hf hp
  have he : mpullback (𝓡∂ 1) 𝓘(ℝ) (fun t : Icc a b ↦ f t) η =
      mextDeriv (RoughForm.ofFunction (𝓡∂ 1) (fun t : Icc a b ↦ f t)) := by
    ext t v
    rw [mpullback_apply, hη, mextDeriv_ofFunction]
    rfl
  rw [he] at h
  refine ⟨h.1, h.2.trans ?_⟩
  simp only [hη, ContinuousLinearEquiv.apply_symm_apply]
  exact intervalIntegral.integral_deriv_of_contDiffOn_Icc hf hab.out.le

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
    -- Normalize 0 + 1 to 1 in the boundary model before using the interval endpoint set.
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
  -- Expose the chosen empty basis B and the endpoint abbreviations L and R.
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
