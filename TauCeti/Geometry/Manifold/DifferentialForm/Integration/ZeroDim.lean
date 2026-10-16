/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import Mathlib.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# Direct integration of zero-dimensional forms

A zero-dimensional chart contains one point. Its normalized basis Haar measure has mass one,
so the actual oriented chart integral is the value at that point times its orientation sign.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold

namespace TauCeti

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 0)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 0)) 1 M]

local notation "E" => EuclideanSpace ℝ (Fin 0)

/-- A function supported in a singleton integrates to its value at that point multiplied by
the tangent orientation sign. Singleton support also supplies compactness. -/
theorem integralTopForm_ofFunction_zeroDim (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin 0))
    (g : M → ℝ) (x : M)
    (hs : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) (RoughForm.ofFunction 𝓘(ℝ, E) g)) ⊆ {x}) :
    integralTopForm o (RoughForm.ofFunction 𝓘(ℝ, E) g) =
      (Orientation.signBasis (o.orientationAt x)
        (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis : ℝ) * g x := by
  classical
  obtain ⟨l, rfl⟩ := o.exists_lift
  let b := (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis
  have hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ)
      (RoughForm.ofFunction 𝓘(ℝ, E) g)) :=
    isCompact_singleton.of_isClosed_subset (_root_.isClosed_tsupport _) hs
  have hi := (isSmoothForm_zeroDim (n := 0) g).integrableTopForm hc b
  rw [integralTopForm_eq_chartIntegral l _ hi x
    (by simpa only [extChartAt_source_zeroDim] using hs), l.chartIntegral_eq_integral _ b x]
  have ht (y : E) : y ∈ (extChartAt 𝓘(ℝ, E) x).target := by
    have h := mem_extChartAt_target (I := 𝓘(ℝ, E)) x
    rwa [Subsingleton.elim (extChartAt 𝓘(ℝ, E) x x) y] at h
  have hx (y : E) : (extChartAt 𝓘(ℝ, E) x).symm y = x := by
    have h := (extChartAt 𝓘(ℝ, E) x).map_target (ht y)
    rwa [extChartAt_source_zeroDim, mem_singleton_iff] at h
  have hcoef (y : E) :
      (RoughForm.ofFunction 𝓘(ℝ, E) g).signedInChartAt b x (fun z ↦ l.signAt x z) y =
        (l.signAt x x : ℝ) * g x := by
    rw [RoughForm.signedInChartAt_apply, dite_eq_left (ht y), RoughForm.inChartAt_ofFunction]
    simp only [hx, ContinuousAlternatingMap.constOfIsEmpty_apply]
  simp_rw [hcoef]
  rw [integral_const, measureReal_def, Module.Basis.addHaar_univ_of_isEmpty,
    ENNReal.toReal_one, one_smul,
    Manifold.Orientation.orientationAt_mk,
    Manifold.OrientationLift.orientationAt_eq, Manifold.OrientationLift.chartOrientation_eq_ite]
  by_cases hsign : l.sign x ⟨x, mem_chart_source E x⟩ = 1
  · simp only [hsign, ↓reduceIte]
    rw [Manifold.OrientationLift.signAt_of_mem _ (mem_chart_source E x), hsign]
    simp only [Units.val_one, Int.cast_one, one_mul]
    rfl
  · have hn : l.sign x ⟨x, mem_chart_source E x⟩ = -1 :=
      (Int.units_eq_one_or (l.sign x ⟨x, mem_chart_source E x⟩)).resolve_left hsign
    simp only [hsign, ↓reduceIte]
    rw [Manifold.OrientationLift.signAt_of_mem _ (mem_chart_source E x), hn]
    have he :
        (Orientation.signBasis (-l.modelOrientation)
          (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis : ℝ) =
        -(Orientation.signBasis l.modelOrientation b : ℝ) := by
      simpa only [b, Units.val_neg, Int.cast_neg] using
        congrArg (fun u : ℤˣ ↦ (u : ℝ)) (_root_.Orientation.signBasis_neg l.modelOrientation b)
    -- The orientation on the tangent fibre is definitionally the model orientation on E,
    -- but rw does not match their inferred module instances. Identify that fibre explicitly.
    change _ = (Orientation.signBasis (-l.modelOrientation) b : ℝ) * g x
    rw [he]
    simp only [Units.val_neg, Units.val_one, Int.cast_neg, Int.cast_one, neg_one_mul]
    ring

/-- On a finite zero-dimensional manifold the actual integral is the signed sum of values.
The signs come from its tangent orientations, and the point masses are normalized to one. -/
theorem integralTopForm_ofFunction_finite_zeroDim [Fintype M]
    (o : Manifold.Orientation 𝓘(ℝ, E) M (Fin 0)) (g : M → ℝ) :
    integralTopForm o (RoughForm.ofFunction 𝓘(ℝ, E) g) =
      ∑ x : M, (Orientation.signBasis (o.orientationAt x)
        (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis : ℝ) * g x := by
  classical
  have : T1Space M := ChartedSpace.t1Space E M
  let δ : M → RoughForm 𝓘(ℝ, E) M ℝ 0 := fun x ↦
    RoughForm.ofFunction 𝓘(ℝ, E) (fun y ↦ if y = x then g x else 0)
  have hs (x : M) : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) (δ x)) ⊆ {x} := by
    apply closure_minimal _ isClosed_singleton
    intro y hy
    by_contra hn
    have hne : y ≠ x := by simpa only [mem_singleton_iff] using hn
    apply hy
    ext v
    simp [δ, RoughForm.ofFunction_apply, hne]
    rfl
  have hc (x : M) : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) (δ x)) :=
    isCompact_singleton.of_isClosed_subset
    (_root_.isClosed_tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) _) (hs x)
  have hi (x : M) : IntegrableTopForm (δ x) :=
    (isSmoothForm_zeroDim (n := 0) _).integrableTopForm (hc x)
      (EuclideanSpace.basisFun (Fin 0) ℝ).toBasis
  have he : RoughForm.ofFunction 𝓘(ℝ, E) g = ∑ x : M, δ x := by
    ext y v
    simp [δ, RoughForm.ofFunction_apply, Finset.sum_apply,
      ContinuousAlternatingMap.sum_apply]
  rw [he, integralTopForm_sum o δ Finset.univ (fun x _ ↦ hi x)]
  apply Finset.sum_congr rfl
  intro x _
  have h := integralTopForm_ofFunction_zeroDim o
    (fun y ↦ if y = x then g x else 0) x (hs x)
  simpa only [δ, ite_true] using h

end TauCeti
