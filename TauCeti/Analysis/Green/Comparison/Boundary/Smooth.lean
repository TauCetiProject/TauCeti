/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.Boundary.Basic
public import TauCeti.Analysis.Green.Comparison.Regularity
public import TauCeti.Analysis.Green.Comparison.PullbackExteriorDerivative
public import TauCeti.Geometry.Manifold.DifferentialForm.SmoothPartition
import Mathlib.Topology.Compactness.SigmaCompact

import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Stokes

/-!
# Global circulation on an actual smooth boundary

Stokes for the actual outward-first boundary orientation becomes a finite sum of real
parametrized circulation integrals. An actual smooth partition localizes the restricted form
in boundary charts with constant orientation signs. Both intrinsic integrability predicates
and the integrability of every real chart coefficient are conclusions.
-/

public section

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff

namespace TauCeti.Green

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (1 + 1)) M]
  [IsManifold (𝓡∂ (1 + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M]

local instance smoothBoundaryIsManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ∞
    ((𝓡∂ (1 + 1)).boundary M) := isManifold_boundary M (by simp)

local instance smoothBoundarySigmaCompactSpace : SigmaCompactSpace ((𝓡∂ (1 + 1)).boundary M) :=
  ((𝓡∂ (1 + 1)).isClosed_boundary (by simp : (∞ : ℕ∞ω) ≠ 0)).sigmaCompactSpace

/-- A compact C1 pulled-back circulation form satisfies the actual global Stokes formula,
expressed as finitely many weighted real boundary-chart circulations. The chart signs and model
orientation are those of the induced outward-first boundary lift, including all components. -/
theorem exists_boundary_chart_circulation
    (l : Manifold.OrientationLift (𝓡∂ (1 + 1)) M (Fin (1 + 1)))
    (P Q : ℂ → ℝ) (f : M → ℂ) (hf : MDifferentiable (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f)
    (hφ : IsSmoothForm (𝓡∂ (1 + 1)) 1
      (mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)))
    (hc : IsCompact (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 2)) [⋀^Fin _]→L[ℝ] ℝ)
    (mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)))) :
    let φ := mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)
    let γ := fun α : (𝓡∂ (1 + 1)).boundary M ↦ fun t : ℝ ↦
      f ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
        ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t)))
    let A := fun α : (𝓡∂ (1 + 1)).boundary M ↦
      {t : ℝ | (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t) ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).target}
    IntegrableTopForm (mextDeriv φ) ∧ IntegrableTopForm (boundaryRestriction φ) ∧
      ∃ s : Finset ((𝓡∂ (1 + 1)).boundary M),
        ∃ ρ : SmoothPartitionOfUnity ((𝓡∂ (1 + 1)).boundary M)
          𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ((𝓡∂ (1 + 1)).boundary M) univ,
          boundaryRestriction φ = ∑ α ∈ s, (fun x ↦ ρ α x • boundaryRestriction φ x) ∧
          (∀ α ∈ s, IntegrableOn (fun t ↦
            ρ α ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
              ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))) *
                circulationFun P Q (γ α) t) (A α)) ∧
          integralTopForm (Manifold.Orientation.mk l) (mextDeriv φ) =
            ∑ α ∈ s,
              (Orientation.signBasis l.boundary.modelOrientation
                (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis : ℝ) *
                (l.boundary.signAt α α : ℝ) * ∫ t in A α,
                  ρ α ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
                    ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))) *
                      circulationFun P Q (γ α) t := by
  classical
  let φ := mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)
  let g : (𝓡∂ (1 + 1)).boundary M → ℂ := fun x ↦ f x
  have hinc : MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) (𝓡∂ (1 + 1))
      (Subtype.val : (𝓡∂ (1 + 1)).boundary M → M) :=
    (isSmoothEmbedding_subtypeVal_boundary M (by simp : (∞ : ℕ∞ω) ≠ 0)).contMDiff
      |>.mdifferentiable (by simp)
  have hg : MDifferentiable 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) g := hf.comp hinc
  have he : boundaryRestriction φ =
      mpullback 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) 𝓘(ℝ, ℂ) g (manifoldOneForm P Q) := by
    exact boundaryRestriction_mpullback hf (manifoldOneForm P Q)
  have hb := hφ.boundaryRestriction
  have hcb := isCompact_tsupport_boundaryRestriction hc
  have hi := hφ.continuous_mextDeriv.integrableTopForm
    (RoughForm.isCompact_tsupport_mextDeriv hc)
    (EuclideanSpace.basisFun (Fin (1 + 1)) ℝ).toBasis
  have hib := hb.integrableTopForm hcb (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
  obtain ⟨s, ρ, hsum, hp⟩ :=
    (boundaryRestriction φ).exists_finset_smooth_partition_in_charts l.boundary hb hcb
  let ψ := fun α : (𝓡∂ (1 + 1)).boundary M ↦
    (fun x ↦ ρ α x • boundaryRestriction φ x :
      RoughForm 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ((𝓡∂ (1 + 1)).boundary M) ℝ 1)
  have hiψ : ∀ α ∈ s, IntegrableTopForm (ψ α) := fun α hα ↦
    (hp α hα).1.integrableTopForm (hp α hα).2.1
      (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis
  have hlocal (α : (𝓡∂ (1 + 1)).boundary M) (hα : α ∈ s) :=
    integralTopForm_weighted_mpullback_chart l.boundary P Q g hg (ρ α) α
      (l.boundary.signAt α α) (fun _ ↦ rfl)
      (by simpa only [ψ, he] using hiψ α hα)
      (by simpa only [ψ, he, extChartAt_source] using (hp α hα).2.2.1)
      (by simpa only [ψ, he] using (hp α hα).2.2.2.1)
  refine ⟨hi, hib, s, ρ, hsum, fun α hα ↦ (hlocal α hα).1, ?_⟩
  rw [integralTopForm_mextDeriv (Manifold.Orientation.mk l) hφ hc,
    boundaryOrientation_mk, hsum, integralTopForm_sum _ ψ s hiψ]
  apply Finset.sum_congr rfl
  intro α hα
  simpa only [ψ, he] using (hlocal α hα).2

/-- Global Green on an actual smooth boundary identifies the intrinsic area integral with
finite boundary-chart circulations. The area form is the actual pullback of normalized complex
area, weighted by curl; its integrability follows from the pulled-back form's C1 regularity. -/
theorem exists_curl_area_boundary_chart_circulation
    (l : Manifold.OrientationLift (𝓡∂ (1 + 1)) M (Fin (1 + 1)))
    (P Q : ℂ → ℝ) (f : M → ℂ) (hf : ContMDiff (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) 2 f)
    (hP : ∀ x, DifferentiableAt ℝ P (f x)) (hQ : ∀ x, DifferentiableAt ℝ Q (f x))
    (hφ : IsSmoothForm (𝓡∂ (1 + 1)) 1
      (mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)))
    (hc : IsCompact (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 2)) [⋀^Fin _]→L[ℝ] ℝ)
    (mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)))) :
    let φ := mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)
    let area := fun x ↦ curl P Q (f x) •
      mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f manifoldAreaForm x
    let γ := fun α : (𝓡∂ (1 + 1)).boundary M ↦ fun t : ℝ ↦
      f ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
        ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t)))
    let A := fun α : (𝓡∂ (1 + 1)).boundary M ↦
      {t : ℝ | (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t) ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).target}
    IntegrableTopForm area ∧ IntegrableTopForm (boundaryRestriction φ) ∧
      ∃ s : Finset ((𝓡∂ (1 + 1)).boundary M),
        ∃ ρ : SmoothPartitionOfUnity ((𝓡∂ (1 + 1)).boundary M)
          𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ((𝓡∂ (1 + 1)).boundary M) univ,
          boundaryRestriction φ = ∑ α ∈ s, (fun x ↦ ρ α x • boundaryRestriction φ x) ∧
          (∀ α ∈ s, IntegrableOn (fun t ↦
            ρ α ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
              ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))) *
                circulationFun P Q (γ α) t) (A α)) ∧
          integralTopForm (Manifold.Orientation.mk l) area =
            ∑ α ∈ s,
              (Orientation.signBasis l.boundary.modelOrientation
                (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis : ℝ) *
                (l.boundary.signAt α α : ℝ) * ∫ t in A α,
                  ρ α ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
                    ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))) *
                      circulationFun P Q (γ α) t := by
  have h := exists_boundary_chart_circulation l P Q f (hf.mdifferentiable (by norm_num)) hφ hc
  have he := ContMDiff.mextDeriv_mpullback_manifoldOneForm hf hP hQ
  simpa only [he] using h

/-- On a compact smooth manifold with boundary the comparison follows directly from real
C1 planar coefficients and a C2 map. Form regularity, support compactness, and both intrinsic
integrabilities are derived rather than supplied as premises. -/
theorem exists_curl_area_boundary_chart_circulation_of_compactSpace [CompactSpace M]
    (l : Manifold.OrientationLift (𝓡∂ (1 + 1)) M (Fin (1 + 1)))
    (P Q : ℂ → ℝ) (f : M → ℂ) (hf : ContMDiff (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) 2 f)
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    let φ := mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)
    let area := fun x ↦ curl P Q (f x) •
      mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f manifoldAreaForm x
    let γ := fun α : (𝓡∂ (1 + 1)).boundary M ↦ fun t : ℝ ↦
      f ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
        ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t)))
    let A := fun α : (𝓡∂ (1 + 1)).boundary M ↦
      {t : ℝ | (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t) ∈
        (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).target}
    IntegrableTopForm area ∧ IntegrableTopForm (boundaryRestriction φ) ∧
      ∃ s : Finset ((𝓡∂ (1 + 1)).boundary M),
        ∃ ρ : SmoothPartitionOfUnity ((𝓡∂ (1 + 1)).boundary M)
          𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) ((𝓡∂ (1 + 1)).boundary M) univ,
          boundaryRestriction φ = ∑ α ∈ s, (fun x ↦ ρ α x • boundaryRestriction φ x) ∧
          (∀ α ∈ s, IntegrableOn (fun t ↦
            ρ α ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
              ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))) *
                circulationFun P Q (γ α) t) (A α)) ∧
          integralTopForm (Manifold.Orientation.mk l) area =
            ∑ α ∈ s,
              (Orientation.signBasis l.boundary.modelOrientation
                (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis : ℝ) *
                (l.boundary.signAt α α : ℝ) * ∫ t in A α,
                  ρ α ((extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 1)) α).symm
                    ((EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ ↦ t))) *
                      circulationFun P Q (γ α) t := by
  have hφ := (ContDiff.isSmoothForm_manifoldOneForm hP hQ).mpullback hf
  have hc : IsCompact (_root_.tsupport (α := (EuclideanSpace ℝ (Fin 2)) [⋀^Fin _]→L[ℝ] ℝ)
    (mpullback (𝓡∂ (1 + 1)) 𝓘(ℝ, ℂ) f (manifoldOneForm P Q))) :=
    isCompact_univ.of_isClosed_subset
    (_root_.isClosed_tsupport (α := (EuclideanSpace ℝ (Fin 2)) [⋀^Fin _]→L[ℝ] ℝ) _) (subset_univ _)
  exact exists_curl_area_boundary_chart_circulation l P Q f hf
    (fun x ↦ hP.differentiable one_ne_zero (f x))
    (fun x ↦ hQ.differentiable one_ne_zero (f x)) hφ hc

end TauCeti.Green
