/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
import TauCeti.Geometry.Manifold.DifferentialForm.SmoothPartition

/-!
# Stokes' theorem on manifolds with boundary

A finite smooth localization reduces a compactly supported C1 form to boundary-centered chart
patches and patches avoiding the boundary. Chart signs are constant on each patch. The local
half-space theorem and finite additivity then give Stokes for the outward-first orientation.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) ∞ M] [T2Space M] [SigmaCompactSpace M]

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M one_ne_zero

/-- Stokes' theorem for a compactly supported C1 form on an oriented smooth manifold with
boundary. The boundary carries its outward-first orientation. -/
theorem integralTopForm_mextDeriv
    (o : Manifold.Orientation (𝓡∂ (n + 1)) M (Fin (n + 1)))
    {φ : RoughForm (𝓡∂ (n + 1)) M ℝ n}
    (hφ : IsSmoothForm (𝓡∂ (n + 1)) 1 φ) (hc : IsCompact
    (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] ℝ) φ)) :
    integralTopForm o (TauCeti.mextDeriv φ) =
      integralTopForm (boundaryOrientation o) (boundaryRestriction φ) := by
  classical
  obtain ⟨l, rfl⟩ := o.exists_lift
  obtain ⟨s, ρ, heq, hp⟩ := φ.exists_finset_smooth_partition_in_charts l hφ hc
  let ψ : M → RoughForm (𝓡∂ (n + 1)) M ℝ n := fun i x ↦ ρ i x • φ x
  have hψ : ∀ i ∈ s, IsSmoothForm (𝓡∂ (n + 1)) 1 (ψ i) := fun i hi ↦ (hp i hi).1
  have hcψ : ∀ i ∈ s, IsCompact
    (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] ℝ) (ψ i)) := fun i hi ↦
    (hp i hi).2.1
  have hm : ∀ i ∈ s, IntegrableTopForm (TauCeti.mextDeriv (ψ i)) := by
    intro i hi
    exact (hψ i hi).continuous_mextDeriv.integrableTopForm
      ((ψ i).isCompact_tsupport_mextDeriv (hcψ i hi))
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  have hb : ∀ i ∈ s, IntegrableTopForm (boundaryRestriction (ψ i)) := by
    intro i hi
    exact (hψ i hi).boundaryRestriction.integrableTopForm
      (isCompact_tsupport_boundaryRestriction (hcψ i hi))
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  have hmd : TauCeti.mextDeriv φ = ∑ i ∈ s, TauCeti.mextDeriv (ψ i) := by
    rw [heq]
    exact mextDeriv_sum ψ s hψ
  have hbd : boundaryRestriction φ = ∑ i ∈ s, boundaryRestriction (ψ i) := by
    rw [heq, boundaryRestriction_sum]
  rw [hmd, hbd, integralTopForm_sum _ _ _ hm, integralTopForm_sum _ _ _ hb]
  apply Finset.sum_congr rfl
  intro i hi
  have hs : (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] ℝ) (ψ i))
    ⊆ (extChartAt (𝓡∂ (n + 1)) i).source := by
    simpa only [extChartAt_source] using (hp i hi).2.2.1
  have hσ := (hp i hi).2.2.2.1
  by_cases hx : i ∈ (𝓡∂ (n + 1)).boundary M
  · exact integralTopForm_mextDeriv_of_tsupport_subset_chart l (hψ i hi) ⟨i, hx⟩
      (hcψ i hi) hs hσ
  · have hd := (hp i hi).2.2.2.2 hx
    rw [boundaryRestriction_eq_zero_of_disjoint hd, integralTopForm_zero]
    exact integralTopForm_mextDeriv_eq_zero_of_tsupport_subset_chart l (hψ i hi) i
      (hcψ i hi) hs hσ hd

end TauCeti
