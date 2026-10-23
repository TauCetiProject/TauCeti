/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.HalfSpace
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Regularity
public import TauCeti.Geometry.Manifold.Boundary.InducedOrientation
public import TauCeti.Geometry.Manifold.Boundary.Restriction

/-!
# Stokes' theorem in boundary charts

Half-space integration gives Stokes' theorem for a compactly supported form in one boundary
chart. Boundary restriction identifies the coordinate boundary term, and the induced orientation
supplies the outward-first sign. General chart-extension support and regularity facts come from
DifferentialForm.Support and DifferentialForm.Regularity.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

section Boundary

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

local instance boundaryChartStokes_isManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M one_ne_zero


/-- Stokes for a compactly supported form in one preferred chart, with its boundary term
read on the coordinate-zero slice. Both actual coefficients are integrable. -/
private theorem integral_mextDeriv_inChartAt [IsManifold (𝓡∂ (n + 1)) 2 M]
    {φ : RoughForm (𝓡∂ (n + 1)) M ℝ n} (hφ : IsSmoothForm (𝓡∂ (n + 1)) 1 φ)
    (α : M) (hc : IsCompact
    (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] ℝ) φ))
    (hs : (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] ℝ) φ)
    ⊆ (extChartAt (𝓡∂ (n + 1)) α).source) :
    let a := (TauCeti.mextDeriv φ).signedInChartAt
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis α (fun _ ↦ 1)
    let b := fun y ↦ ((extChartAt (𝓡∂ (n + 1)) α).target.indicator (φ.inChartAt α))
      (euclideanHalfSpaceBoundaryParam n y)
      (fun i ↦ euclideanHalfSpaceBoundaryParam n (EuclideanSpace.basisFun (Fin n) ℝ i))
    MeasureTheory.Integrable a ∧ MeasureTheory.Integrable b ∧
      (∫ x, a x) = -(∫ y, b y) := by
  let I := 𝓡∂ (n + 1)
  let e := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  let f := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let ω := (extChartAt I α).target.indicator (φ.inChartAt α)
  let a := (TauCeti.mextDeriv φ).signedInChartAt e α (fun _ ↦ 1)
  let b := fun y ↦ ω (euclideanHalfSpaceBoundaryParam n y)
    (fun i ↦ euclideanHalfSpaceBoundaryParam n (f i))
  -- Use the local scalar names a and b for the two chart integrands.
  change MeasureTheory.Integrable a ∧ MeasureTheory.Integrable b ∧ _
  have hω := φ.contDiffOn_indicator_inChartAt α
    (fun z hz ↦ hφ.contDiffWithinAt_inChartAt α hz) hc hs
  have hr := ContDiffOn.integral_extDerivWithin_euclideanHalfSpace hω
    (φ.hasCompactSupport_indicator_inChartAt α hc hs)
  have hD : EqOn (fun z ↦ extDerivWithin ω (range I) z e) a (range I) := by
    intro z hz
    dsimp only [a]
    rw [RoughForm.signedInChartAt_one]
    exact congrArg (fun L ↦ L e) (hφ.extDerivWithin_indicator_inChartAt α hc hs hz)
  have hsA : Function.support a ⊆ range I :=
    ((TauCeti.mextDeriv φ).support_signedInChartAt_subset_target e α (fun _ ↦ 1)).trans
      (extChartAt_target_subset_range α)
  have hHm : MeasurableSet (range I) := by
    -- Expand the local model I to use the canonical half-space range equation.
    change MeasurableSet (range (𝓡∂ (n + 1)))
    rw [range_modelWithCornersEuclideanHalfSpace]
    exact isClosed_le continuous_const (EuclideanSpace.proj 0).continuous |>.measurableSet
  have hAi : MeasureTheory.Integrable a :=
    (MeasureTheory.integrableOn_iff_integrable_of_support_subset hsA).mp
      (hr.1.congr_fun hD hHm)
  have hBi : MeasureTheory.Integrable b := hr.2.1
  refine ⟨hAi, hBi, ?_⟩
  calc
    (∫ x, a x) = ∫ x in range I, a x :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx ↦ Function.notMem_support.mp (fun hm ↦ hx (hsA hm)))).symm
    _ = ∫ x in range I, extDerivWithin ω (range I) x e :=
      MeasureTheory.setIntegral_congr_fun hHm (fun _ hx ↦ (hD hx).symm)
    _ = _ := hr.2.2

/-- Stokes for one boundary-centered chart. The coefficients are the canonical unsigned chart
coefficients, including their zero extension; the boundary orientation contributes the minus sign.
Both coefficients are genuinely integrable with standard Euclidean volume. -/
theorem integral_mextDeriv_inChartAt_boundary [IsManifold (𝓡∂ (n + 1)) 2 M]
    {φ : RoughForm (𝓡∂ (n + 1)) M ℝ n} (hφ : IsSmoothForm (𝓡∂ (n + 1)) 1 φ)
    (α : (𝓡∂ (n + 1)).boundary M) (hc : IsCompact
    (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] ℝ) φ))
    (hs : (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] ℝ) φ)
    ⊆ (extChartAt (𝓡∂ (n + 1)) (α : M)).source) :
    let a := (TauCeti.mextDeriv φ).signedInChartAt
      (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis (α : M) (fun _ ↦ 1)
    let b := (boundaryRestriction φ).signedInChartAt
      (EuclideanSpace.basisFun (Fin n) ℝ).toBasis α (fun _ ↦ 1)
    MeasureTheory.Integrable a ∧ MeasureTheory.Integrable b ∧
      (∫ x, a x) = -(∫ y, b y) := by
  have hr := integral_mextDeriv_inChartAt hφ (α : M) hc hs
  have hb : (fun y ↦ ((extChartAt (𝓡∂ (n + 1)) (α : M)).target.indicator
      (φ.inChartAt (α : M))) (euclideanHalfSpaceBoundaryParam n y)
        (fun i ↦ euclideanHalfSpaceBoundaryParam n (EuclideanSpace.basisFun (Fin n) ℝ i))) =
      (boundaryRestriction φ).signedInChartAt (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        α (fun _ ↦ 1) := by
    funext y
    rw [RoughForm.signedInChartAt_one, indicator_inChartAt_boundaryRestriction]
    rfl
  simpa only [hb] using hr

end Boundary

section Oriented

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 2 M]

local instance orientedChartStokes_isManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M one_ne_zero

/-- Local Stokes for the canonical manifold integrals. The source sign need only be constant
on the form's support, as supplied by a local smooth partition. -/
theorem integralTopForm_mextDeriv_of_tsupport_subset_chart
    (l : Manifold.OrientationLift (𝓡∂ (n + 1)) M (Fin (n + 1)))
    {φ : RoughForm (𝓡∂ (n + 1)) M ℝ n} (hφ : IsSmoothForm (𝓡∂ (n + 1)) 1 φ)
    (α : (𝓡∂ (n + 1)).boundary M) (hc : IsCompact
    (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] ℝ) φ))
    (hs : (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] ℝ) φ)
    ⊆ (extChartAt (𝓡∂ (n + 1)) (α : M)).source)
    (hσ : ∀ x ∈ (_root_.tsupport (α := (EuclideanSpace ℝ (Fin (n + 1))) [⋀^Fin _]→L[ℝ] ℝ) φ),
    l.signAt (α : M) x = l.signAt (α : M) (α : M)) :
    integralTopForm (Manifold.Orientation.mk l) (TauCeti.mextDeriv φ) =
      integralTopForm (boundaryOrientation (Manifold.Orientation.mk l))
        (boundaryRestriction φ) := by
  let e := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).toBasis
  let f := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let c := l.signAt (α : M) (α : M)
  have hcA := φ.isCompact_tsupport_mextDeriv hc
  have hsA := φ.tsupport_mextDeriv_subset.trans hs
  have hcB := isCompact_tsupport_boundaryRestriction hc
  have hsB := tsupport_boundaryRestriction_subset_source α hs
  have hiA := hφ.continuous_mextDeriv.integrableTopForm hcA e
  have hiB := hφ.boundaryRestriction.integrableTopForm hcB f
  rw [boundaryOrientation_mk, integralTopForm_eq_chartIntegral l _ hiA (α : M) hsA,
    integralTopForm_eq_chartIntegral l.boundary _ hiB α hsB]
  have hσB : ∀ x ∈ (_root_.tsupport (α := (EuclideanSpace ℝ (Fin n)) [⋀^Fin _]→L[ℝ] ℝ)
    (boundaryRestriction φ)), l.boundary.signAt α x = c := by
    intro x hx
    have hxB : x ∈ (chartAt (EuclideanSpace ℝ (Fin n)) α).source := by
      simpa only [extChartAt_source] using hsB hx
    have hxA := tsupport_boundaryRestriction_subset φ hx
    have hxS : (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (α : M)).source := by
      simpa only [extChartAt_source] using hs hxA
    rw [l.boundary.signAt_of_mem hxB, Manifold.OrientationLift.boundary_sign,
      ← l.signAt_of_mem hxS]
    exact hσ x hxA
  rw [l.chartIntegral_eq_const_mul_unsigned _ e (α : M) c
      (fun x hx ↦ hσ x (φ.tsupport_mextDeriv_subset hx)),
    l.boundary.chartIntegral_eq_const_mul_unsigned _ f α c hσB,
    Manifold.OrientationLift.boundary_modelOrientation,
    Orientation.signBasis_halfSpaceBoundaryOrientation]
  simp only [e, f, OrthonormalBasis.addHaar_eq_volume, Units.val_neg, Int.cast_neg]
  rw [(integral_mextDeriv_inChartAt_boundary hφ α hc hs).2.2]
  ring

end Oriented

end TauCeti
