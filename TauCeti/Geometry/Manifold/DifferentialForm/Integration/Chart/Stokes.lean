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
# Compactly supported chart extensions for Stokes' theorem

A form supported inside one chart extends by zero off that chart's target. Compactness keeps
its coordinate support away from the edge of the target, so extension preserves regularity
within the model range and commutes with the actual exterior derivative.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The coordinate extension of a form supported inside a chart has support inside the compact
coordinate image of the original support. -/
theorem RoughForm.tsupport_indicator_inChartAt_subset (φ : RoughForm I M F k) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source) :
    _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α)) ⊆
      (extChartAt I α) '' (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) := by
  classical
  have hK := hc.image_of_continuousOn ((continuousOn_extChartAt α).mono hs)
  apply closure_minimal _ hK.isClosed
  intro z hz
  have ht : z ∈ (extChartAt I α).target := by
    by_contra ht
    exact hz (indicator_of_notMem ht _)
  refine ⟨(extChartAt I α).symm z, ?_, (extChartAt I α).right_inv ht⟩
  apply _root_.subset_tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ
  intro hzero
  apply hz
  rw [indicator_of_mem ht]
  ext v
  rw [RoughForm.inChartAt_apply, hzero]
  rfl

/-- The zero extension of a compact chart-supported form has no support outside the target. -/
theorem RoughForm.notMem_tsupport_indicator_inChartAt (φ : RoughForm I M F k) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source)
    {z : E} (hz : z ∉ (extChartAt I α).target) :
    z ∉ _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α)) := by
  intro ht
  obtain ⟨x, hx, rfl⟩ := φ.tsupport_indicator_inChartAt_subset α hc hs ht
  exact hz ((extChartAt I α).map_source (hs hx))

/-- Compact support survives extension by zero from a chart containing the form's support. -/
theorem RoughForm.hasCompactSupport_indicator_inChartAt (φ : RoughForm I M F k) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source) :
    HasCompactSupport ((extChartAt I α).target.indicator (φ.inChartAt α)) :=
  (hc.image_of_continuousOn ((continuousOn_extChartAt α).mono hs)).of_isClosed_subset
    (_root_.isClosed_tsupport _) (φ.tsupport_indicator_inChartAt_subset α hc hs)

/-- On the target, extension by zero has the same germ within the model range as the original
coordinate form. -/
theorem RoughForm.indicator_inChartAt_eventuallyEq (φ : RoughForm I M F k) (α : M)
    {z : E} (hz : z ∈ (extChartAt I α).target) :
    (extChartAt I α).target.indicator (φ.inChartAt α) =ᶠ[𝓝[range I] z] φ.inChartAt α := by
  classical
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz] with y hy
  exact indicator_of_mem hy _

/-- A coordinate form supported compactly inside the chart extends with the same regularity
within the model range. Regularity outside the model range is unnecessary. -/
theorem RoughForm.contDiffOn_indicator_inChartAt {r : WithTop ℕ∞}
    (φ : RoughForm I M F k) (α : M)
    (hφ : ∀ z ∈ (extChartAt I α).target,
      ContDiffWithinAt ℝ r (φ.inChartAt α) (range I) z)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source) :
    ContDiffOn ℝ r ((extChartAt I α).target.indicator (φ.inChartAt α)) (range I) := by
  classical
  intro z hz
  by_cases ht : z ∈ (extChartAt I α).target
  · exact (hφ z ht).congr_of_eventuallyEq (φ.indicator_inChartAt_eventuallyEq α ht)
      (indicator_of_mem ht _)
  · have hn : z ∉ _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α)) :=
      φ.notMem_tsupport_indicator_inChartAt α hc hs ht
    have he : (extChartAt I α).target.indicator (φ.inChartAt α) =ᶠ[𝓝 z] 0 := by
      filter_upwards [(_root_.isClosed_tsupport _).isOpen_compl.mem_nhds hn] with y hy
      exact image_eq_zero_of_notMem_tsupport hy
    exact (contDiffAt_const.congr_of_eventuallyEq he).contDiffWithinAt

/-- For a form supported inside one chart, exterior differentiation of its zero extension
is the zero extension of its actual manifold exterior derivative, throughout the model range. -/
theorem IsSmoothForm.extDerivWithin_indicator_inChartAt [IsManifold I 2 M]
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I 1 φ) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] F) φ) ⊆ (extChartAt I α).source) :
    EqOn (extDerivWithin ((extChartAt I α).target.indicator (φ.inChartAt α)) (range I))
      ((extChartAt I α).target.indicator ((TauCeti.mextDeriv φ).inChartAt α)) (range I) := by
  classical
  intro z hz
  by_cases ht : z ∈ (extChartAt I α).target
  · rw [indicator_of_mem ht, hφ.inChartAt_mextDeriv_eq α ht, extDerivWithin,
      extDerivWithin]
    exact congrArg ContinuousAlternatingMap.alternatizeUncurryFin
      ((φ.indicator_inChartAt_eventuallyEq α ht).fderivWithin_eq (indicator_of_mem ht _))
  · rw [indicator_of_notMem ht]
    have hn : z ∉ _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α)) :=
      φ.notMem_tsupport_indicator_inChartAt α hc hs ht
    rw [extDerivWithin,
      (HasFDerivWithinAt.of_notMem_tsupport ℝ (s := range I) hn).fderivWithin
        (I.uniqueDiffOn z hz)]
    exact map_zero _

section Boundary

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

local instance boundaryChartStokes_isManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M) := isManifold_boundary M one_ne_zero


private theorem unsignedInChartAt_eq_indicator
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
    {j : ℕ} (ψ : RoughForm I M ℝ j) (b : Module.Basis (Fin j) ℝ E) (α : M) (y : E) :
    ψ.signedInChartAt b α (fun _ ↦ 1) y =
      ((extChartAt I α).target.indicator (ψ.inChartAt α) y) b := by
  classical
  rw [RoughForm.signedInChartAt_apply]
  split_ifs with hy
  · rw [indicator_of_mem hy]
    simp
  · rw [indicator_of_notMem hy]
    rfl

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
  change MeasureTheory.Integrable a ∧ MeasureTheory.Integrable b ∧ _
  have hω := φ.contDiffOn_indicator_inChartAt α
    (fun z hz ↦ hφ.contDiffWithinAt_inChartAt α hz) hc hs
  have hr := ContDiffOn.integral_extDerivWithin_euclideanHalfSpace hω
    (φ.hasCompactSupport_indicator_inChartAt α hc hs)
  have hD : EqOn (fun z ↦ extDerivWithin ω (range I) z e) a (range I) := by
    intro z hz
    dsimp only [a]
    rw [unsignedInChartAt_eq_indicator]
    exact congrArg (fun L ↦ L e) (hφ.extDerivWithin_indicator_inChartAt α hc hs hz)
  have hsA : Function.support a ⊆ range I :=
    ((TauCeti.mextDeriv φ).support_signedInChartAt_subset_target e α (fun _ ↦ 1)).trans
      (extChartAt_target_subset_range α)
  have hHm : MeasurableSet (range I) := by
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
    rw [unsignedInChartAt_eq_indicator, indicator_inChartAt_boundaryRestriction]
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
  have hiA := ((isSmoothForm_def 0 _).mpr ((isSmoothBundleForm_def 0 _).mp
      (isSmoothBundleForm_mextDeriv _ ((isSmoothBundleForm_def 1 _).mpr hφ.contMDiff)
        (n := 0) (by simp)))).integrableTopForm hcA e
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
