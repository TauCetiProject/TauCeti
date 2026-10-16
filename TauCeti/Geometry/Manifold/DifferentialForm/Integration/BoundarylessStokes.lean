/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Chart.Stokes
import TauCeti.Geometry.Manifold.DifferentialForm.Integration.SmoothPartition
import TauCeti.Analysis.Calculus.DifferentialForm.Integral

/-!
# Stokes' theorem away from the boundary

Compactly supported exact top forms have zero canonical oriented integral when the primitive
is supported away from the boundary. The manifold may use any model with corners.
Extension by zero reduces a chart-supported form to flat compact Stokes, and an actual finite
smooth partition gives the global result.
-/

public section

noncomputable section

open Set MeasureTheory Filter
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] {n : ℕ}

omit [FiniteDimensional ℝ E] in
private theorem tsupport_indicator_inChartAt_subset_interior [IsManifold I 1 M]
    (φ : RoughForm I M ℝ n) (α : M) (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ))
    (hs : (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (extChartAt I α).source)
    (hd : Disjoint (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) (I.boundary M)) :
    _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α)) ⊆
      interior (extChartAt I α).target := by
  intro y hy
  obtain ⟨x, hx, rfl⟩ := φ.tsupport_indicator_inChartAt_subset α hc hs hy
  apply mem_interior_iff_mem_nhds.mpr
  exact ModelWithCorners.extChartAt_target_mem_nhds_of_isInteriorPoint (k := 1)
    one_ne_zero α (hs hx)
    ((I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr
      (fun hb ↦ Set.disjoint_left.mp hd hx hb))

omit [FiniteDimensional ℝ E] in
private theorem contDiff_indicator_inChartAt [IsManifold I 2 M]
    {φ : RoughForm I M ℝ n} (hφ : IsSmoothForm I 1 φ) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (extChartAt I α).source)
    (hd : Disjoint (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) (I.boundary M)) :
    ContDiff ℝ 1 ((extChartAt I α).target.indicator (φ.inChartAt α)) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y ∈ _root_.tsupport ((extChartAt I α).target.indicator (φ.inChartAt α))
  · have ht := mem_interior_iff_mem_nhds.mp
      (tsupport_indicator_inChartAt_subset_interior φ α hc hs hd hy)
    have hr : range I ∈ 𝓝 y := mem_of_superset ht (extChartAt_target_subset_range α)
    have he : (extChartAt I α).target.indicator (φ.inChartAt α) =ᶠ[𝓝 y] φ.inChartAt α := by
      filter_upwards [ht] with z hz
      exact indicator_of_mem hz _
    have hy := (hφ.contDiffWithinAt_inChartAt α (mem_of_mem_nhds ht)).contDiffAt hr
    exact hy.congr_of_eventuallyEq he
  · exact contDiffAt_const.congr_of_eventuallyEq (notMem_tsupport_iff_eventuallyEq.mp hy)

/-- The canonical integral of a chart-supported exterior derivative vanishes when the form's
support avoids the boundary. This applies to every real model with corners. -/
theorem integralTopForm_mextDeriv_eq_zero_of_tsupport_subset_chart [IsManifold I 2 M]
    (l : Manifold.OrientationLift I M (Fin (n + 1)))
    {φ : RoughForm I M ℝ n} (hφ : IsSmoothForm I 1 φ) (α : M)
    (hc : IsCompact (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ)) (hs :
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) ⊆ (extChartAt I α).source)
    (hσ : ∀ x ∈ (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ), l.signAt α x = l.signAt α α)
    (hd : Disjoint (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) (I.boundary M)) :
    integralTopForm (Manifold.Orientation.mk l) (TauCeti.mextDeriv φ) = 0 := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  let η := (extChartAt I α).target.indicator (φ.inChartAt α)
  have hω := contDiff_indicator_inChartAt hφ α hc hs hd
  have hcω := φ.hasCompactSupport_indicator_inChartAt α hc hs
  have hr := Module.Basis.integral_extDeriv_eq_zero b hω hcω
  have he (y : E) : (TauCeti.mextDeriv φ).signedInChartAt b α (fun _ ↦ 1) y =
      extDeriv η y b := by
    by_cases hy : y ∈ (extChartAt I α).target
    · have hderiv := hφ.extDerivWithin_indicator_inChartAt α hc hs
        (extChartAt_target_subset_range α hy)
      have hde : extDerivWithin η (range I) y = extDeriv η y := by
        by_cases ht : y ∈ _root_.tsupport η
        · have hn := mem_interior_iff_mem_nhds.mp
            (tsupport_indicator_inChartAt_subset_interior φ α hc hs hd ht)
          rw [extDerivWithin, extDeriv,
            fderivWithin_of_mem_nhds (mem_of_superset hn (extChartAt_target_subset_range α))]
        · rw [extDerivWithin, extDeriv, fderiv_of_notMem_tsupport ℝ ht,
            (HasFDerivWithinAt.of_notMem_tsupport ℝ ht).fderivWithin
              (I.uniqueDiffOn y (extChartAt_target_subset_range α hy))]
      rw [indicator_of_mem hy, hde] at hderiv
      rw [RoughForm.signedInChartAt_apply, dite_eq_left hy]
      simp only [Units.val_one, Int.cast_one, one_mul]
      exact (congrArg (fun A ↦ A b) hderiv).symm
    · have hn : y ∉ _root_.tsupport η := φ.notMem_tsupport_indicator_inChartAt α hc hs hy
      rw [RoughForm.signedInChartAt_apply, dite_eq_right hy, extDeriv,
        fderiv_of_notMem_tsupport ℝ hn]
      simp only [ContinuousAlternatingMap.alternatizeUncurryFin_apply,
        zero_apply, ContinuousAlternatingMap.coe_zero, Pi.zero_apply,
        smul_zero, Finset.sum_const_zero]
  have hi := ((isSmoothForm_def 0 _).mpr ((isSmoothBundleForm_def 0 _).mp
      (isSmoothBundleForm_mextDeriv _ ((isSmoothBundleForm_def 1 _).mpr hφ.contMDiff)
        (n := 0) (by simp)))).integrableTopForm
    (φ.isCompact_tsupport_mextDeriv hc) b
  rw [integralTopForm_eq_chartIntegral l _ hi α (φ.tsupport_mextDeriv_subset.trans hs),
    l.chartIntegral_eq_const_mul_unsigned _ b α (l.signAt α α)
      (fun x hx ↦ hσ x (φ.tsupport_mextDeriv_subset hx))]
  simp_rw [he]
  rw [hr.2, mul_zero]

/-- On any smooth manifold with corners, the actual exterior derivative of a compactly
supported C1 form whose support avoids the boundary has zero canonical oriented integral. -/
theorem integralTopForm_mextDeriv_eq_zero_of_disjoint_boundary [IsManifold I ∞ M] [T2Space M]
    [SigmaCompactSpace M] (o : Manifold.Orientation I M (Fin (n + 1)))
    {φ : RoughForm I M ℝ n} (hφ : IsSmoothForm I 1 φ) (hc : IsCompact
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ))
    (hd : Disjoint (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ) (I.boundary M)) :
    integralTopForm o (TauCeti.mextDeriv φ) = 0 := by
  classical
  let : MeasurableSpace E := borel E
  let : BorelSpace E := ⟨rfl⟩
  obtain ⟨l, rfl⟩ := o.exists_lift
  let b := Module.finBasisOfFinrankEq ℝ E (by simpa using l.card_eq.symm)
  obtain ⟨s, ρ, heq, hp⟩ := φ.exists_finset_smooth_partition_in_charts l hφ hc
  let ψ : M → RoughForm I M ℝ n := fun i x ↦ ρ i x • φ x
  have hψ : ∀ i ∈ s, IsSmoothForm I 1 (ψ i) := fun i hi ↦ (hp i hi).1
  have hcψ : ∀ i ∈ s, IsCompact
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) (ψ i)) := fun i hi ↦ (hp i hi).2.1
  have hm : ∀ i ∈ s, IntegrableTopForm (TauCeti.mextDeriv (ψ i)) := by
    intro i hi
    exact ((isSmoothForm_def 0 _).mpr ((isSmoothBundleForm_def 0 _).mp
      (isSmoothBundleForm_mextDeriv _ ((isSmoothBundleForm_def 1 _).mpr (hψ i hi).contMDiff)
        (n := 0) (by simp)))).integrableTopForm
      ((ψ i).isCompact_tsupport_mextDeriv (hcψ i hi)) b
  have hmd : TauCeti.mextDeriv φ = ∑ i ∈ s, TauCeti.mextDeriv (ψ i) := by
    rw [heq]
    exact mextDeriv_sum ψ s hψ
  rw [hmd, integralTopForm_sum _ _ _ hm]
  apply Finset.sum_eq_zero
  intro i hi
  apply integralTopForm_mextDeriv_eq_zero_of_tsupport_subset_chart l (hψ i hi) i (hcψ i hi)
  · simpa only [extChartAt_source] using (hp i hi).2.2.1
  · exact (hp i hi).2.2.2.1
  · exact hd.mono_left (_root_.tsupport_smul_subset_right (ρ i)
    (show M → E [⋀^Fin _]→L[ℝ] ℝ from φ))

/-- On a boundaryless smooth manifold, compactly supported exact top forms have zero integral.
Intrinsic boundarylessness suffices, even when the model itself has boundary. -/
theorem integralTopForm_mextDeriv_eq_zero [BoundarylessManifold I M]
    [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
    (o : Manifold.Orientation I M (Fin (n + 1)))
    {φ : RoughForm I M ℝ n} (hφ : IsSmoothForm I 1 φ) (hc : IsCompact
    (_root_.tsupport (α := E [⋀^Fin _]→L[ℝ] ℝ) φ)) :
    integralTopForm o (TauCeti.mextDeriv φ) = 0 :=
  integralTopForm_mextDeriv_eq_zero_of_disjoint_boundary o hφ hc
    (by simp only [ModelWithCorners.Boundaryless.boundary_eq_empty, disjoint_empty])

end TauCeti
