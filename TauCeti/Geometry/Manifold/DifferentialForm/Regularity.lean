/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Continuity
public import TauCeti.Geometry.Manifold.DifferentialForm.Support
import TauCeti.Geometry.Manifold.DifferentialForm.Chart
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# Regularity and support of the manifold exterior derivative

The actual manifold exterior derivative lowers differentiability by one. Its locality prevents
its topological support from enlarging, so compactly supported forms retain compact support.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped Manifold Topology

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Locality of the actual exterior derivative prevents enlargement of a form's support.
No regularity assumption is needed. -/
theorem RoughForm.tsupport_mextDeriv_subset (φ : RoughForm I M F k) :
    (TauCeti.mextDeriv φ).tsupport ⊆ φ.tsupport := by
  rw [RoughForm.tsupport_def]
  apply closure_minimal _ φ.isClosed_tsupport
  intro x hx
  by_contra hnot
  have hz : ∀ᶠ y in 𝓝 x, φ y = (0 : RoughForm I M F k) y := by
    filter_upwards [φ.isClosed_tsupport.isOpen_compl.mem_nhds hnot] with y hy
    exact RoughForm.eq_zero_of_notMem_tsupport hy
  have heq := mextDeriv_congr_of_eventuallyEq hz
  rw [mextDeriv_zero] at heq
  exact hx heq

/-- Compact support is preserved by the actual exterior derivative, without a regularity
assumption. -/
theorem RoughForm.isCompact_tsupport_mextDeriv {φ : RoughForm I M F k}
    (hφ : IsCompact φ.tsupport) : IsCompact (TauCeti.mextDeriv φ).tsupport :=
  hφ.of_isClosed_subset (RoughForm.isClosed_tsupport _) (φ.tsupport_mextDeriv_subset)

section Regularity

/-- In the form's own preferred chart, its section regularity is its coordinate regularity
within the model range at the chart center. -/
theorem IsSmoothForm.contDiffWithinAt_inChartAt_self [IsManifold I 1 M]
    {n : WithTop ℕ∞}
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I n φ) (x : M) :
    ContDiffWithinAt ℝ n (φ.inChartAt x) (range I) (extChartAt I x x) := by
  have hc := (contMDiffAt_section x).mp (hφ.contMDiff x)
  have hf := (contMDiffAt_iff.mp hc).2
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] at hf
  have heq : φ.inChartAt x =ᶠ[𝓝[range I] (extChartAt I x x)]
      fun z ↦ (trivializationAt (E [⋀^Fin k]→L[ℝ] F)
        (fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] F) x
          ⟨(extChartAt I x).symm z, φ ((extChartAt I x).symm z)⟩).2 := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with z hz
    exact φ.inChartAt_eq_trivializationAt x hz
  exact hf.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin
    (extChartAt_target_subset_range x (mem_extChartAt_target x)))

/-- On a `C²` manifold, the actual exterior derivative read in any preferred chart is the
flat exterior derivative of the original coordinate expression. -/
theorem IsSmoothForm.inChartAt_mextDeriv_eq [IsManifold I 2 M]
    {φ : RoughForm I M F k} (hφ : IsSmoothForm I 1 φ) (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target) :
    (TauCeti.mextDeriv φ).inChartAt α z = extDerivWithin (φ.inChartAt α) (range I) z := by
  let y : M := (extChartAt I α).symm z
  have hy : y ∈ (extChartAt I α).source := (extChartAt I α).map_target hz
  have hd := (hφ.contDiffWithinAt_inChartAt_self y).differentiableWithinAt one_ne_zero
  have hcov := φ.extDerivWithin_inChartAt_eq (x := y) hz (mem_extChartAt_source y) hd
  rw [hcov]
  have hchain := mfderiv_comp_mfderivWithin (I := 𝓘(ℝ, E)) (I' := I) (I'' := 𝓘(ℝ, E)) z
    (mdifferentiableAt_extChartAt (mem_chart_source H y))
    (mdifferentiableWithinAt_extChartAt_symm hz)
    (I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range α hz)
      |>.uniqueMDiffWithinAt)
  rw [mfderivWithin_eq_fderivWithin, mfderiv_extChartAt_self] at hchain
  ext v
  rw [RoughForm.inChartAt_apply, mextDeriv_def]
  change extDerivWithin (φ.inChartAt y) (range I) (extChartAt I y y)
      (fun i ↦ mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) z (v i)) =
    extDerivWithin (φ.inChartAt y) (range I) (extChartAt I y y)
      (fun i ↦ fderivWithin ℝ (extChartAt I y ∘ (extChartAt I α).symm) (range I) z (v i))
  congr 1
  funext i
  have h := congrArg (fun L ↦ L (v i)) hchain
  change fderivWithin ℝ (extChartAt I y ∘ (extChartAt I α).symm) (range I) z (v i) =
    mfderivWithin 𝓘(ℝ, E) I (extChartAt I α).symm (range I) z (v i) at h
  exact h.symm

/-- The actual exterior derivative of a `C¹` differential form is a `C⁰` section on a `C²`
manifold. All degrees and normed coefficient spaces are allowed. -/
theorem IsSmoothForm.mextDeriv [IsManifold I 2 M] {φ : RoughForm I M F k}
    (hφ : IsSmoothForm I 1 φ) : IsSmoothForm I 0 (TauCeti.mextDeriv φ) := by
  rw [isSmoothForm_def, contMDiff_zero_iff]
  apply continuous_iff_continuousAt.mpr
  intro x
  have hx : extChartAt I x x ∈ range I :=
    extChartAt_target_subset_range x (mem_extChartAt_target x)
  have hd := (hφ.contDiffWithinAt_inChartAt_self x).continuousWithinAt_fderivWithin
    I.uniqueDiffOn one_ne_zero hx
  have hc := (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F).continuous.continuousAt
    |>.comp_continuousWithinAt hd
  change ContinuousWithinAt (extDerivWithin (φ.inChartAt x) (range I)) (range I)
    (extChartAt I x x) at hc
  have heq : (TauCeti.mextDeriv φ).inChartAt x =ᶠ[𝓝[range I] (extChartAt I x x)]
      extDerivWithin (φ.inChartAt x) (range I) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with z hz
    exact hφ.inChartAt_mextDeriv_eq x hz
  have hdc := hc.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin hx)
  rw [FiberBundle.continuousAt_section, ← continuousWithinAt_univ,
    continuousWithinAt_iff_source (I := I)]
  simp only [preimage_univ, univ_inter]
  apply hdc.congr_of_eventuallyEq
  · filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with z hz
    exact ((TauCeti.mextDeriv φ).inChartAt_eq_trivializationAt x hz).symm
  · exact ((TauCeti.mextDeriv φ).inChartAt_eq_trivializationAt x (mem_extChartAt_target x)).symm

end Regularity

end TauCeti
