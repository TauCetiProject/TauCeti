/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.BumpFunction
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Compactly supported functions with prescribed first derivative

On a finite-dimensional Hausdorff real manifold, any value and continuous linear derivative
at a point are realized by a globally smooth function supported in a prescribed neighborhood.
The construction cuts off an affine function of the extended chart. It works for normed-space
valued functions and also for manifolds with boundary.

This local first-jet realization allows, in particular, localized Hamiltonian perturbations
with a prescribed differential without requiring a global coordinate chart.

## Main results

* `TauCeti.exists_contMDiff_hasCompactSupport_mvfderiv_eq`: a compactly supported smooth function
  with prescribed value and derivative at a point.
-/

public noncomputable section

open Set Topology Manifold
open scoped ContDiff

namespace TauCeti

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Any prescribed value and derivative at a point of a finite-dimensional Hausdorff real
manifold are realized by a smooth function compactly supported in any chosen neighborhood. -/
theorem exists_contMDiff_hasCompactSupport_mvfderiv_eq (x : M) (c : F)
    (L : E →L[ℝ] F) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ f : M → F, ContMDiff I 𝓘(ℝ, F) ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ U ∧
      f x = c ∧ mvfderiv I f x = L := by
  obtain ⟨b, -, hbU⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := I) x).mem_iff.1 hU
  let g : M → F := fun y => c + L (extChartAt I x y - extChartAt I x x)
  have hg : ContMDiffOn I 𝓘(ℝ, F) ∞ g (chartAt H x).source :=
    contMDiffOn_const.add (L.contMDiff.comp_contMDiffOn
      (contMDiffOn_extChartAt.sub_const (extChartAt I x x)))
  have heq : (fun y => b y • g y) =ᶠ[𝓝 x] g := by
    filter_upwards [b.eventuallyEq_one] with y hy
    simp [hy]
  refine ⟨fun y => b y • g y, b.contMDiff_smul hg, b.hasCompactSupport.smul_right,
    (tsupport_smul_subset_left _ _).trans hbU, ?_, ?_⟩
  · simp [g]
  · rw [heq.mvfderiv_eq]
    have hd : HasMFDerivAt I 𝓘(ℝ, F) g x L := by
      have hchart := (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H x)).hasMFDerivAt
      rw [mfderiv_extChartAt_self] at hchart
      have ha : HasFDerivAt (fun y : E => c + L (y - extChartAt I x x)) L
          (extChartAt I x x) := by
        simpa using (L.hasFDerivAt.comp _ ((hasFDerivAt_id _).sub_const
          (extChartAt I x x))).const_add c
      -- The composite chart derivative is the same map across the tangent-space synonym.
      convert ha.hasMFDerivAt.comp x hchart using 1
      rfl
    ext v
    rw [mvfderiv_apply_eq_mfderiv_apply, hd.mfderiv]
    -- `hd` reads `L v` in the target tangent synonym; its underlying vector is still `L v`.
    rfl

end TauCeti
