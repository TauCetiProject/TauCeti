/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.MFDeriv.Atlas
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.Submersion
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The projection of a fibre bundle is a submersion

For a fibre bundle `V` with model fibre `F` over a manifold `B` modelled on `IB`, the total space
carries the charts `(trivializationAt F V b) ≫ (chartAt HB b × id)`, modelled on
`IB.prod 𝓘(𝕜, F)`. In such a chart and the chart `chartAt HB b` of the base, the bundle
projection is the first projection `(u, v) ↦ u`. Hence the projection is a submersion in the
sense of `Manifold.IsSubmersion`, with the model fibre `F` as a complement. Smoothness of the
projection, Mathlib's `Bundle.contMDiff_proj`, is recovered from this by
`Manifold.IsSubmersion.contMDiff`.

The same chart computation identifies the derivative of the projection: composed with the
derivative of the inverse of a preferred chart of the total space, it is the derivative of the
inverse base chart applied to the first coordinate
(`Bundle.mfderiv_proj_comp_mfderivWithin_extChartAt_symm`). This is how forms built from the
derivative of the projection, such as the Liouville form of a cotangent bundle, are computed in
charts. A self-map of the total space covering the identity of the base commutes with the
derivative of the projection (`Bundle.mfderiv_proj_comp_mfderiv_of_proj_eq`).

No linear structure on the fibres is used, and the regularity order `n` is arbitrary.
-/

public section

open Bundle Filter Set
open scoped Manifold Topology

namespace Bundle

variable {𝕜 B F EB HB : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F V]
  [IsManifold IB n B] [IsManifold (IB.prod 𝓘(𝕜, F)) n (TotalSpace F V)]

/-- A point of the target of a preferred chart of the total space has its first coordinate in the
target of the corresponding chart of the base. -/
theorem fst_mem_extChartAt_target (p : TotalSpace F V) {y : EB × F}
    (hy : y ∈ (extChartAt (IB.prod 𝓘(𝕜, F)) p).target) : y.1 ∈ (extChartAt IB p.proj).target := by
  rw [FiberBundle.extChartAt_target] at hy
  exact hy.1.1

/-- Read through the inverse of a preferred chart of the total space, the bundle projection is the
inverse of the base chart applied to the first coordinate. -/
theorem proj_extChartAt_symm (p : TotalSpace F V) {y : EB × F}
    (hy : y ∈ (extChartAt (IB.prod 𝓘(𝕜, F)) p).target) :
    ((extChartAt (IB.prod 𝓘(𝕜, F)) p).symm y).proj = (extChartAt IB p.proj).symm y.1 := by
  rw [FiberBundle.extChartAt_target] at hy
  simp only [FiberBundle.extChartAt, PartialEquiv.trans_symm_eq_symm_trans_symm,
    PartialEquiv.coe_trans, PartialEquiv.prod_symm, PartialEquiv.refl_symm,
    PartialEquiv.prod_coe, PartialEquiv.refl_coe, Function.comp_apply, id]
  rw [OpenPartialHomeomorph.coe_toPartialEquiv_symm,
    (trivializationAt F V p.proj).proj_symm_apply' hy.1.2]

/-- The projection of a fibre bundle is a submersion, with the model fibre as complement: in the
preferred charts of the total space and of the base, it is the first projection. -/
theorem isSubmersionOfComplement_proj :
    Manifold.IsSubmersionOfComplement F (IB.prod 𝓘(𝕜, F)) IB n (π F V) := by
  refine Manifold.isSubmersionOfComplement_iff.mpr fun p ↦ ?_
  refine .mk_of_continuousAt (FiberBundle.continuous_proj F V).continuousAt
    (ContinuousLinearEquiv.refl 𝕜 (EB × F)) (chartAt _ p) (chartAt HB p.proj)
    (mem_chart_source _ p) (mem_chart_source HB p.proj) (IsManifold.chart_mem_maximalAtlas p)
    (IsManifold.chart_mem_maximalAtlas p.proj) ?_
  intro y hy
  rw [← extChartAt, ← extChartAt] at *
  simp only [Function.comp_apply, proj_extChartAt_symm p hy, ContinuousLinearEquiv.refl_apply,
    (extChartAt IB p.proj).right_inv (fst_mem_extChartAt_target p hy)]

/-- The projection of a fibre bundle is a submersion. -/
theorem isSubmersion_proj : Manifold.IsSubmersion (IB.prod 𝓘(𝕜, F)) IB n (π F V) :=
  isSubmersionOfComplement_proj.isSubmersion

/-- **The derivative of the bundle projection in a preferred chart.** Composed with the derivative
of the inverse of a preferred chart of the total space, the derivative of the projection is the
derivative of the inverse base chart applied to the first coordinate. -/
theorem mfderiv_proj_comp_mfderivWithin_extChartAt_symm [IsManifold IB 1 B]
    [IsManifold (IB.prod 𝓘(𝕜, F)) 1 (TotalSpace F V)] (p : TotalSpace F V) {y : EB × F}
    (hy : y ∈ (extChartAt (IB.prod 𝓘(𝕜, F)) p).target) :
    mfderiv (IB.prod 𝓘(𝕜, F)) IB (π F V) ((extChartAt (IB.prod 𝓘(𝕜, F)) p).symm y) ∘L
        mfderivWithin 𝓘(𝕜, EB × F) (IB.prod 𝓘(𝕜, F)) (extChartAt (IB.prod 𝓘(𝕜, F)) p).symm
          (range (IB.prod 𝓘(𝕜, F))) y =
      mfderivWithin 𝓘(𝕜, EB) IB (extChartAt IB p.proj).symm (range IB) y.1 ∘L
        ContinuousLinearMap.fst 𝕜 EB F := by
  have huniq : UniqueDiffWithinAt 𝕜 (range (IB.prod 𝓘(𝕜, F))) y :=
    (IB.prod 𝓘(𝕜, F)).uniqueDiffOn y (extChartAt_target_subset_range p hy)
  have hproj : π F V ∘ (extChartAt (IB.prod 𝓘(𝕜, F)) p).symm
      =ᶠ[𝓝[range (IB.prod 𝓘(𝕜, F))] y] (extChartAt IB p.proj).symm ∘ Prod.fst := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hy] with y' hy'
    exact proj_extChartAt_symm p hy'
  rw [← mfderiv_comp_mfderivWithin y
      ((contMDiff_proj V _).mdifferentiableAt one_ne_zero)
      (mdifferentiableWithinAt_extChartAt_symm hy) huniq.uniqueMDiffWithinAt,
    hproj.mfderivWithin_eq (proj_extChartAt_symm p hy),
    mfderivWithin_comp y (u := range IB)
      (mdifferentiableWithinAt_extChartAt_symm (fst_mem_extChartAt_target p hy))
      differentiableWithinAt_fst.mdifferentiableWithinAt ?_ huniq.uniqueMDiffWithinAt,
    mfderivWithin_eq_fderivWithin, fderivWithin_fst huniq]
  · -- The tangent spaces of the model spaces are the model spaces themselves.
    rfl
  · intro y' hy'
    rw [ModelWithCorners.range_prod] at hy'
    exact hy'.1

/-- A self-map `g` of the total space covering the identity of the base commutes with the
derivative of the projection: `dπ_{g z} ∘ dg_z = dπ_z`. -/
theorem mfderiv_proj_comp_mfderiv_of_proj_eq {g : TotalSpace F V → TotalSpace F V}
    {z : TotalSpace F V} (hg : MDifferentiableAt (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) g z)
    (hproj : ∀ p, (g p).proj = p.proj) :
    mfderiv (IB.prod 𝓘(𝕜, F)) IB (π F V) (g z) ∘L mfderiv (IB.prod 𝓘(𝕜, F)) (IB.prod 𝓘(𝕜, F)) g z =
      mfderiv (IB.prod 𝓘(𝕜, F)) IB (π F V) z := by
  have hπg : π F V ∘ g = π F V := funext hproj
  rw [← mfderiv_comp z ((contMDiff_proj V (g z)).mdifferentiableAt one_ne_zero) hg, hπg]

end Bundle
