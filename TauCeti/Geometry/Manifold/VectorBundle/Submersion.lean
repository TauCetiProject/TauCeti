/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import TauCeti.Geometry.Manifold.Submersion

/-!
# The projection of a fibre bundle is a submersion

For a fibre bundle `V` with model fibre `F` over a manifold `B` modelled on `IB`, the total space
carries the charts `(trivializationAt F V b) ≫ (chartAt HB b × id)`, modelled on
`IB.prod 𝓘(𝕜, F)`. In such a chart and the chart `chartAt HB b` of the base, the bundle
projection is the first projection `(u, v) ↦ u`. Hence the projection is a submersion in the
sense of `Manifold.IsSubmersion`, with the model fibre `F` as a complement. Smoothness of the
projection, Mathlib's `Bundle.contMDiff_proj`, is recovered from this by
`Manifold.IsSubmersion.contMDiff`.

No linear structure on the fibres is used, and the regularity order `n` is arbitrary.
-/

public section

open Bundle
open scoped Manifold

namespace Bundle

variable {𝕜 B F EB HB : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {V : B → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B] [FiberBundle F V]
  [IsManifold IB n B] [IsManifold (IB.prod 𝓘(𝕜, F)) n (TotalSpace F V)]

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
  rw [FiberBundle.extChartAt_target] at hy
  obtain ⟨⟨hy₁, hy₂⟩, -⟩ := hy
  simp only [Function.comp_apply, FiberBundle.extChartAt,
    PartialEquiv.trans_symm_eq_symm_trans_symm, PartialEquiv.coe_trans, PartialEquiv.prod_symm,
    PartialEquiv.refl_symm, PartialEquiv.prod_coe, PartialEquiv.refl_coe, id,
    ContinuousLinearEquiv.refl_apply]
  rw [OpenPartialHomeomorph.coe_toPartialEquiv_symm,
    (trivializationAt F V p.proj).proj_symm_apply' hy₂, PartialEquiv.right_inv _ hy₁]

/-- The projection of a fibre bundle is a submersion. -/
theorem isSubmersion_proj : Manifold.IsSubmersion (IB.prod 𝓘(𝕜, F)) IB n (π F V) :=
  isSubmersionOfComplement_proj.isSubmersion

end Bundle
