/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Geometry.Manifold.Submersion.Basic

/-!
# The projection of a smooth fibre bundle with manifold fibre is a submersion

Let `E` be a fibre bundle over a manifold `B` modelled on `IB`, whose model fibre `F` is a manifold
modelled on `IF`, and chart its total space `TauCeti.ManifoldTotalSpace F E` by the trivializations
of its atlas followed by product charts of `B × F`. In such a chart and the chart of the base at the
same base point, the bundle projection is the first projection `(u, w) ↦ u`
(`TauCeti.ManifoldTotalSpace.extChartAt_proj_extChartAt_symm`). Hence, for a `C^n` fibre bundle
over a `C^n` manifold with a `C^n` manifold as fibre, the projection is a `C^n` submersion in the
sense of `Manifold.IsSubmersion`, with the model space `EF` of the fibre as a complement.

Smooth descent along the projection, which needs no submersion theory, is in
`TauCeti.Geometry.Manifold.FiberBundle.Basic`.

## Main results

* `TauCeti.ManifoldTotalSpace.hasMFDerivAt_proj`, `tangentSpaceCastModel_mfderiv_proj`, and
  `mfderiv_proj_surjective`: at every point of the total space (with no manifold smoothness
  needed), the differential of `ManifoldTotalSpace.proj` reads in model coordinates as `Prod.fst`
  and is surjective.
* `TauCeti.ManifoldTotalSpace.isSubmersionOfComplement_proj` and `isSubmersion_proj`: the projection
  of a `C^n` fibre bundle is a `C^n` submersion.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §9.1 (fibre bundles; the projection is a surjective submersion).
* The projection derivative and submersion structure generalize `Bundle.mfderiv_proj`,
  `Bundle.mfderiv_proj_surjective`, and `Bundle.isSubmersionOfComplement_proj` in
  `TauCeti.Geometry.Manifold.VectorBundle.Submersion` from the normed-space fibre charts of
  `FiberBundle.chartedSpace` to a manifold fibre.
-/
public section

open Bundle
open scoped Manifold Topology ContDiff

namespace TauCeti.ManifoldTotalSpace

variable {n : ℕ∞ω} {𝕜 B F : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

variable (IB IF) in
/-- At every point `z` of `ManifoldTotalSpace F E`, the bundle projection `proj` has manifold
derivative given in model coordinates by the first projection `EB × EF →L[𝕜] EB`. Smoothness of
atlas transitions is not needed. -/
theorem hasMFDerivAt_proj (z : ManifoldTotalSpace F E) :
    HasMFDerivAt (IB.prod IF) IB (proj : ManifoldTotalSpace F E → B) z
      ((tangentSpaceCastModel IB z.proj).symm.toContinuousLinearMap ∘L
        (ContinuousLinearMap.fst 𝕜 EB EF).comp
          (tangentSpaceCastModel (IB.prod IF) z).toContinuousLinearMap) := by
  have hf :
      (tangentSpaceCastModel IB z.proj).toContinuousLinearMap ∘L
          ((tangentSpaceCastModel IB z.proj).symm.toContinuousLinearMap ∘L
            (ContinuousLinearMap.fst 𝕜 EB EF).comp
              (tangentSpaceCastModel (IB.prod IF) z).toContinuousLinearMap) ∘L
          (tangentSpaceCastModel (IB.prod IF) z).symm.toContinuousLinearMap =
        ContinuousLinearMap.fst 𝕜 EB EF :=
    ContinuousLinearMap.ext fun v ↦ by simp
  refine ⟨continuous_proj.continuousAt, ?_⟩
  rw [hf]
  obtain ⟨x, rfl⟩ := (homeomorph F E).surjective z
  have hy := mem_extChartAt_target (I := IB.prod IF) (homeomorph F E x)
  refine (hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := EF)).hasFDerivWithinAt.congr_of_eventuallyEq
    ?_ (by simpa [writtenInExtChartAt] using extChartAt_proj_extChartAt_symm x hy)
  filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hy] with y hy'
  simpa [writtenInExtChartAt] using extChartAt_proj_extChartAt_symm x hy'

/-- Read in model coordinates via `tangentSpaceCastModel`, the differential of
`ManifoldTotalSpace.proj` at `z` takes the first component. -/
@[simp]
theorem tangentSpaceCastModel_mfderiv_proj (z : ManifoldTotalSpace F E)
    (v : TangentSpace (IB.prod IF) z) :
    tangentSpaceCastModel IB z.proj
        (mfderiv (IB.prod IF) IB (proj : ManifoldTotalSpace F E → B) z v) =
      (tangentSpaceCastModel (IB.prod IF) z v).1 := by
  rw [(hasMFDerivAt_proj IB IF z).mfderiv]
  simp

/-- The differential of `ManifoldTotalSpace.proj` is surjective at every point of the total
space. -/
theorem mfderiv_proj_surjective (z : ManifoldTotalSpace F E) :
    Function.Surjective (mfderiv (IB.prod IF) IB (proj : ManifoldTotalSpace F E → B) z) :=
  fun u ↦ ⟨(tangentSpaceCastModel (IB.prod IF) z).symm (tangentSpaceCastModel IB z.proj u, 0),
    (tangentSpaceCastModel IB z.proj).injective <| by
      rw [tangentSpaceCastModel_mfderiv_proj, ContinuousLinearEquiv.apply_symm_apply]⟩

section Submersion

variable [IsManifold IB n B] [IsManifold IF n F] [ContMDiffFiberBundle n F E IB IF]

variable (n F E IB IF) in
/-- The projection of a `C^n` fibre bundle with a manifold fibre is a `C^n` submersion, with the
model space of the fibre as complement: in the preferred charts of the total space and of the base,
it is the first projection. -/
theorem isSubmersionOfComplement_proj :
    Manifold.IsSubmersionOfComplement EF (IB.prod IF) IB n
      fun x : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm x).proj := by
  refine Manifold.isSubmersionOfComplement_iff.mpr fun x ↦ ?_
  obtain ⟨x, rfl⟩ := (homeomorph F E).surjective x
  refine .mk_of_continuousAt (contMDiff_proj n F E IB IF).continuous.continuousAt
    (ContinuousLinearEquiv.refl 𝕜 (EB × EF)) (chartAt _ (homeomorph F E x)) (chartAt HB x.proj)
    (mem_chart_source _ _) (by simp) (IsManifold.chart_mem_maximalAtlas _)
    (IsManifold.chart_mem_maximalAtlas _) fun y hy ↦ ?_
  rw [← extChartAt, ← extChartAt] at *
  simpa using extChartAt_proj_extChartAt_symm x hy

variable (n F E IB IF) in
/-- The projection of a `C^n` fibre bundle with a manifold fibre is a `C^n` submersion. -/
theorem isSubmersion_proj :
    Manifold.IsSubmersion (IB.prod IF) IB n
      fun x : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm x).proj :=
  (isSubmersionOfComplement_proj n F E IB IF).isSubmersion

end Submersion

end TauCeti.ManifoldTotalSpace
