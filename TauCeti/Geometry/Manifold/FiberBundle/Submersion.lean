/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.RegularValue

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

* `TauCeti.ManifoldTotalSpace.isSubmersionOfComplement_proj` and `isSubmersion_proj`: the projection
  of a `C^n` fibre bundle is a `C^n` submersion.
* `TauCeti.ManifoldTotalSpace.isRegularValue_proj`: every base point is a regular value
  of the projection, without smoothness assumptions on the bundle's coordinate changes.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §9.1 (fibre bundles; the projection is a surjective submersion).
* The construction of the submersion structure generalizes the chart-based proof of
  `Bundle.isSubmersionOfComplement_proj` in `TauCeti.Geometry.Manifold.VectorBundle.Submersion`
  from the normed-space fibre charts of `FiberBundle.chartedSpace` to a manifold fibre.
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
  [IsManifold IB n B] [IsManifold IF n F] [ContMDiffFiberBundle n F E IB IF]

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

omit [IsManifold IB n B] [IsManifold IF n F] [ContMDiffFiberBundle n F E IB IF] in
/-- Every base point is a regular value of the bundle projection, including when its fibre is
empty. Smoothness of the bundle's coordinate changes is not needed. -/
theorem isRegularValue_proj (b : B) :
    TauCeti.IsRegularValue (IB.prod IF) IB
      (fun x : ManifoldTotalSpace F E ↦ ((homeomorph F E).symm x).proj) b := by
  rw [TauCeti.isRegularValue_iff]
  intro x _
  obtain ⟨x, rfl⟩ := (homeomorph F E).surjective x
  let e := trivializationAt F E x.proj
  let s := fun b ↦ homeomorph F E (e.toOpenPartialHomeomorph.symm (b, (e x).2))
  have hx : x.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E x.proj
  have hsx : s x.proj = homeomorph F E x :=
    congrArg (homeomorph F E) (e.symm_apply_mk_proj (e.mem_source.2 hx))
  have hps : (fun b ↦ ((homeomorph F E).symm (s b)).proj) =ᶠ[𝓝 x.proj] id := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with b hb
    simpa [s] using e.proj_symm_apply' hb
  have hs : ContMDiffAt IB (IB.prod IF) 1 s x.proj :=
    contMDiffAt_trivializationAt_symm x.proj (e x).2
  have hid := (hasMFDerivAt_id (I := IB) x.proj).congr_of_eventuallyEq_abuse hps
  have hd := mfderiv_comp x.proj
    ((contMDiff_proj 1 F E IB IF).mdifferentiableAt one_ne_zero)
    (hs.mdifferentiableAt one_ne_zero)
  rw [Function.comp_def, hid.mfderiv, hsx] at hd
  refine TauCeti.isRegularPoint_iff.2 fun v ↦ ⟨mfderiv IB (IB.prod IF) s x.proj v, ?_⟩
  exact (DFunLike.congr_fun hd v).symm

end TauCeti.ManifoldTotalSpace
