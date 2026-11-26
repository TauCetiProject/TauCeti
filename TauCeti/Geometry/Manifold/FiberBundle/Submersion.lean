/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Geometry.Manifold.Submersion.Basic
public import TauCeti.Geometry.Manifold.RegularValue
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Cast

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

* `TauCeti.ManifoldTotalSpace.hasMFDerivAt_proj` and `tangentSpaceCastModel_mfderiv_proj`: at every
  point of the total space (with no manifold smoothness needed), the differential of
  `ManifoldTotalSpace.proj` reads in model coordinates as `Prod.fst`.
* `TauCeti.ManifoldTotalSpace.fst_comp_tangentCoordChange`,
  `fst_continuousLinearMapAt_tangent`, and `mfderiv_proj_symmL`: compatibility of `mfderiv proj`
  with preferred tangent trivializations and tangent coordinate changes on `ManifoldTotalSpace F E`
  (requiring `C^1` regularity).
* `TauCeti.ManifoldTotalSpace.isSubmersionOfComplement_proj` and `isSubmersion_proj`: the projection
  of a `C^n` fibre bundle is a `C^n` submersion.
* `TauCeti.ManifoldTotalSpace.isRegularValue_proj`: every base point is a regular value
  of the projection, without smoothness assumptions on the bundle's coordinate changes.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §9.1 (fibre bundles; the projection is a surjective submersion).
* The projection derivative and submersion structure generalize `Bundle.mfderiv_proj`,
  `Bundle.mfderiv_proj_surjective`, and `Bundle.isSubmersionOfComplement_proj` in
  `TauCeti.Geometry.Manifold.VectorBundle.Submersion` from the normed-space fibre charts of
  `FiberBundle.chartedSpace` to a manifold fibre.
* Preferred tangent-trivialization bridges use
  `TauCeti.Geometry.Manifold.VectorBundle.Tangent.Cast` (base-point bridges) and
  `TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic`
  (`continuousLinearMapAt_symmL_coordChange`).
-/
public section

open Bundle Set Filter
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

section TangentCoordChange

variable [IsManifold IB 1 B] [IsManifold IF 1 F] [ContMDiffFiberBundle 1 F E IB IF]

/-- On the overlap of two preferred charts of `ManifoldTotalSpace F E`, the first component of
`tangentCoordChange` intertwines with the base `tangentCoordChange` via `Prod.fst`. -/
theorem fst_comp_tangentCoordChange {i j z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source)
    (hj : z ∈ (chartAt (ModelProd HB HF) j).source) :
    (ContinuousLinearMap.fst 𝕜 EB EF).comp (tangentCoordChange (IB.prod IF) i j z) =
      (tangentCoordChange IB i.proj j.proj z.proj).comp (ContinuousLinearMap.fst 𝕜 EB EF) := by
  have hi' : z ∈ (extChartAt (IB.prod IF) i).source := (extChartAt_source (IB.prod IF) i).symm ▸ hi
  have hj' : z ∈ (extChartAt (IB.prod IF) j).source := (extChartAt_source (IB.prod IF) j).symm ▸ hj
  have hbi : z.proj ∈ (extChartAt IB i.proj).source :=
    proj_mem_extChartAt_source_of_mem_chartAt_source hi
  have hbj : z.proj ∈ (extChartAt IB j.proj).source :=
    proj_mem_extChartAt_source_of_mem_chartAt_source hj
  have hLHS := (hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := EF)).comp_hasFDerivWithinAt _
    (hasFDerivWithinAt_tangentCoordChange (I := IB.prod IF) ⟨hi', hj'⟩)
  have hRHS := ((extChartAt_fst_eq (IB := IB) (IF := IF) hi).symm ▸
      hasFDerivWithinAt_tangentCoordChange (I := IB) ⟨hbi, hbj⟩).comp (extChartAt (IB.prod IF) i z)
    ((hasFDerivAt_fst (𝕜 := 𝕜) (E := EB) (F := EF)).hasFDerivWithinAt (s := range (IB.prod IF)))
    fun y hy ↦ by rw [ModelWithCorners.range_prod] at hy; exact hy.1
  have hrange := extChartAt_target_subset_range i ((extChartAt (IB.prod IF) i).map_source hi')
  have hev : (fun y : EB × EF ↦ (extChartAt (IB.prod IF) j ((extChartAt (IB.prod IF) i).symm y)).1)
      =ᶠ[𝓝[range (IB.prod IF)] (extChartAt (IB.prod IF) i z)]
      fun y : EB × EF ↦ (extChartAt IB j.proj ∘ (extChartAt IB i.proj).symm) y.1 := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem
        ((extChartAt (IB.prod IF) i).map_source hi'),
      nhdsWithin_le_nhds (extChartAt_preimage_mem_nhds' hi'
        ((chartAt (ModelProd HB HF) j).open_source.mem_nhds hj))] with y hyt hyj
    rw [extChartAt_fst_eq hyj, proj_extChartAt_symm i hyt, Function.comp_apply]
  exact (IB.prod IF).uniqueDiffOn.eq hrange hLHS
    (hRHS.congr_of_eventuallyEq hev (hev.self_of_nhdsWithin hrange))

/-- In the preferred tangent trivialization around `i`, the first coordinate of a tangent vector `v`
at `z` equals the base tangent coordinate around `i.proj` of `mfderiv proj z v`. -/
theorem fst_continuousLinearMapAt_tangent {i z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source) (v : TangentSpace (IB.prod IF) z) :
    ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt 𝕜 z v).1 =
      (trivializationAt EB (TangentSpace IB) i.proj).continuousLinearMapAt 𝕜 z.proj
        (mfderiv (IB.prod IF) IB proj z v) := by
  have hz_self := mem_chart_source (ModelProd HB HF) z
  have hbi := (proj_mem_of_mem_chartAt_source hi).2
  have hv : v = (trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) z).symmL 𝕜 z
      (tangentSpaceCastModel (IB.prod IF) z v) := by
    rw [TauCeti.Manifold.symmL_trivializationAt_self_eq_tangentSpaceCastModel_symm]
    simp
  have hmfd : mfderiv (IB.prod IF) IB proj z v =
      (trivializationAt EB (TangentSpace IB) z.proj).symmL 𝕜 z.proj
        (tangentSpaceCastModel (IB.prod IF) z v).1 := by
    rw [TauCeti.Manifold.symmL_trivializationAt_self_eq_tangentSpaceCastModel_symm]
    exact (tangentSpaceCastModel IB z.proj).injective (by simp)
  rw [hmfd]; nth_rw 1 [hv]
  rw [TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange hz_self hi,
    TauCeti.Manifold.continuousLinearMapAt_symmL_coordChange (mem_chart_source HB z.proj) hbi]
  exact DFunLike.congr_fun (fst_comp_tangentCoordChange hz_self hi) _

/-- In the preferred tangent trivialization around `i`, `mfderiv proj z` sends the tangent vector at
`z` with coordinate pair `p : EB × EF` to the base tangent vector at `z.proj` with coordinate
`p.1`. -/
theorem mfderiv_proj_symmL {i z : ManifoldTotalSpace F E}
    (hi : z ∈ (chartAt (ModelProd HB HF) i).source) (p : EB × EF) :
    mfderiv (IB.prod IF) IB (proj : ManifoldTotalSpace F E → B) z
        ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z p) =
      (trivializationAt EB (TangentSpace IB) i.proj).symmL 𝕜 z.proj p.1 := by
  have hbi := (proj_mem_of_mem_chartAt_source hi).2
  have h := fst_continuousLinearMapAt_tangent hi
    ((trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).symmL 𝕜 z p)
  rw [(trivializationAt (EB × EF) (TangentSpace (IB.prod IF)) i).continuousLinearMapAt_symmL
    hi] at h
  have h0 := congrArg ((trivializationAt EB (TangentSpace IB) i.proj).symmL 𝕜 z.proj) h.symm
  rwa [(trivializationAt EB (TangentSpace IB) i.proj).symmL_continuousLinearMapAt hbi] at h0

end TangentCoordChange

section Submersion

variable [IsManifold IB n B] [IsManifold IF n F] [ContMDiffFiberBundle n F E IB IF]

variable (n F E IB IF) in
/-- The projection of a `C^n` fibre bundle with a manifold fibre is a `C^n` submersion, with the
model space of the fibre as complement: in the preferred charts of the total space and of the base,
it is the first projection. -/
theorem isSubmersionOfComplement_proj :
    Manifold.IsSubmersionOfComplement EF (IB.prod IF) IB n
      (proj : ManifoldTotalSpace F E → B) := by
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
    Manifold.IsSubmersion (IB.prod IF) IB n (proj : ManifoldTotalSpace F E → B) :=
  (isSubmersionOfComplement_proj n F E IB IF).isSubmersion

end Submersion

variable (IB IF) in
/-- Every point of the total space is a regular point of the bundle projection.
Smoothness of the bundle's coordinate changes is not needed. -/
theorem isRegularPoint_proj (x : ManifoldTotalSpace F E) :
    TauCeti.IsRegularPoint (IB.prod IF) IB (proj : ManifoldTotalSpace F E → B) x := by
  obtain ⟨x, rfl⟩ := (homeomorph F E).surjective x
  let e := trivializationAt F E x.proj
  let s := fun b ↦ homeomorph F E (e.toOpenPartialHomeomorph.symm (b, (e x).2))
  have hx : x.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E x.proj
  have hsx : s x.proj = homeomorph F E x :=
    congrArg (homeomorph F E) (e.symm_apply_mk_proj (e.mem_source.2 hx))
  have hps : (fun b ↦ (s b).proj) =ᶠ[𝓝 x.proj] id := by
    filter_upwards [e.open_baseSet.mem_nhds hx] with b hb
    simpa [s] using e.proj_symm_apply' hb
  have hs : ContMDiffAt IB (IB.prod IF) 1 s x.proj :=
    contMDiffAt_trivializationAt_symm x.proj (e x).2
  rw [← hsx]
  have hd := mfderiv_comp x.proj
    ((contMDiff_proj 1 F E IB IF).mdifferentiableAt one_ne_zero)
    (hs.mdifferentiableAt one_ne_zero)
  rw [Function.comp_def, hps.mfderiv_eq, mfderiv_id, ContinuousLinearMap.comp_id] at hd
  refine TauCeti.isRegularPoint_iff.2
    (Function.Surjective.of_comp (g := mfderiv IB (IB.prod IF) s x.proj) ?_)
  rw [← ContinuousLinearMap.coe_comp, ← hd, ContinuousLinearEquiv.coe_coe]
  exact (tangentSpaceCast IB _ _).surjective

variable (F E IB IF) in
/-- Every base point is a regular value of the bundle projection, including when its fibre is
empty. Smoothness of the bundle's coordinate changes is not needed. -/
theorem isRegularValue_proj (b : B) :
    TauCeti.IsRegularValue (IB.prod IF) IB (proj : ManifoldTotalSpace F E → B) b := by
  rw [TauCeti.isRegularValue_iff]
  exact fun x _ ↦ isRegularPoint_proj IB IF x

end TauCeti.ManifoldTotalSpace
