/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Geometry.Manifold.Submersion

/-!
# The projection of a smooth fibre bundle with manifold fibre

Let `E` be a fibre bundle over a manifold `B` modelled on `IB`, whose model fibre `F` is a manifold
modelled on `IF`, and chart its total space `TauCeti.ManifoldTotalSpace F E` by the trivializations
of its atlas followed by product charts of `B × F`. In such a chart and the chart of the base at the
same base point, the bundle projection is the first projection `(u, w) ↦ u`. Hence, for a `C^n`
fibre bundle over a `C^n` manifold with a `C^n` manifold as fibre, the projection is a `C^n`
submersion in the sense of `Manifold.IsSubmersion`, with the model space `EF` of the fibre as a
complement (`TauCeti.ManifoldTotalSpace.isSubmersionOfComplement_proj`).

Every point `x` of the total space lies on a local section of the trivialization at its base point,
`b ↦ e⁻¹ (b, (e x).2)`, whose fibre coordinate in that trivialization is constant. A map `h` out of
the base therefore agrees, near the base point of `x`, with the composite of `h ∘ π` and this
section, so `h` is `C^n` at the base point of `x` exactly when `h ∘ π` is `C^n` at `x`
(`TauCeti.ManifoldTotalSpace.contMDiffAt_comp_proj_iff`). When the fibre is nonempty the projection
is surjective, so a map out of the base is `C^n` exactly when its composite with the projection is
(`TauCeti.ManifoldTotalSpace.contMDiff_comp_proj_iff`), and a `C^n` map on the total space that is
constant on the fibres descends uniquely to a `C^n` map on the base
(`TauCeti.ManifoldTotalSpace.existsUnique_contMDiff_comp_proj_eq`). These descent statements hold
for every order `n` and use neither smoothness of the coordinate changes nor `IsManifold`
instances: they rest only on the product form of the charts.

For a principal bundle, a map on the total space that is invariant under the right action is
constant on the fibres, because each fibre is a single orbit; the last statement is then the smooth
descent of invariant maps along the principal projection.

## Main results

* `TauCeti.ManifoldTotalSpace.extChartAt_proj_extChartAt_symm`: in preferred charts, the projection
  is the first coordinate.
* `TauCeti.ManifoldTotalSpace.isSubmersionOfComplement_proj` and `isSubmersion_proj`: the projection
  of a `C^n` fibre bundle is a `C^n` submersion.
* `TauCeti.ManifoldTotalSpace.contMDiffWithinAt_comp_proj_iff` and `contMDiffAt_comp_proj_iff`: a
  map out of the base is `C^n` at the base point of `x` exactly when its composite with the
  projection is `C^n` at `x`.
* `TauCeti.ManifoldTotalSpace.contMDiffOn_comp_proj_iff` and `contMDiff_comp_proj_iff`: for a
  nonempty fibre, the same on a set of the base and globally.
* `TauCeti.ManifoldTotalSpace.existsUnique_contMDiff_comp_proj_eq`: a `C^n` map constant on the
  fibres is the composite of a unique `C^n` map of the base with the projection.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §9.1 (fibre bundles; the projection is a surjective submersion).
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorems 4.26 (local sections of submersions), 4.29 (characteristic property of
  surjective submersions) and 4.30 (passing smoothly to the quotient).
-/

public section

open Bundle Set Filter Function
open scoped Manifold Topology ContDiff

namespace TauCeti.ManifoldTotalSpace

variable {n : ℕ∞ω} {𝕜 B F M : Type*} {E : B → Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*}
  [TopologicalSpace HF] {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  [TopologicalSpace (TotalSpace F E)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E]

/-! ### The projection is a submersion -/

/-- Read through the inverse of a preferred extended chart of the total space, the projection
followed by the extended chart of the base at the same base point is the first coordinate. -/
theorem extChartAt_proj_extChartAt_symm (x : TotalSpace F E) {y : EB × EF}
    (hy : y ∈ (extChartAt (IB.prod IF) (homeomorph F E x)).target) :
    extChartAt IB x.proj
        ((homeomorph F E).symm ((extChartAt (IB.prod IF) (homeomorph F E x)).symm y)).proj =
      y.1 := by
  obtain ⟨w, hw⟩ :=
    (homeomorph F E).surjective ((extChartAt (IB.prod IF) (homeomorph F E x)).symm y)
  rw [← hw, Homeomorph.symm_apply_apply]
  -- The point `w` lies in the source of the trivialization at the base point of `x`.
  have hws : w ∈ (trivializationAt F E x.proj).source := by
    have h := (extChartAt (IB.prod IF) (homeomorph F E x)).map_target hy
    rw [← hw, extChartAt_source, chartAt_homeomorph] at h
    simp only [Homeomorph.transOpenPartialHomeomorph_source, mem_preimage,
      Homeomorph.symm_apply_apply, OpenPartialHomeomorph.trans_source] at h
    exact h.1
  have hy' := (extChartAt (IB.prod IF) (homeomorph F E x)).right_inv hy
  rw [← hw, extChartAt_homeomorph_apply] at hy'
  rw [← hy', (trivializationAt F E x.proj).coe_fst'
    ((trivializationAt F E x.proj).mem_source.1 hws)]

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

/-! ### Descent along the projection -/

/-- The local section `b ↦ e⁻¹ (b, (e x).2)` through `x` of the trivialization `e` at the base point
of `x` is `C^n` at that base point: its fibre coordinate in `e` is constant. -/
private theorem contMDiffAt_trivializationAt_symm (x : TotalSpace F E) :
    ContMDiffAt IB (IB.prod IF) n
      (fun b ↦ homeomorph F E ((trivializationAt F E x.proj).toOpenPartialHomeomorph.symm
        (b, (trivializationAt F E x.proj x).2))) x.proj := by
  set e := trivializationAt F E x.proj
  have hx : x.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E x.proj
  refine ManifoldTotalSpace.contMDiffAt_iff.2 ⟨contMDiffAt_id.congr_of_eventuallyEq ?_, ?_⟩
  · filter_upwards [e.open_baseSet.mem_nhds hx] with b hb
    exact e.proj_symm_apply' hb
  · rw [e.symm_apply_mk_proj (e.mem_source.2 hx)]
    refine (contMDiffAt_const (c := (e x).2)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds hx] with b hb
    rw [e.apply_symm_apply' hb]

/-- A map `h` out of the base is `C^n` within `s` at the base point of `x` exactly when its
composite with the projection is `C^n` within the preimage of `s` at `x`. -/
theorem contMDiffWithinAt_comp_proj_iff {h : B → M} {s : Set B} {x : TotalSpace F E} :
    ContMDiffWithinAt (IB.prod IF) IM n (fun y ↦ h ((homeomorph F E).symm y).proj)
        ((fun y ↦ ((homeomorph F E).symm y).proj) ⁻¹' s) (homeomorph F E x) ↔
      ContMDiffWithinAt IB IM n h s x.proj := by
  refine ⟨fun hh ↦ ?_, fun hh ↦ hh.comp_of_eq (contMDiff_proj n F E IB IF _).contMDiffWithinAt
    (mapsTo_preimage _ _) (by simp)⟩
  set e := trivializationAt F E x.proj
  have hx : x.proj ∈ e.baseSet := mem_baseSet_trivializationAt F E x.proj
  have hsx : e.toOpenPartialHomeomorph.symm (x.proj, (e x).2) = x :=
    e.symm_apply_mk_proj (e.mem_source.2 hx)
  -- Near the base point of `x`, the map `h` is the composite of `h ∘ π` with the local section of
  -- `e` through `x`.
  rw [← contMDiffWithinAt_inter (e.open_baseSet.mem_nhds hx)]
  refine (hh.comp_of_eq (contMDiffAt_trivializationAt_symm x).contMDiffWithinAt
    (fun b hb ↦ ?_) (by simp [e, hsx])).congr (fun b hb ↦ ?_) (by simp [e, hsx])
  · simpa [(trivializationAt F E x.proj).proj_symm_apply' hb.2] using hb.1
  · simp [(trivializationAt F E x.proj).proj_symm_apply' hb.2]

/-- A map `h` out of the base is `C^n` at the base point of `x` exactly when its composite with the
projection is `C^n` at `x`. -/
theorem contMDiffAt_comp_proj_iff {h : B → M} {x : TotalSpace F E} :
    ContMDiffAt (IB.prod IF) IM n (fun y ↦ h ((homeomorph F E).symm y).proj) (homeomorph F E x) ↔
      ContMDiffAt IB IM n h x.proj := by
  simpa only [preimage_univ, contMDiffWithinAt_univ] using
    contMDiffWithinAt_comp_proj_iff (s := univ) (x := x) (h := h) (IF := IF) (n := n)

/-- For a nonempty fibre, a map `h` out of the base is `C^n` on `s` exactly when its composite with
the projection is `C^n` on the preimage of `s`. -/
theorem contMDiffOn_comp_proj_iff [Nonempty F] {h : B → M} {s : Set B} :
    ContMDiffOn (IB.prod IF) IM n (fun y ↦ h ((homeomorph F E).symm y).proj)
        ((fun y ↦ ((homeomorph F E).symm y).proj) ⁻¹' s) ↔ ContMDiffOn IB IM n h s := by
  refine ⟨fun hh b hb ↦ ?_, fun hh y hy ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := FiberBundle.surjective_proj F E b
    exact contMDiffWithinAt_comp_proj_iff.1 (hh _ (by simpa using hb))
  · obtain ⟨x, rfl⟩ := (homeomorph F E).surjective y
    exact contMDiffWithinAt_comp_proj_iff.2 (hh _ (by simpa using hy))

/-- For a nonempty fibre, a map out of the base is `C^n` exactly when its composite with the
projection is `C^n`. -/
theorem contMDiff_comp_proj_iff [Nonempty F] {h : B → M} :
    ContMDiff (IB.prod IF) IM n (fun y ↦ h ((homeomorph F E).symm y).proj) ↔
      ContMDiff IB IM n h := by
  simpa only [preimage_univ, contMDiffOn_univ] using
    contMDiffOn_comp_proj_iff (s := univ) (h := h) (IF := IF) (n := n)

/-- **Smooth descent along the projection.** For a nonempty fibre, a `C^n` map `g` on the total
space that is constant on each fibre is the composite of a unique `C^n` map of the base with the
projection. -/
theorem existsUnique_contMDiff_comp_proj_eq [Nonempty F] {g : ManifoldTotalSpace F E → M}
    (hg : ContMDiff (IB.prod IF) IM n g)
    (hfib : ∀ x y : TotalSpace F E, x.proj = y.proj → g (homeomorph F E x) = g (homeomorph F E y)) :
    ∃! h : B → M, ContMDiff IB IM n h ∧ ∀ x : TotalSpace F E, h x.proj = g (homeomorph F E x) := by
  have hπ := FiberBundle.surjective_proj F E
  have hh : ∀ x : TotalSpace F E, g (homeomorph F E (surjInv hπ x.proj)) = g (homeomorph F E x) :=
    fun x ↦ hfib _ _ (surjInv_eq hπ x.proj)
  refine ⟨fun b ↦ g (homeomorph F E (surjInv hπ b)),
    ⟨(contMDiff_comp_proj_iff (F := F) (E := E) (IF := IF)).1 ?_, hh⟩, ?_⟩
  · refine hg.congr fun y ↦ ?_
    obtain ⟨x, rfl⟩ := (homeomorph F E).surjective y
    simp [hh]
  · rintro h' ⟨-, hh'⟩
    funext b
    obtain ⟨x, rfl⟩ := hπ b
    rw [hh', hh]

end TauCeti.ManifoldTotalSpace
