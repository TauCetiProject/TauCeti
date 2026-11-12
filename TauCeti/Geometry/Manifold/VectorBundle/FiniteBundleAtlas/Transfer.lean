/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic

/-!
# Transfer domains of a finite bundle atlas

Let `A` be a finite bundle atlas of a manifold `M` modelled on `E` for a fibre bundle `V → M`. The
chart data of a section in chart `i` are compared with those in chart `j` on the transfer domain
`A.transferDomain i j`: the chart-`i` coordinates whose preimage lies in the source of chart `j` and
in the base sets of the bundle charts `i` and `j`. This file collects the geometry of transfer
domains used to move chart data between charts.

For a smooth vector bundle over a smooth manifold without boundary modelled on a real normed space,
the coordinate change of the bundle, read in chart `i`, is smooth on the transfer domain.

If `M` is Hausdorff, the image of each chart is covered by finitely many open pieces with compact
closure in a transfer domain, each mapped by the chart coordinate change
`(A.chart i).symm ≫ₕ A.chart j` into an open set with compact closure in the image of another chart.
These pieces are built from the shrinking `TauCeti.FiniteBundleAtlas.exists_shrinking` of the chart
domains; smoothness and invertible derivative of chart coordinate changes are in
`TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic`.

## Main definitions

* `TauCeti.FiniteBundleAtlas.transferDomain`: the chart-`i` coordinates on which chart `j` and the
  bundle charts `i` and `j` are defined.

## Main results

* `TauCeti.FiniteBundleAtlas.exists_transfer_cover`: the transfer cover of the chart images.
* `TauCeti.FiniteBundleAtlas.contDiffOn_coordChangeL_transferDomain`: the coordinate change of the
  bundle, read in chart `i`, is smooth on the transfer domain.
-/

public section

noncomputable section

open Bundle Set TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace TauCeti

section Geometry
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [TopologicalSpace F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  (A : FiniteBundleAtlas E M F V)

namespace FiniteBundleAtlas

/-! ### Transfer domains and the transfer cover -/

/-- The chart-`i` coordinates on which the transfer of chart data from chart `j` is defined: points
of the target of chart `i` whose preimage lies in the source of chart `j` and in the base sets of
the bundle charts `i` and `j`. -/
def transferDomain (i j : Fin A.n) : Set E :=
  (A.chart i).target ∩
    (A.chart i).symm ⁻¹' ((A.chart j).source ∩ ((A.triv i).baseSet ∩ (A.triv j).baseSet))

omit [NormedSpace ℝ E] in
/-- Transfer domains are open. -/
theorem isOpen_transferDomain (i j : Fin A.n) : IsOpen (A.transferDomain i j) :=
  (A.chart i).isOpen_inter_preimage_symm ((A.chart j).open_source.inter
    ((A.triv i).open_baseSet.inter (A.triv j).open_baseSet))

omit [NormedSpace ℝ E] in
/-- The transfer domain lies in the source of the chart coordinate change from chart `i` to chart
`j`. -/
theorem transferDomain_subset_source (i j : Fin A.n) :
    A.transferDomain i j ⊆ ((A.chart i).symm ≫ₕ A.chart j).source := fun _ hy ↦ by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  exact ⟨hy.1, hy.2.1⟩

omit [NormedSpace ℝ E] in
/-- **Transfer cover.** For a finite bundle atlas of a Hausdorff manifold, the image of each chart
`i` is covered by finitely many open pieces `P i j`. The piece `P i j` lies in the overlap of the
domains of charts `j` and `i`, has compact closure in the transfer domain, and is mapped by the
chart coordinate change into an open set `Q j` with compact closure inside the image of chart `j`.
The pieces are `A.chart i '' (A.dom i ∩ D j)` and `Q j = A.chart j '' D j` for a shrinking `D` of
the chart domains. -/
theorem exists_transfer_cover [T2Space M] :
    ∃ (P : Fin A.n → Fin A.n → Opens E) (Q : Fin A.n → Opens E),
      (∀ i j, (P i j : Set E) ⊆ A.overlap j i) ∧ (∀ i j, IsCompact (closure (P i j : Set E))) ∧
      (∀ i j, closure (P i j : Set E) ⊆ A.transferDomain i j) ∧
      (∀ j, IsCompact (closure (Q j : Set E))) ∧ (∀ j, closure (Q j : Set E) ⊆ A.image j) ∧
      (∀ i j, MapsTo ((A.chart i).symm ≫ₕ A.chart j) (P i j) (Q j)) ∧
      ∀ i, A.image i ≤ ⨆ j, P i j := by
  obtain ⟨D, hDo, hD, hcov⟩ := A.exists_shrinking
  have hDdom (j : Fin A.n) : D j ⊆ A.dom j := subset_closure.trans (hD j)
  have hKc (i j : Fin A.n) : IsCompact (A.chart i '' (closure (A.dom i) ∩ closure (D j))) :=
    ((A.isCompact_closure_dom i).inter_right isClosed_closure).image_of_continuousOn
      ((A.chart i).continuousOn.mono (inter_subset_left.trans (A.closure_dom_subset_source i)))
  have hPK (i j : Fin A.n) : A.chart i '' (A.dom i ∩ D j) ⊆
      A.chart i '' (closure (A.dom i) ∩ closure (D j)) :=
    image_mono (inter_subset_inter subset_closure subset_closure)
  have hQc (j : Fin A.n) : IsCompact (A.chart j '' closure (D j)) :=
    ((A.isCompact_closure_dom j).of_isClosed_subset isClosed_closure
      ((hD j).trans subset_closure)).image_of_continuousOn
      ((A.chart j).continuousOn.mono ((hD j).trans (A.dom_subset_chart_source j)))
  refine ⟨fun i j ↦ ⟨A.chart i '' (A.dom i ∩ D j), (A.chart i).isOpen_image_of_subset_source
      ((A.isOpen_dom i).inter (hDo j)) (inter_subset_left.trans (A.dom_subset_chart_source i))⟩,
    fun j ↦ ⟨A.chart j '' D j, (A.chart j).isOpen_image_of_subset_source (hDo j)
      ((hDdom j).trans (A.dom_subset_chart_source j))⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro i j _ ⟨x, hx, rfl⟩
    exact A.mem_overlap.2 ⟨x, ⟨hDdom j hx.2, hx.1⟩, rfl⟩
  · exact fun i j ↦ (hKc i j).closure_of_subset (hPK i j)
  · intro i j
    refine (closure_minimal (hPK i j) (hKc i j).isClosed).trans ?_
    rintro _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    have hs := A.closure_dom_subset_source i hx₁
    refine ⟨(A.chart i).map_source hs, ?_⟩
    rw [mem_preimage, (A.chart i).left_inv hs]
    exact ⟨A.dom_subset_chart_source j (hD j hx₂), A.closure_dom_subset_baseSet i hx₁,
      A.dom_subset_baseSet j (hD j hx₂)⟩
  · exact fun j ↦ (hQc j).closure_of_subset (image_mono subset_closure)
  · intro j y hy
    exact A.mem_image.2
      (image_mono (hD j) (closure_minimal (image_mono subset_closure) (hQc j).isClosed hy))
  · rintro i j _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    refine ⟨x, hx₂, ?_⟩
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      (A.chart i).left_inv (A.dom_subset_chart_source i hx₁)]
  · intro i y hy
    obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hy
    obtain ⟨j, hj⟩ := hcov x
    exact Opens.mem_iSup.2 ⟨j, ⟨x, ⟨hx, hj⟩, rfl⟩⟩

end FiniteBundleAtlas

end Geometry

section Bundle

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  [IsManifold 𝓘(ℝ, E) ∞ M] [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)] (A : FiniteBundleAtlas E M F V)

namespace FiniteBundleAtlas

/-- The coordinate change from bundle chart `j` to bundle chart `i`, read in chart `i`, is smooth on
the transfer domain. -/
theorem contDiffOn_coordChangeL_transferDomain (i j : Fin A.n) :
    ContDiffOn ℝ ∞
      (fun y ↦ ((A.triv j).coordChangeL ℝ (A.triv i) ((A.chart i).symm y) : F →L[ℝ] F))
      (A.transferDomain i j) := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact (contMDiffOn_coordChangeL (IB := 𝓘(ℝ, E)) (A.triv j) (A.triv i)).comp
    (contMDiffOn_chart_symm.mono inter_subset_left) fun _ hy ↦ ⟨hy.2.2.2, hy.2.2.1⟩

end FiniteBundleAtlas

end Bundle

end TauCeti
