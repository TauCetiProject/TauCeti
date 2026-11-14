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
chart data of a section in chart `j` are compared with those in chart `i` on the transfer domain
`A.transferDomain i j`: the chart-`j` coordinates whose preimage lies in the source of chart `i` and
in the base sets of the bundle charts `i` and `j`. This file collects the geometry of transfer
domains used to move chart data between charts.

For a `C^n` vector bundle over a `C^n` manifold without boundary modelled on a real normed space,
the coordinate change of the bundle, read in chart `j`, is `C^n` on the transfer domain.

If `M` and `E` are Hausdorff, the image of each chart is covered by finitely many open pieces with
compact closure in a transfer domain, each mapped by the chart coordinate change
`(A.chart j).symm ≫ₕ A.chart i` into an open set with compact closure in the image of another chart.
These pieces are built from the shrinking
`TauCeti.FiniteBundleAtlas.exists_isOpen_closure_subset_dom` of the chart domains.

## Main definitions

* `TauCeti.FiniteBundleAtlas.transferDomain`: the chart-`j` coordinates on which chart `i` and the
  bundle charts `i` and `j` are defined.

## Main results

* `TauCeti.FiniteBundleAtlas.mem_transferDomain`,
  `TauCeti.FiniteBundleAtlas.overlap_subset_transferDomain`: membership in transfer domains, which
  contain the overlaps of chart domains.
* `TauCeti.FiniteBundleAtlas.exists_transfer_cover`: the transfer cover of the chart images.
* `TauCeti.FiniteBundleAtlas.contDiffOn_coordChangeL_transferDomain`: the coordinate change of the
  bundle, read in chart `j`, is `C^n` on the transfer domain.
-/

public section

noncomputable section

open Bundle Set TopologicalSpace
open scoped Manifold Topology

universe u

namespace TauCeti

section Geometry
variable {E : Type u} [TopologicalSpace E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [TopologicalSpace F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  (A : FiniteBundleAtlas E M F V)

namespace FiniteBundleAtlas

/-! ### Transfer domains and the transfer cover -/

/-- The chart-`j` coordinates on which the transfer of chart data from chart `i` is defined: points
of the target of chart `j` whose preimage lies in the source of chart `i` and in the base sets of
the bundle charts `i` and `j`. -/
def transferDomain (i j : Fin A.n) : Set E :=
  (A.chart j).target ∩
    (A.chart j).symm ⁻¹' ((A.chart i).source ∩ ((A.triv j).baseSet ∩ (A.triv i).baseSet))

theorem mem_transferDomain {i j : Fin A.n} {y : E} :
    y ∈ A.transferDomain i j ↔ y ∈ (A.chart j).target ∧ (A.chart j).symm y ∈ (A.chart i).source ∧
      (A.chart j).symm y ∈ (A.triv j).baseSet ∧ (A.chart j).symm y ∈ (A.triv i).baseSet :=
  Iff.rfl

/-- The overlap of the domains of charts `i` and `j`, read in chart `j`, lies in the transfer
domain. -/
theorem overlap_subset_transferDomain (i j : Fin A.n) : A.overlap i j ⊆ A.transferDomain i j := by
  intro _ hy
  obtain ⟨x, ⟨hxi, hxj⟩, rfl⟩ := A.mem_overlap.1 hy
  have hs := A.dom_subset_chart_source j hxj
  refine A.mem_transferDomain.2 ⟨(A.chart j).map_source hs, ?_⟩
  rw [(A.chart j).left_inv hs]
  exact ⟨A.dom_subset_chart_source i hxi, A.dom_subset_baseSet j hxj, A.dom_subset_baseSet i hxi⟩

/-- Transfer domains are open. -/
theorem isOpen_transferDomain (i j : Fin A.n) : IsOpen (A.transferDomain i j) :=
  (A.chart j).isOpen_inter_preimage_symm ((A.chart i).open_source.inter
    ((A.triv j).open_baseSet.inter (A.triv i).open_baseSet))

/-- The transfer domain lies in the source of the chart coordinate change from chart `j` to chart
`i`. -/
theorem transferDomain_subset_source (i j : Fin A.n) :
    A.transferDomain i j ⊆ ((A.chart j).symm ≫ₕ A.chart i).source := fun _ hy ↦ by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  exact ⟨hy.1, hy.2.1⟩

/-- **Transfer cover.** For a finite bundle atlas of a Hausdorff manifold, the image of each chart
`j` is covered by finitely many open pieces `P i j`. The piece `P i j` lies in the overlap of the
domains of charts `i` and `j`, has compact closure in the transfer domain, and is mapped by the
chart coordinate change into an open set `Q i` with compact closure inside the image of chart `i`.
-/
theorem exists_transfer_cover [T2Space E] [T2Space M] :
    ∃ (P : Fin A.n → Fin A.n → Opens E) (Q : Fin A.n → Opens E),
      (∀ i j, (P i j : Set E) ⊆ A.overlap i j) ∧ (∀ i j, IsCompact (closure (P i j : Set E))) ∧
      (∀ i j, closure (P i j : Set E) ⊆ A.transferDomain i j) ∧
      (∀ i, IsCompact (closure (Q i : Set E))) ∧ (∀ i, closure (Q i : Set E) ⊆ A.image i) ∧
      (∀ i j, MapsTo ((A.chart j).symm ≫ₕ A.chart i) (P i j) (Q i)) ∧
      ∀ j, A.image j ≤ ⨆ i, P i j := by
  obtain ⟨D, hDo, hD, hcov⟩ := A.exists_isOpen_closure_subset_dom
  have hDdom (i : Fin A.n) : D i ⊆ A.dom i := subset_closure.trans (hD i)
  have hKc (i j : Fin A.n) : IsCompact (A.chart j '' (closure (A.dom j) ∩ closure (D i))) :=
    ((A.isCompact_closure_dom j).inter_right isClosed_closure).image_of_continuousOn
      ((A.chart j).continuousOn.mono (inter_subset_left.trans (A.closure_dom_subset_source j)))
  have hPK (i j : Fin A.n) : A.chart j '' (A.dom j ∩ D i) ⊆
      A.chart j '' (closure (A.dom j) ∩ closure (D i)) :=
    image_mono (inter_subset_inter subset_closure subset_closure)
  have hQc (i : Fin A.n) : IsCompact (A.chart i '' closure (D i)) :=
    ((A.isCompact_closure_dom i).of_isClosed_subset isClosed_closure
      ((hD i).trans subset_closure)).image_of_continuousOn
      ((A.chart i).continuousOn.mono ((hD i).trans (A.dom_subset_chart_source i)))
  refine ⟨fun i j ↦ ⟨A.chart j '' (A.dom j ∩ D i), (A.chart j).isOpen_image_of_subset_source
      ((A.isOpen_dom j).inter (hDo i)) (inter_subset_left.trans (A.dom_subset_chart_source j))⟩,
    fun i ↦ ⟨A.chart i '' D i, (A.chart i).isOpen_image_of_subset_source (hDo i)
      ((hDdom i).trans (A.dom_subset_chart_source i))⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro i j _ ⟨x, hx, rfl⟩
    exact A.mem_overlap.2 ⟨x, ⟨hDdom i hx.2, hx.1⟩, rfl⟩
  · exact fun i j ↦ (hKc i j).closure_of_subset (hPK i j)
  · intro i j
    refine (closure_minimal (hPK i j) (hKc i j).isClosed).trans ?_
    rintro _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    have hs := A.closure_dom_subset_source j hx₁
    refine ⟨(A.chart j).map_source hs, ?_⟩
    rw [mem_preimage, (A.chart j).left_inv hs]
    exact ⟨A.dom_subset_chart_source i (hD i hx₂), A.closure_dom_subset_baseSet j hx₁,
      A.dom_subset_baseSet i (hD i hx₂)⟩
  · exact fun i ↦ (hQc i).closure_of_subset (image_mono subset_closure)
  · intro i y hy
    exact A.mem_image.2
      (image_mono (hD i) (closure_minimal (image_mono subset_closure) (hQc i).isClosed hy))
  · rintro i j _ ⟨x, ⟨hx₁, hx₂⟩, rfl⟩
    refine ⟨x, hx₂, ?_⟩
    rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      (A.chart j).left_inv (A.dom_subset_chart_source j hx₁)]
  · intro j y hy
    obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hy
    obtain ⟨i, hi⟩ := hcov x
    exact Opens.mem_iSup.2 ⟨i, ⟨x, ⟨hx, hi⟩, rfl⟩⟩

end FiniteBundleAtlas

end Geometry

section Bundle

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : WithTop ℕ∞} [IsManifold 𝓘(ℝ, E) n M] [ContMDiffVectorBundle n F V 𝓘(ℝ, E)]
  (A : FiniteBundleAtlas E M F V)

namespace FiniteBundleAtlas

/-- The coordinate change from bundle chart `i` to bundle chart `j`, read in chart `j`, is `C^n` on
the transfer domain. -/
theorem contDiffOn_coordChangeL_transferDomain (i j : Fin A.n) :
    ContDiffOn ℝ n
      (fun y ↦ ((A.triv i).coordChangeL ℝ (A.triv j) ((A.chart j).symm y) : F →L[ℝ] F))
      (A.transferDomain i j) := by
  rw [← contMDiffOn_iff_contDiffOn]
  exact (contMDiffOn_coordChangeL (IB := 𝓘(ℝ, E)) (A.triv i) (A.triv j)).comp
    (contMDiffOn_chart_symm.mono inter_subset_left) fun _ hy ↦ ⟨hy.2.2.2, hy.2.2.1⟩

end FiniteBundleAtlas

end Bundle

end TauCeti
