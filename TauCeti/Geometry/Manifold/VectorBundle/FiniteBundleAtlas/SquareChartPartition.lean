/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
import TauCeti.Geometry.Manifold.PartitionOfUnity.Square
import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic

/-!
# Square chart partitions of vector bundles

A **square chart partition** (`TauCeti.SquareChartPartition`) of a smooth real vector bundle
`V → M` consists of finitely many chart data `ContMDiffSection.ChartTestData` (a chart `cᵢ` of `M`
and a bundle frame `tᵢ` over its source) whose charts have smooth inverses, and smooth cutoffs `χᵢ`
with compact supports inside the chart sources such that `∑ᵢ χᵢ² = 1`. These are the data through
which functionals on bundle tests are localized into function spaces on the model space, for
instance the Sobolev spaces of
`TauCeti.Geometry.Manifold.VectorBundle.Sobolev.BesselPotential`. On a compact boundaryless
manifold one always exists (`TauCeti.exists_squareChartPartition`).

Read in the `i`-th chart, the `i`-th cutoff is the complex test function `y ↦ χᵢ (cᵢ⁻¹ y)` on the
chart target (`TauCeti.SquareChartPartition.chartCutoff`), supported in the compact image
`TauCeti.SquareChartPartition.chartSupport` of `tsupport χᵢ`.

## Main declarations

* `TauCeti.SquareChartPartition`: finite chart data and a square partition of unity.
* `TauCeti.exists_squareChartPartition`: existence on compact boundaryless manifolds.
* `TauCeti.SquareChartPartition.chartSupport`, `TauCeti.SquareChartPartition.chartCutoff`: the
  cutoffs read in the charts.
-/

public section

noncomputable section

open Bundle Set TopologicalSpace Complex ContMDiffSection
open scoped Manifold ContDiff Distributions

namespace TauCeti

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F]
  {V : M → Type*}
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V]

variable (ι I F V) in
/-- A **square chart partition** of a vector bundle `V → M`: finitely many chart data (a chart `cᵢ`
of `M` and a bundle frame `tᵢ` over its source) whose charts have smooth inverses, and smooth
cutoffs `χᵢ` with compact closed supports inside the chart sources whose squares sum to one,
`∑ᵢ χᵢ² = 1`. These are the data with which functionals on bundle tests are localized into
function spaces on the model space. -/
structure SquareChartPartition where
  /-- The chart and the bundle frame of the `i`-th piece. -/
  chartData : ι → ChartTestData I F V ⊤
  /-- The charts have smooth inverses on their targets. -/
  contMDiffOn_chart_symm : ∀ i, ContMDiffOn 𝓘(ℝ, E) I ∞ (chartData i).chart.symm
    (chartData i).chart.target
  /-- The cutoffs. -/
  cutoff : ι → C^∞⟮I, M; ℝ⟯
  /-- The cutoffs have compact closed supports. -/
  isCompact_tsupport_cutoff : ∀ i, IsCompact (tsupport (cutoff i))
  /-- The closed support of the `i`-th cutoff lies in the `i`-th chart source. -/
  tsupport_cutoff_subset : ∀ i, tsupport (cutoff i) ⊆ (chartData i).chart.source
  /-- The squares of the cutoffs sum to one. -/
  sum_sq_cutoff : ∀ x, ∑ i, cutoff i x ^ 2 = 1

namespace SquareChartPartition

variable (A : SquareChartPartition ι I F V)

/-! ### The cutoffs read in the charts -/

/-- The image of the closed support of the `i`-th cutoff in the `i`-th chart, a compact subset of
the chart target. -/
def chartSupport (i : ι) : Compacts E :=
  ⟨(A.chartData i).chart '' tsupport (A.cutoff i),
    (A.isCompact_tsupport_cutoff i).image_of_continuousOn
      ((A.chartData i).chart.continuousOn.mono (A.tsupport_cutoff_subset i))⟩

@[simp]
theorem coe_chartSupport (i : ι) :
    (A.chartSupport i : Set E) = (A.chartData i).chart '' tsupport (A.cutoff i) :=
  (rfl)

theorem chartSupport_subset_target (i : ι) :
    (A.chartSupport i : Set E) ⊆ (A.chartData i).chart.target :=
  image_subset_iff.2 fun _ hx ↦ (A.chartData i).chart.map_source (A.tsupport_cutoff_subset i hx)

theorem mapsTo_chartSupport (i : ι) :
    MapsTo (A.chartData i).chart (tsupport (A.cutoff i)) (A.chartSupport i) :=
  mapsTo_image _ _

/-- Outside the chart image of its support, the `i`-th cutoff read in the chart vanishes. -/
private theorem cutoff_symm_eq_zero {i : ι} {y : E} (hy : y ∈ (A.chartData i).chart.target)
    (hyL : y ∉ (A.chartSupport i : Set E)) : A.cutoff i ((A.chartData i).chart.symm y) = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hyL ⟨_, h, (A.chartData i).chart.right_inv hy⟩

open scoped Classical in
/-- The values of the `i`-th cutoff read in the `i`-th chart, extended by zero. -/
private def chartCutoffFun (i : ι) (y : E) : ℂ :=
  if y ∈ (A.chartData i).chart.target then (A.cutoff i ((A.chartData i).chart.symm y) : ℂ) else 0

private theorem chartCutoffFun_eq_zero {i : ι} {y : E} (hy : y ∉ (A.chartSupport i : Set E)) :
    A.chartCutoffFun i y = 0 := by
  unfold chartCutoffFun
  split_ifs with h
  · rw [A.cutoff_symm_eq_zero h hy, ofReal_zero]
  · rfl

private theorem contDiff_chartCutoffFun (i : ι) : ContDiff ℝ ∞ (A.chartCutoffFun i) := by
  refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
  by_cases hy : y ∈ (A.chartData i).chart.target
  · have h : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞
        (fun y ↦ (A.cutoff i ((A.chartData i).chart.symm y) : ℂ)) y :=
      ofRealCLM.contDiff.contMDiff.contMDiffAt.comp y ((A.cutoff i).contMDiff.contMDiffAt.comp y
        ((A.contMDiffOn_chart_symm i).contMDiffAt
          ((A.chartData i).chart.open_target.mem_nhds hy)))
    refine (contMDiffAt_iff_contDiffAt.1 h).congr_of_eventuallyEq ?_
    filter_upwards [(A.chartData i).chart.open_target.mem_nhds hy] with z hz
    simp [chartCutoffFun, hz]
  · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [(A.chartSupport i).isCompact.isClosed.isOpen_compl.mem_nhds
      fun h ↦ hy (A.chartSupport_subset_target i h)] with z hz
    exact A.chartCutoffFun_eq_zero hz

private theorem tsupport_chartCutoffFun_subset (i : ι) :
    tsupport (A.chartCutoffFun i) ⊆ A.chartSupport i :=
  closure_minimal (fun _ hy ↦ by_contra fun h ↦ hy (A.chartCutoffFun_eq_zero h))
    (A.chartSupport i).isCompact.isClosed

/-- The `i`-th cutoff read in the `i`-th chart: the complex test function `y ↦ χᵢ (cᵢ⁻¹ y)` on the
chart target. -/
def chartCutoff (i : ι) :
    𝓓(⟨(A.chartData i).chart.target, (A.chartData i).chart.open_target⟩, ℂ) :=
  ⟨A.chartCutoffFun i, A.contDiff_chartCutoffFun i,
    HasCompactSupport.intro (A.chartSupport i).isCompact fun _ hy ↦ A.chartCutoffFun_eq_zero hy,
    (A.tsupport_chartCutoffFun_subset i).trans (A.chartSupport_subset_target i)⟩

theorem chartCutoff_apply_of_mem {i : ι} {y : E} (hy : y ∈ (A.chartData i).chart.target) :
    A.chartCutoff i y = A.cutoff i ((A.chartData i).chart.symm y) := by
  rw [chartCutoff, TestFunction.coe_mk]
  simp [chartCutoffFun, hy]

theorem chartCutoff_apply_of_notMem {i : ι} {y : E} (hy : y ∉ (A.chartData i).chart.target) :
    A.chartCutoff i y = 0 := by
  rw [chartCutoff, TestFunction.coe_mk]
  simp [chartCutoffFun, hy]

/-- The `i`-th cutoff read in the `i`-th chart is supported in `chartSupport i`. -/
theorem tsupport_chartCutoff_subset (i : ι) :
    tsupport (A.chartCutoff i) ⊆ A.chartSupport i :=
  A.tsupport_chartCutoffFun_subset i

end SquareChartPartition

/-! ### Existence on compact manifolds -/

/-- **Square chart partitions exist on compact manifolds.** On a compact boundaryless manifold
with finite-dimensional model, every smooth vector bundle has a square chart partition indexed by
`Fin n` for some `n`. -/
theorem exists_squareChartPartition [FiniteDimensional ℝ E] [I.Boundaryless] [CompactSpace M]
    [T2Space M] [IsManifold I ∞ M] :
    ∃ n : ℕ, Nonempty (SquareChartPartition (Fin n) I F V) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  choose c hc hcs hct hx using fun x : M ↦
    exists_chart_source_subset_baseSet (I := I) (F := F) (V := V) (n := ∞) x
  obtain ⟨B, hB⟩ := FiniteBundleAtlas.exists_closure_dom_subset (E := H) (F := F) (V := V)
    (fun x ↦ (c x).source) (fun x ↦ (c x).open_source) hx
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ B.dom B.isOpen_dom
    fun y _ ↦ B.iUnion_dom.symm ▸ mem_univ y
  exact ⟨B.n, ⟨{
    chartData := fun i ↦
      { trivialization := trivializationAt F V (B.center i)
        chart := c (B.center i)
        contMDiffOn_chart := hc _
        source_subset := hct _ }
    contMDiffOn_chart_symm := fun i ↦ hcs _
    cutoff := ρ.sqrtNormalized
    isCompact_tsupport_cutoff := fun i ↦ (B.isCompact_closure_dom i).of_isClosed_subset
      (isClosed_tsupport _) ((hρ.tsupport_sqrtNormalized_subset i).trans subset_closure)
    tsupport_cutoff_subset := fun i ↦
      (hρ.tsupport_sqrtNormalized_subset i).trans (subset_closure.trans (hB i))
    sum_sq_cutoff := fun y ↦ by
      rw [← finsum_eq_sum_of_fintype]
      exact ρ.sum_sq_sqrtNormalized_eq_one (mem_univ y) }⟩⟩

end TauCeti
