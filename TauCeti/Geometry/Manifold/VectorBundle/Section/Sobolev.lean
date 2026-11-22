/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.FunctionalSpaces.BesselPotentialSpace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import TauCeti.Analysis.Distribution.TemperedDistribution.Cutoff
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ChartLocalization
public import TauCeti.Geometry.Manifold.VectorBundle.Section.WaveFrontSet
import TauCeti.Analysis.Distribution.Sobolev
import TauCeti.Analysis.Distribution.TestFunction.Schwartz
import TauCeti.Analysis.Distribution.WaveFrontSet.Sobolev.Tempered
import TauCeti.Analysis.Sobolev.BesselPotential.Inclusion
import TauCeti.Geometry.Manifold.PartitionOfUnity.Square

/-!
# Sobolev spaces of distributions on bundle tests

Let `V → M` be a smooth real vector bundle with model fibre `F`. A distribution on `M` with values
in `V`, or more generally a real functional `T` on the bundle tests `TauCeti.BundleTest I F V`, is
read through a fixed finite family of charts and frames. This file builds the Sobolev spaces `H^s`,
`s ∈ ℝ`, of such functionals from the Euclidean Bessel-potential spaces `H^s(E, ℂ)` of Mathlib.

A **square chart partition** (`TauCeti.SquareChartPartition`) consists of finitely many charts
`cᵢ` with smooth inverses, frames `tᵢ` over their sources, and smooth cutoffs `χᵢ` with compact
supports inside the chart sources such that `∑ᵢ χᵢ² = 1`. On a compact boundaryless manifold one
always exists (`TauCeti.exists_squareChartPartition`). Write `(bⱼ)` for the standard basis
`Module.finBasis ℝ F` of the model fibre.

* The **localization** `χᵢ Tᵢⱼ` of `T` (`TauCeti.SquareChartPartition.localization`) is the
  tempered distribution on the model space `E` obtained from the component `φ ↦ T (φ • bⱼ)` of `T`
  in the `i`-th chart and frame (`Bundle.Trivialization.chartComponent`) by cutting it off with
  `χᵢ` read in the chart (`Distribution.cutoffTempered`).
* Dually, a bundle test `s` has localizations `sᵢⱼ`, the complex Schwartz functions
  `y ↦ χᵢ (cᵢ⁻¹ y) bⱼ* (tᵢ (s (cᵢ⁻¹ y)))` (`TauCeti.SquareChartPartition.testLocalization`).
* The **reconstruction** of tempered distributions `vᵢⱼ` is the functional `s ↦ ∑ᵢⱼ Re vᵢⱼ (sᵢⱼ)`
  (`TauCeti.SquareChartPartition.reconstruction`). It inverts the localization
  (`TauCeti.SquareChartPartition.reconstruction_localization`): the pairing of the localizations
  of `T` and `s` in the `i`-th chart is `T (χᵢ² s)`, and `∑ᵢ χᵢ² = 1`. In particular a functional
  is determined by its localizations (`TauCeti.SquareChartPartition.ext_localization`).

`T` is **`H^s` with respect to the partition** (`TauCeti.SquareChartPartition.MemSobolev`) when all
its localizations lie in `H^s(E, ℂ)`. The **Sobolev space**
`TauCeti.SquareChartPartition.sobolevSpace` is the image of the localization map: the real subspace
of the tuples `(uᵢⱼ)` in the Hilbert sum `⨁ᵢⱼ H^s(E, ℂ)` (`PiLp 2`) that are reproduced by
localizing their reconstruction. It is closed
(`TauCeti.SquareChartPartition.isClosed_sobolevSpace`), so it is complete, and its norm is the
pinned atlas norm `‖T‖² = ∑ᵢⱼ ‖χᵢ Tᵢⱼ‖²_{H^s}`
(`TauCeti.SquareChartPartition.norm_ofMemSobolev_sq`). It is linearly equivalent to the functionals
that are `H^s` with respect to the partition (`TauCeti.SquareChartPartition.sobolevSpaceEquiv`),
through the reconstruction `TauCeti.SquareChartPartition.toDistribution`.

It is a real, not a complex, subspace: the localizations of a real functional are the
complexifications of real distributions, and multiplying them by `i` leaves this class.

Completeness needs no Sobolev estimate for chart changes. A limit of localizations is again a
localization because the localization of a reconstruction, tested on a Schwartz function, only
involves finitely many values of the tempered distributions being reconstructed, so the defining
equations of the subspace are closed.

## Main declarations

* `TauCeti.SquareChartPartition`: finite charts, frames and a square partition of unity.
* `TauCeti.exists_squareChartPartition`: existence on compact boundaryless manifolds.
* `TauCeti.SquareChartPartition.localization`, `TauCeti.SquareChartPartition.reconstruction` and
  `TauCeti.SquareChartPartition.reconstruction_localization`.
* `TauCeti.SquareChartPartition.MemSobolev`: `H^s` regularity with respect to the partition.
* `TauCeti.SquareChartPartition.sobolevSpace`: the Sobolev space, with
  `TauCeti.SquareChartPartition.isClosed_sobolevSpace` and its `CompleteSpace` instance.
* `TauCeti.SquareChartPartition.toDistribution`, `TauCeti.SquareChartPartition.ofMemSobolev`,
  `TauCeti.SquareChartPartition.range_toDistribution` and
  `TauCeti.SquareChartPartition.sobolevSpaceEquiv`: the Sobolev space represents exactly the
  functionals that are `H^s` with respect to the partition.
* `TauCeti.SquareChartPartition.norm_ofMemSobolev_sq`: the pinned norm.

The independence of the space from the partition, up to equivalent norms, needs the Sobolev
estimates for multiplication by cutoffs and for chart changes, and is not proved here.

## References

* M. E. Taylor, *Partial Differential Equations I*, 2nd ed., Springer, 2011, Chapter 4, §3
  (Sobolev spaces on compact manifolds, defined through a partition of unity and charts).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Springer, 1985,
  Appendix B.1 (Sobolev spaces on manifolds).
-/

public section

noncomputable section

open Bundle Set TopologicalSpace Complex ContMDiffSection
open scoped Manifold ContDiff Distributions SchwartzMap CompactConvergenceCLM

namespace TauCeti

variable {ι : Type*} [Fintype ι]
  {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F]
  {V : M → Type*} [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V]

variable (ι I F V) in
/-- A **square chart partition** of a vector bundle `V → M`: finitely many charts `cᵢ` of `M` with
smooth inverses, bundle frames `tᵢ` over their sources, and smooth cutoffs `χᵢ` with compact closed
supports inside the chart sources whose squares sum to one, `∑ᵢ χᵢ² = 1`. These are the data with
which distributions on `M` are localized into the Euclidean Sobolev spaces of the charts. -/
structure SquareChartPartition where
  /-- The bundle frame over the `i`-th chart. -/
  trivialization : ι → Trivialization F (π F V)
  /-- The frames belong to the atlas of the bundle. -/
  [memTrivializationAtlas : ∀ i, MemTrivializationAtlas (trivialization i)]
  /-- The `i`-th chart. -/
  chart : ι → OpenPartialHomeomorph M E
  /-- The charts are smooth on their sources. -/
  contMDiffOn_chart : ∀ i, ContMDiffOn I 𝓘(ℝ, E) ∞ (chart i) (chart i).source
  /-- The charts have smooth inverses on their targets. -/
  contMDiffOn_chart_symm : ∀ i, ContMDiffOn 𝓘(ℝ, E) I ∞ (chart i).symm (chart i).target
  /-- Each chart source lies in the base set of its frame. -/
  source_subset : ∀ i, (chart i).source ⊆ (trivialization i).baseSet
  /-- The cutoffs. -/
  cutoff : ι → C^∞⟮I, M; ℝ⟯
  /-- The cutoffs have compact closed supports. -/
  isCompact_tsupport_cutoff : ∀ i, IsCompact (tsupport (cutoff i))
  /-- The closed support of the `i`-th cutoff lies in the `i`-th chart source. -/
  tsupport_cutoff_subset : ∀ i, tsupport (cutoff i) ⊆ (chart i).source
  /-- The squares of the cutoffs sum to one. -/
  sum_sq_cutoff : ∀ x, ∑ i, cutoff i x ^ 2 = 1

namespace SquareChartPartition

attribute [instance] memTrivializationAtlas

variable (A : SquareChartPartition ι I F V)

/-! ### The cutoffs read in the charts -/

/-- The image of the closed support of the `i`-th cutoff in the `i`-th chart, a compact subset of
the chart target. -/
def chartSupport (i : ι) : Compacts E :=
  ⟨A.chart i '' tsupport (A.cutoff i), (A.isCompact_tsupport_cutoff i).image_of_continuousOn
    ((A.chart i).continuousOn.mono (A.tsupport_cutoff_subset i))⟩

theorem chartSupport_subset_target (i : ι) : (A.chartSupport i : Set E) ⊆ (A.chart i).target :=
  image_subset_iff.2 fun _ hx ↦ (A.chart i).map_source (A.tsupport_cutoff_subset i hx)

theorem mapsTo_chartSupport (i : ι) :
    MapsTo (A.chart i) (tsupport (A.cutoff i)) (A.chartSupport i) :=
  mapsTo_image _ _

/-- Outside the chart image of its support, the `i`-th cutoff read in the chart vanishes. -/
private theorem cutoff_symm_eq_zero {i : ι} {y : E} (hy : y ∈ (A.chart i).target)
    (hyL : y ∉ (A.chartSupport i : Set E)) : A.cutoff i ((A.chart i).symm y) = 0 :=
  image_eq_zero_of_notMem_tsupport fun h ↦ hyL ⟨_, h, (A.chart i).right_inv hy⟩

open scoped Classical in
/-- The values of the `i`-th cutoff read in the `i`-th chart, extended by zero. -/
private def chartCutoffFun (i : ι) (y : E) : ℂ :=
  if y ∈ (A.chart i).target then (A.cutoff i ((A.chart i).symm y) : ℂ) else 0

private theorem chartCutoffFun_eq_zero {i : ι} {y : E} (hy : y ∉ (A.chartSupport i : Set E)) :
    A.chartCutoffFun i y = 0 := by
  unfold chartCutoffFun
  split_ifs with h
  · rw [A.cutoff_symm_eq_zero h hy, ofReal_zero]
  · rfl

private theorem contDiff_chartCutoffFun (i : ι) : ContDiff ℝ ∞ (A.chartCutoffFun i) := by
  refine contDiff_iff_contDiffAt.2 fun y ↦ ?_
  by_cases hy : y ∈ (A.chart i).target
  · have h : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (fun y ↦ (A.cutoff i ((A.chart i).symm y) : ℂ)) y :=
      ofRealCLM.contDiff.contMDiff.contMDiffAt.comp y ((A.cutoff i).contMDiff.contMDiffAt.comp y
        ((A.contMDiffOn_chart_symm i).contMDiffAt ((A.chart i).open_target.mem_nhds hy)))
    refine (contMDiffAt_iff_contDiffAt.1 h).congr_of_eventuallyEq ?_
    filter_upwards [(A.chart i).open_target.mem_nhds hy] with z hz
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
def chartCutoff (i : ι) : 𝓓(⟨(A.chart i).target, (A.chart i).open_target⟩, ℂ) :=
  ⟨A.chartCutoffFun i, A.contDiff_chartCutoffFun i,
    HasCompactSupport.intro (A.chartSupport i).isCompact fun _ hy ↦ A.chartCutoffFun_eq_zero hy,
    (A.tsupport_chartCutoffFun_subset i).trans (A.chartSupport_subset_target i)⟩

theorem chartCutoff_apply_of_mem {i : ι} {y : E} (hy : y ∈ (A.chart i).target) :
    A.chartCutoff i y = A.cutoff i ((A.chart i).symm y) := by
  rw [chartCutoff, TestFunction.coe_mk]
  simp [chartCutoffFun, hy]

theorem chartCutoff_apply_of_notMem {i : ι} {y : E} (hy : y ∉ (A.chart i).target) :
    A.chartCutoff i y = 0 := by
  rw [chartCutoff, TestFunction.coe_mk]
  simp [chartCutoffFun, hy]

private theorem tsupport_cutoff_mul_subset (i : ι) :
    tsupport ⇑(A.cutoff i * A.cutoff i) ⊆ tsupport (A.cutoff i) := by
  rw [ContMDiffMap.coe_mul]
  exact tsupport_mul_subset_left

/-! ### Existence on compact manifolds -/

/-- **Square chart partitions exist on compact manifolds.** On a compact boundaryless manifold
with finite-dimensional model, every smooth vector bundle has a square chart partition, indexed by
a finite set of points of the base. -/
theorem _root_.TauCeti.exists_squareChartPartition [FiniteDimensional ℝ E] [I.Boundaryless]
    [CompactSpace M] [T2Space M] [IsManifold I ∞ M] :
    ∃ t : Finset M, Nonempty (SquareChartPartition t I F V) := by
  have : LocallyCompactSpace H := I.locallyCompactSpace
  have : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace H M
  choose c hc hcs hct hx using fun x : M ↦
    exists_chart_source_subset_baseSet (I := I) (F := F) (V := V) (n := ∞) x
  -- Shrink each chart source to an open neighbourhood with compact closure inside it.
  choose W hWo hxW hWs hWc using fun x : M ↦ exists_open_between_and_isCompact_closure
    isCompact_singleton (c x).open_source (singleton_subset_iff.2 (hx x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo
    fun y _ ↦ mem_iUnion.2 ⟨y, hxW y rfl⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I isClosed_univ
    (fun x : t ↦ W x) (fun x ↦ hWo x) fun y _ ↦ by simpa using ht (mem_univ y)
  exact ⟨t, ⟨{
    trivialization := fun x ↦ trivializationAt F V x
    chart := fun x ↦ c x
    contMDiffOn_chart := fun x ↦ hc x
    contMDiffOn_chart_symm := fun x ↦ hcs x
    source_subset := fun x ↦ hct x
    cutoff := ρ.sqrtNormalized
    isCompact_tsupport_cutoff := fun x ↦ (hWc x).of_isClosed_subset (isClosed_tsupport _)
      ((hρ.tsupport_sqrtNormalized_subset x).trans subset_closure)
    tsupport_cutoff_subset := fun x ↦
      (hρ.tsupport_sqrtNormalized_subset x).trans (subset_closure.trans (hWs x))
    sum_sq_cutoff := fun y ↦ by
      rw [← finsum_eq_sum_of_fintype]
      exact ρ.sum_sq_sqrtNormalized_eq_one (mem_univ y) }⟩⟩

/-! ### Localization and reconstruction -/

variable [FiniteDimensional ℝ E] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]

/-- The chart localization of bundle tests by a cutoff `ψ` supported in the support of the `i`-th
cutoff, as a continuous linear map into the test functions supported in `A.chartSupport i`. -/
private def localizationCLM (i : ι) (ψ : C^∞⟮I, M; ℝ⟯) (hψ : tsupport ψ ⊆ tsupport (A.cutoff i)) :
    BundleTest I F V →L[ℝ] 𝓓_{A.chartSupport i}(E, F) where
  toLinearMap := (A.trivialization i).chartLocalization (A.chart i) (A.contMDiffOn_chart_symm i)
      (A.source_subset i) ψ (A.chartSupport i) (A.chartSupport_subset_target i)
      ((A.mapsTo_chartSupport i).mono_left hψ) ∘ₗ
    (compactlySupported I F ∞ V).subtype ∘ₗ (BundleTest.ofCompactlySupported I F V).symm.toLinearMap
  cont := by
    let e := fun x : M ↦ trivializationAt F V x
    let U := fun x : M ↦ (⟨_, (trivializationAt F V x).open_baseSet⟩ : Opens M)
    let := frameTopology (I := I) (n := ∞) e U fun _ ↦ subset_rfl
    exact ((A.trivialization i).continuous_chartLocalization (A.chart i)
      (A.contMDiffOn_chart_symm i) (A.source_subset i) ψ (A.chartSupport i)
      (A.chartSupport_subset_target i) ((A.mapsTo_chartSupport i).mono_left hψ) e U
      (fun _ ↦ subset_rfl) fun x ↦ ⟨x, mem_baseSet_trivializationAt F V x⟩).comp
      (continuous_val_compactlySupportedTopology (I := I) (n := ∞) e U fun _ ↦ subset_rfl)

omit [FiniteDimensional ℝ F] in
private theorem localizationCLM_apply_of_mem (i : ι) (ψ : C^∞⟮I, M; ℝ⟯)
    (hψ : tsupport ψ ⊆ tsupport (A.cutoff i)) (s : BundleTest I F V) {y : E}
    (hy : y ∈ (A.chart i).target) :
    A.localizationCLM i ψ hψ s y = ψ ((A.chart i).symm y) •
      (A.trivialization i ⟨(A.chart i).symm y, s ((A.chart i).symm y)⟩).2 :=
  (A.trivialization i).chartLocalization_apply_of_mem _ _ _ _ _ _ _ _ hy

omit [FiniteDimensional ℝ F] in
private theorem localizationCLM_apply_of_notMem (i : ι) (ψ : C^∞⟮I, M; ℝ⟯)
    (hψ : tsupport ψ ⊆ tsupport (A.cutoff i)) (s : BundleTest I F V) {y : E}
    (hy : y ∉ (A.chart i).target) :
    A.localizationCLM i ψ hψ s y = 0 :=
  (A.trivialization i).chartLocalization_apply_of_notMem _ _ _ _ _ _ _ _ hy

/-- The `j`-th coordinate functional of the standard basis of the model fibre, with complex
values. -/
private def coordCLM (j : Fin (Module.finrank ℝ F)) : F →L[ℝ] ℂ :=
  ofRealCLM ∘L LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord j)

@[simp]
private theorem coordCLM_apply (j : Fin (Module.finrank ℝ F)) (v : F) :
    coordCLM j v = ((Module.finBasis ℝ F).repr v j : ℂ) :=
  rfl

/-- The **localization of bundle tests**: a bundle test `s` goes to the complex Schwartz function
`y ↦ χᵢ (cᵢ⁻¹ y) bⱼ* (tᵢ (s (cᵢ⁻¹ y)))` on the model space, the `j`-th frame coordinate of `s` in
the `i`-th chart cut off by `χᵢ`, extended by zero. Here `(bⱼ*)` is the dual basis of the standard
basis `Module.finBasis ℝ F` of the model fibre. -/
def testLocalization (i : ι) (j : Fin (Module.finrank ℝ F)) :
    BundleTest I F V →L[ℝ] 𝓢(E, ℂ) :=
  ContDiffMapSupportedIn.toSchwartzMapCLM ℝ ∘L ContDiffMapSupportedIn.postcompCLM (coordCLM j) ∘L
    A.localizationCLM i (A.cutoff i) subset_rfl

theorem testLocalization_apply_of_mem (i : ι) (j : Fin (Module.finrank ℝ F))
    (s : BundleTest I F V) {y : E} (hy : y ∈ (A.chart i).target) :
    A.testLocalization i j s y = (A.cutoff i ((A.chart i).symm y) *
      (Module.finBasis ℝ F).repr
        (A.trivialization i ⟨(A.chart i).symm y, s ((A.chart i).symm y)⟩).2 j : ℝ) := by
  simp [testLocalization, A.localizationCLM_apply_of_mem _ _ _ _ hy]

theorem testLocalization_apply_of_notMem (i : ι) (j : Fin (Module.finrank ℝ F))
    (s : BundleTest I F V) {y : E} (hy : y ∉ (A.chart i).target) :
    A.testLocalization i j s y = 0 := by
  simp [testLocalization, A.localizationCLM_apply_of_notMem _ _ _ _ hy]

/-- The functional `s ↦ ∑ᵢⱼ Re vᵢⱼ (sᵢⱼ)` on bundle tests. -/
private def reconstructionCLM (v : ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ)) :
    BundleTest I F V →L_c[ℝ] ℝ where
  toFun s := ∑ k, (v k (A.testLocalization k.1 k.2 s)).re
  map_add' s s' := by simp [Finset.sum_add_distrib]
  map_smul' a s := by
    simp only [map_smul, ← Complex.coe_smul, smul_eq_mul, Complex.re_ofReal_mul, Finset.mul_sum,
      RingHom.id_apply]
  cont := continuous_finsetSum _ fun k _ ↦
    continuous_re.comp ((v k).continuous.comp (A.testLocalization k.1 k.2).continuous)

private theorem reconstructionCLM_apply (v : ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ))
    (s : BundleTest I F V) :
    A.reconstructionCLM v s = ∑ k, (v k (A.testLocalization k.1 k.2 s)).re :=
  (rfl)

/-- The **reconstruction** of a functional on bundle tests from tempered distributions `vᵢⱼ`, one
for each chart and each basis vector of the model fibre: `s ↦ ∑ᵢⱼ Re vᵢⱼ (sᵢⱼ)`, where `sᵢⱼ` is
the localization of `s` (`TauCeti.SquareChartPartition.testLocalization`). It inverts the
localization of distributions (`TauCeti.SquareChartPartition.reconstruction_localization`). -/
def reconstruction :
    (ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ)) →ₗ[ℝ] (BundleTest I F V →L_c[ℝ] ℝ) where
  toFun := A.reconstructionCLM
  map_add' v v' := by
    ext s
    simp [reconstructionCLM_apply, Finset.sum_add_distrib]
  map_smul' a v := by
    ext s
    simp [reconstructionCLM_apply, Finset.mul_sum]

theorem reconstruction_apply (v : ι × Fin (Module.finrank ℝ F) → 𝓢'(E, ℂ))
    (s : BundleTest I F V) :
    A.reconstruction v s = ∑ k, (v k (A.testLocalization k.1 k.2 s)).re :=
  (rfl)

/-! ### Localization of distributions -/

variable [T2Space M]

omit [FiniteDimensional ℝ F] in
/-- Extending the localization by `ψ` back through the chart and the frame gives `ψ • s`. -/
private theorem chartTestCLM_localizationCLM (i : ι) (ψ : C^∞⟮I, M; ℝ⟯)
    (hψ : tsupport ψ ⊆ tsupport (A.cutoff i)) (s : BundleTest I F V) (x : M) :
    (A.trivialization i).chartTestCLM (A.chart i) (A.contMDiffOn_chart i) (A.source_subset i)
      (TestFunction.ofSupportedIn (A.chartSupport_subset_target i) (A.localizationCLM i ψ hψ s)) x =
      ψ x • s x := by
  rw [Bundle.Trivialization.coe_chartTestCLM]
  refine (congr($((A.trivialization i).chartTestSection_chartLocalization (A.chart i)
    (A.contMDiffOn_chart_symm i) (A.source_subset i) ψ (A.chartSupport i)
    (A.chartSupport_subset_target i) ((A.mapsTo_chartSupport i).mono_left hψ)
    (A.contMDiffOn_chart i) (hψ.trans (A.tsupport_cutoff_subset i))
    ((BundleTest.ofCompactlySupported I F V).symm s).val) x)).trans ?_
  simp

/-- The **localization of distributions**: a real functional `T` on bundle tests goes to the
tempered distribution `χᵢ Tᵢⱼ` on the model space, where `Tᵢⱼ` is the component of `T` along the
`j`-th basis vector `bⱼ` of the model fibre in the `i`-th chart and frame, `φ ↦ T (φ • bⱼ)`
(`Bundle.Trivialization.chartComponent`), cut off by `χᵢ` read in the chart. -/
def localization (i : ι) (j : Fin (Module.finrank ℝ F)) :
    (BundleTest I F V →L_c[ℝ] ℝ) →ₗ[ℝ] 𝓢'(E, ℂ) where
  toFun T := ((A.trivialization i).chartComponent (A.chart i) (A.contMDiffOn_chart i)
    (A.source_subset i) T (Module.finBasis ℝ F j)).cutoffTempered (A.chartCutoff i)
  map_add' T S := by
    ext ψ
    simp only [Distribution.cutoffTempered_def, Distribution.complexPairing_apply,
      Bundle.Trivialization.chartComponent_apply, _root_.add_apply, ofReal_add]
    ring
  map_smul' a T := by
    ext ψ
    simp only [Distribution.cutoffTempered_def, Distribution.complexPairing_apply,
      Bundle.Trivialization.chartComponent_apply, _root_.smul_apply, RingHom.id_apply]
    simp
    ring

theorem localization_apply (i : ι) (j : Fin (Module.finrank ℝ F)) (T : BundleTest I F V →L_c[ℝ] ℝ) :
    A.localization i j T = ((A.trivialization i).chartComponent (A.chart i)
      (A.contMDiffOn_chart i) (A.source_subset i) T (Module.finBasis ℝ F j)).cutoffTempered
        (A.chartCutoff i) :=
  (rfl)

/-- The localization of `T`, paired with the localization of `s`, is `T` evaluated on the `j`-th
frame component of `χᵢ² s`. -/
private theorem localization_apply_testLocalization (T : BundleTest I F V →L_c[ℝ] ℝ) (i : ι)
    (j : Fin (Module.finrank ℝ F)) (s : BundleTest I F V) :
    A.localization i j T (A.testLocalization i j s) =
      (T ((A.trivialization i).chartTestCLM (A.chart i) (A.contMDiffOn_chart i) (A.source_subset i)
        (TestFunction.postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (Module.finBasis ℝ F j))
          (TestFunction.postcompCLM
            (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord j))
            (TestFunction.ofSupportedIn (A.chartSupport_subset_target i)
              (A.localizationCLM i _ (A.tsupport_cutoff_mul_subset i) s))))) : ℂ) := by
  rw [localization_apply, Distribution.cutoffTempered_apply _ _ (χ := TestFunction.postcompCLM
    (𝕜 := ℝ) ofRealCLM (TestFunction.postcompCLM
      (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord j))
      (TestFunction.ofSupportedIn (A.chartSupport_subset_target i)
        (A.localizationCLM i _ (A.tsupport_cutoff_mul_subset i) s)))),
    Distribution.complexPairing_postcompCLM_ofRealCLM,
    Bundle.Trivialization.chartComponent_apply]
  intro y
  by_cases hy : y ∈ (A.chart i).target
  · simp [A.testLocalization_apply_of_mem _ _ _ hy, A.chartCutoff_apply_of_mem hy,
      A.localizationCLM_apply_of_mem _ _ _ _ hy, ContMDiffMap.coe_mul]
    ring
  · simp [A.testLocalization_apply_of_notMem _ _ _ hy,
      A.localizationCLM_apply_of_notMem _ _ _ _ hy]

/-- **Reconstruction inverts localization.** A real functional `T` on bundle tests is recovered
from its localizations: `T s = ∑ᵢⱼ Re (χᵢ Tᵢⱼ) (sᵢⱼ)`. This is `∑ᵢ χᵢ² = 1`: the pairing of the
localizations of `T` and `s` in the `i`-th chart is `T (χᵢ² s)`. -/
@[simp]
theorem reconstruction_localization (T : BundleTest I F V →L_c[ℝ] ℝ) :
    A.reconstruction (fun k ↦ A.localization k.1 k.2 T) = T := by
  ext s
  have hj (i : ι) : ∑ j, TestFunction.postcompCLM
      (ContinuousLinearMap.toSpanSingleton ℝ (Module.finBasis ℝ F j))
      (TestFunction.postcompCLM (LinearMap.toContinuousLinearMap ((Module.finBasis ℝ F).coord j))
        (TestFunction.ofSupportedIn (Ω := ⟨(A.chart i).target, (A.chart i).open_target⟩)
          (A.chartSupport_subset_target i)
          (A.localizationCLM i _ (A.tsupport_cutoff_mul_subset i) s))) =
      TestFunction.ofSupportedIn (Ω := ⟨(A.chart i).target, (A.chart i).open_target⟩)
        (A.chartSupport_subset_target i)
        (A.localizationCLM i _ (A.tsupport_cutoff_mul_subset i) s) := by
    ext y
    simp only [_root_.sum_apply, TestFunction.postcompCLM_apply,
      Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    exact (Module.finBasis ℝ F).sum_repr _
  have hi : ∑ i, (A.trivialization i).chartTestCLM (A.chart i) (A.contMDiffOn_chart i)
      (A.source_subset i) (TestFunction.ofSupportedIn (A.chartSupport_subset_target i)
        (A.localizationCLM i _ (A.tsupport_cutoff_mul_subset i) s)) = s := by
    ext x
    have h : ∑ i, (A.cutoff i * A.cutoff i) x = 1 := by
      simpa only [sq, ContMDiffMap.coe_mul, Pi.mul_apply] using A.sum_sq_cutoff x
    simp only [BundleTest.sum_apply, chartTestCLM_localizationCLM, ← Finset.sum_smul, h, one_smul]
  rw [reconstruction_apply, Fintype.sum_prod_type]
  simp only [localization_apply_testLocalization, ofReal_re, ← map_sum, hj, hi]

/-- **Functionals on bundle tests are determined by their localizations.** -/
theorem ext_localization {T T' : BundleTest I F V →L_c[ℝ] ℝ}
    (h : ∀ i j, A.localization i j T = A.localization i j T') : T = T' := by
  rw [← A.reconstruction_localization T, ← A.reconstruction_localization T']
  exact congrArg A.reconstruction (funext fun k ↦ h k.1 k.2)

/-- The value of a localization on a Schwartz function only involves the values of `T` on two
bundle tests, which do not depend on `T`. -/
private theorem exists_localization_apply (i : ι) (j : Fin (Module.finrank ℝ F)) (ψ : 𝓢(E, ℂ)) :
    ∃ g g' : BundleTest I F V, ∀ T : BundleTest I F V →L_c[ℝ] ℝ,
      A.localization i j T ψ = (T g : ℂ) + Complex.I * (T g' : ℂ) :=
  ⟨_, _, fun T ↦ by
    rw [localization_apply, Distribution.cutoffTempered_def, Distribution.complexPairing_apply,
      Bundle.Trivialization.chartComponent_apply, Bundle.Trivialization.chartComponent_apply]⟩

/-! ### Sobolev regularity and the Sobolev spaces -/

section Sobolev

open scoped BesselPotentialSpace

variable [MeasurableSpace E] [BorelSpace E]

/-- A real functional `T` on bundle tests, for instance a distributional section of the bundle,
is **`H^s` with respect to the square chart partition `A`** when each of its localizations
`χᵢ Tᵢⱼ` (`TauCeti.SquareChartPartition.localization`) lies in the Bessel-potential space
`H^s(E, ℂ)`. -/
def MemSobolev (s : ℝ) (T : BundleTest I F V →L_c[ℝ] ℝ) : Prop :=
  ∀ i j, (A.localization i j T).MemSobolev s 2

theorem memSobolev_iff {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} :
    A.MemSobolev s T ↔ ∀ i j, (A.localization i j T).MemSobolev s 2 :=
  Iff.rfl

variable {A} in
theorem MemSobolev.localization {s : ℝ} {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T)
    (i : ι) (j : Fin (Module.finrank ℝ F)) : (A.localization i j T).MemSobolev s 2 :=
  hT i j

variable {A} in
theorem MemSobolev.mono {s r : ℝ} (h : r ≤ s) {T : BundleTest I F V →L_c[ℝ] ℝ}
    (hT : A.MemSobolev s T) : A.MemSobolev r T :=
  fun i j ↦ (hT i j).mono h

/-- **Finite order.** Every real functional on bundle tests, for instance every distributional
section of the bundle, is `H^s` with respect to `A` for some `s`: its finitely many localizations
are compactly supported distributions, each of which lies in some `H^s(E, ℂ)`. -/
theorem exists_memSobolev (T : BundleTest I F V →L_c[ℝ] ℝ) : ∃ s, A.MemSobolev s T := by
  choose r hr using fun k : ι × Fin (Module.finrank ℝ F) ↦
    Distribution.exists_memSobolev_cutoffTempered ((A.trivialization k.1).chartComponent
      (A.chart k.1) (A.contMDiffOn_chart k.1) (A.source_subset k.1) T (Module.finBasis ℝ F k.2))
      (A.chartCutoff k.1)
  refine ⟨-∑ k, |r k|, fun i j ↦ ?_⟩
  rw [localization_apply]
  refine (hr (i, j)).mono ?_
  -- `-∑ₖ |rₖ| ≤ -|rᵢⱼ| ≤ rᵢⱼ`.
  have := Finset.single_le_sum (fun k _ ↦ abs_nonneg (r k)) (Finset.mem_univ (i, j))
  linarith [neg_abs_le (r (i, j))]

variable (s : ℝ)

/-- The functionals on bundle tests that are `H^s` with respect to `A`, as a real subspace. -/
def memSobolevSubmodule : Submodule ℝ (BundleTest I F V →L_c[ℝ] ℝ) where
  carrier := {T | A.MemSobolev s T}
  add_mem' {T T'} hT hT' i j := by
    rw [map_add]
    exact (hT i j).add (hT' i j)
  zero_mem' i j := by
    rw [map_zero]
    exact TemperedDistribution.memSobolev_fun_zero E ℂ s 2
  smul_mem' a T hT i j := by
    rw [map_smul]
    exact TemperedDistribution.MemSobolev.smul_of_tower a (hT i j)

theorem mem_memSobolevSubmodule {T : BundleTest I F V →L_c[ℝ] ℝ} :
    T ∈ A.memSobolevSubmodule s ↔ A.MemSobolev s T :=
  Iff.rfl

/-- The **Sobolev space `H^s` of a vector bundle** with respect to the square chart partition `A`,
realized as the tuples `(uᵢⱼ)` in the Hilbert sum `⨁ᵢⱼ H^s(E, ℂ)` that are localizations of a
functional on bundle tests: those reproduced by localizing their reconstruction. It is a closed
subspace (`TauCeti.SquareChartPartition.isClosed_sobolevSpace`), hence complete, and its norm is
the pinned norm `‖u‖² = ∑ᵢⱼ ‖uᵢⱼ‖²_{H^s}` of the Hilbert sum. The functional represented by `u`
is `TauCeti.SquareChartPartition.toDistribution`. -/
def sobolevSpace :
    Submodule ℝ (PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)) where
  carrier := {u | ∀ k, A.localization k.1 k.2 (A.reconstruction fun l ↦ (u l).toDistr) =
    (u k).toDistr}
  add_mem' {u u'} hu hu' k := by
    simp only [PiLp.add_apply, BesselPotentialSpace.toDistr_add]
    rw [← Pi.add_def, map_add, map_add, hu k, hu' k]
  zero_mem' k := by
    simp only [PiLp.zero_apply, BesselPotentialSpace.toDistr_zero]
    rw [← Pi.zero_def, map_zero, map_zero]
  smul_mem' a u hu k := by
    -- The tempered distributions of the components of `a • u` are, by definition of the scalar
    -- action on `PiLp` and on `H^s`, those of `u` multiplied by `a`.
    change A.localization k.1 k.2 (A.reconstruction (a • fun l ↦ (u l).toDistr)) =
      a • (u k).toDistr
    rw [map_smul, map_smul, hu k]

theorem mem_sobolevSpace {u : PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)} :
    u ∈ A.sobolevSpace s ↔
      ∀ k, A.localization k.1 k.2 (A.reconstruction fun l ↦ (u l).toDistr) = (u k).toDistr :=
  Iff.rfl

/-- The `H^s` spaces of `A` are closed in the Hilbert sum `⨁ᵢⱼ H^s(E, ℂ)`. -/
theorem isClosed_sobolevSpace :
    IsClosed
      (A.sobolevSpace s : Set (PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ))) := by
  have hcont (k : ι × Fin (Module.finrank ℝ F)) (ψ : 𝓢(E, ℂ)) :
      Continuous fun u : PiLp 2 (fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ)) ↦
        (u k).toDistr ψ :=
    (ContinuousEvalConst.continuous_eval_const ψ).comp
      (BesselPotentialSpace.continuous_toDistr.comp (PiLp.continuous_apply 2 _ k))
  have h : (A.sobolevSpace s : Set (PiLp 2 fun _ : ι × Fin (Module.finrank ℝ F) ↦ H^{s}(E, ℂ))) =
      ⋂ k, ⋂ ψ : 𝓢(E, ℂ),
      {u | A.localization k.1 k.2 (A.reconstruction fun l ↦ (u l).toDistr) ψ =
        (u k).toDistr ψ} := by
    ext u
    simp only [SetLike.mem_coe, mem_sobolevSpace, mem_iInter, Set.mem_ofPred_eq]
    exact forall_congr' fun k ↦ ⟨fun h ψ ↦ by rw [h], fun h ↦ ContinuousLinearMap.ext h⟩
  rw [h]
  refine isClosed_iInter fun k ↦ isClosed_iInter fun ψ ↦ isClosed_eq ?_ (hcont k ψ)
  obtain ⟨g, g', hg⟩ := A.exists_localization_apply k.1 k.2 ψ
  simp only [hg, reconstruction_apply]
  refine ((continuous_ofReal.comp ?_).add (continuous_const.mul (continuous_ofReal.comp ?_))) <;>
    exact continuous_finsetSum _ fun l _ ↦ continuous_re.comp (hcont l _)

instance : CompleteSpace (A.sobolevSpace s) :=
  (A.isClosed_sobolevSpace s).completeSpace_coe

/-- The functional on bundle tests represented by an element of the Sobolev space
`TauCeti.SquareChartPartition.sobolevSpace`: the reconstruction of its components. -/
def toDistribution : A.sobolevSpace s →ₗ[ℝ] (BundleTest I F V →L_c[ℝ] ℝ) where
  toFun u := A.reconstruction fun l ↦ (u.val l).toDistr
  map_add' u u' := by
    rw [← map_add]
    congr 1
  map_smul' a u := by
    rw [RingHom.id_apply, ← map_smul]
    congr 1

/-- The localizations of the functional represented by `u` are the components of `u`. -/
@[simp]
theorem localization_toDistribution (u : A.sobolevSpace s) (k : ι × Fin (Module.finrank ℝ F)) :
    A.localization k.1 k.2 (A.toDistribution s u) = (u.val k).toDistr :=
  u.property k

theorem memSobolev_toDistribution (u : A.sobolevSpace s) :
    A.MemSobolev s (A.toDistribution s u) := fun i j ↦ by
  rw [A.localization_toDistribution s u (i, j)]
  exact BesselPotentialSpace.memSobolev_toDistr _

theorem toDistribution_injective : Function.Injective (A.toDistribution s) := fun u u' h ↦
  Subtype.ext <| PiLp.ext fun k ↦ BesselPotentialSpace.ext <| by
    rw [← A.localization_toDistribution s u k, ← A.localization_toDistribution s u' k, h]

/-- The element of the Sobolev space representing a functional which is `H^s` with respect to
`A`: the tuple of its localizations. -/
def ofMemSobolev {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T) : A.sobolevSpace s :=
  ⟨WithLp.toLp 2 fun k ↦ (hT k.1 k.2).toBesselPotentialSpace, fun k ↦ by
    simp only [TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr,
      reconstruction_localization]⟩

@[simp]
theorem ofMemSobolev_apply {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T)
    (k : ι × Fin (Module.finrank ℝ F)) :
    (A.ofMemSobolev s hT).val k = (hT.localization k.1 k.2).toBesselPotentialSpace :=
  (rfl)

@[simp]
theorem toDistribution_ofMemSobolev {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T) :
    A.toDistribution s (A.ofMemSobolev s hT) = T := by
  simp only [toDistribution, ofMemSobolev, LinearMap.coe_mk, AddHom.coe_mk,
    TemperedDistribution.MemSobolev.toBesselPotentialSpace_toDistr, reconstruction_localization]

/-- The functionals represented by the Sobolev space are exactly those which are `H^s` with
respect to `A`. -/
theorem range_toDistribution : LinearMap.range (A.toDistribution s) = A.memSobolevSubmodule s :=
  Submodule.ext fun _ ↦ ⟨by rintro ⟨u, rfl⟩; exact A.memSobolev_toDistribution s u,
    fun hT ↦ ⟨_, A.toDistribution_ofMemSobolev s hT⟩⟩

/-- The Sobolev space is linearly equivalent to the space of functionals on bundle tests that are
`H^s` with respect to `A`. -/
def sobolevSpaceEquiv : A.sobolevSpace s ≃ₗ[ℝ] A.memSobolevSubmodule s :=
  (LinearEquiv.ofInjective _ (A.toDistribution_injective s)).trans
    (LinearEquiv.ofEq _ _ (A.range_toDistribution s))

@[simp]
theorem coe_sobolevSpaceEquiv_apply (u : A.sobolevSpace s) :
    (A.sobolevSpaceEquiv s u : BundleTest I F V →L_c[ℝ] ℝ) = A.toDistribution s u :=
  (rfl)

/-- **The pinned norm.** The squared `H^s` norm of a functional which is `H^s` with respect to `A`
is the sum of the squared `H^s(E, ℂ)` norms of its localizations `χᵢ Tᵢⱼ`. -/
theorem norm_ofMemSobolev_sq {T : BundleTest I F V →L_c[ℝ] ℝ} (hT : A.MemSobolev s T) :
    ‖A.ofMemSobolev s hT‖ ^ 2 = ∑ i, ∑ j, ‖(hT.localization i j).toBesselPotentialSpace‖ ^ 2 := by
  rw [← Submodule.norm_coe, PiLp.norm_sq_eq_of_L2, Fintype.sum_prod_type]
  simp only [ofMemSobolev_apply]

end Sobolev

end SquareChartPartition

end TauCeti
