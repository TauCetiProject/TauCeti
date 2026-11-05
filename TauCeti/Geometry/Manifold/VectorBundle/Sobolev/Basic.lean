/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.Topology.VectorBundle.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Basic

/-!
# Sobolev spaces of sections of a vector bundle

Let `M` be a `C¹` manifold without boundary modelled on a finite-dimensional real inner product
space `E`, and let `V → M` be a real vector bundle with finite-dimensional model fibre `F`. This
file constructs the Banach space `W^{k,p}(V)` of sections of `V` whose coordinates in finitely many
bundle charts are Sobolev functions of order `k`, for every natural number `k` and `1 ≤ p ≤ ∞`.

The charts are fixed by a `TauCeti.FiniteBundleAtlas`: finitely many open sets `dom i` covering
`M`, each with compact closure inside the domain of the preferred manifold chart and bundle
trivialization at a point `center i`. Every compact Hausdorff manifold has one
(`TauCeti.FiniteBundleAtlas.nonempty`). In chart
`i` a section `s` is read as the `F`-valued function `A.coord i s` on the open set
`A.image i = chart i '' dom i` of `E`. Fixing a basis of `F`, an element of the space is a tuple of
scalar Sobolev functions `w i j ∈ W^{k,p}(A.image i)` (the components in chart `i`), one for each
chart and each basis vector, that are the components of a single section: there is a section `s`
with `A.chartValue w i = A.coord i s` almost everywhere on `A.image i` for every `i`, with respect
to the Haar measure `μ` of `E`. These tuples form the submodule `TauCeti.sobolevSections A μ p k`
of the finite product of scalar Sobolev spaces, and `TauCeti.SobolevSection A μ p k` carries the
product norm, the maximum of the chartwise component norms.

The main result is that this submodule is closed (`TauCeti.isClosed_sobolevSections`), so that
`W^{k,p}(V)` is a Banach space. Being the components of a section is equivalent to the chart data
satisfying the cocycle relation on every overlap: on `chart i' '' (dom i ∩ dom i')` the chart-`i'`
data are the coordinate change of the bundle applied to the chart-`i` data composed with the chart
transition (`TauCeti.FiniteBundleAtlas.mem_sobolevSections_iff_forall_compatible`). In one
direction a section is glued from the chart data, using any choice of chart at each point; in the
other the relation is read off from the section, which needs that chart transitions, being `C¹`
diffeomorphisms between open sets, carry null sets to null sets
(`TauCeti.FiniteBundleAtlas.ae_restrict_overlap_transition`). Each relation is closed in the
product of Sobolev spaces, because convergence in `Lᵖ` gives almost everywhere convergence along a
subsequence. Forgetting the highest derivative of every component gives the continuous inclusion
`W^{k+1,p}(V) → W^{k,p}(V)` (`TauCeti.SobolevSection.lowerOrderL`).

## Main definitions

* `TauCeti.FiniteBundleAtlas E M F V`: a finite cover of `M` by open sets inside preferred manifold
  and bundle charts.
* `TauCeti.FiniteBundleAtlas.coord`: a section read in chart `i`, as a function on `A.image i`.
* `TauCeti.FiniteBundleAtlas.chartValueL`: the `F`-valued `Lᵖ` function on `A.image i` assembled
  from the chart-`i` Sobolev components of a tuple.
* `TauCeti.sobolevSections A μ p k`: the tuples of chartwise Sobolev components of sections.
* `TauCeti.SobolevSection A μ p k`: the Banach space `W^{k,p}(V)`.

## Main results

* `TauCeti.FiniteBundleAtlas.mem_sobolevSections_iff_forall_compatible`: a tuple consists of the
  components of a section exactly when its chart data satisfy the cocycle relations.
* `TauCeti.isClosed_sobolevSections`, `TauCeti.SobolevSection.instCompleteSpace`: completeness.
* `TauCeti.SobolevSection.lowerOrderL`: the continuous inclusion `W^{k+1,p}(V) → W^{k,p}(V)`.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton (1989), Chapter III, §2.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold Topology ENNReal

universe u

namespace TauCeti

section Atlas

variable (E : Type u) [TopologicalSpace E] (M : Type*) [TopologicalSpace M] [ChartedSpace E M]
  (F : Type*) [TopologicalSpace F] (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

/-- A finite atlas of bundle charts: finitely many open sets `dom i` covering `M`, each with compact
closure contained in the source of the preferred manifold chart `chartAt E (center i)` and in the
base set of the preferred trivialization `trivializationAt F V (center i)`. Relative compactness
keeps every chart transition and coordinate change, with all its derivatives, bounded on the chart
domains. -/
structure FiniteBundleAtlas where
  /-- The number of charts. -/
  n : ℕ
  /-- The point whose preferred charts are used for the `i`th chart. -/
  center : Fin n → M
  /-- The domain of the `i`th chart. -/
  dom : Fin n → Set M
  isOpen_dom : ∀ i, IsOpen (dom i)
  isCompact_closure_dom : ∀ i, IsCompact (closure (dom i))
  closure_dom_subset_source : ∀ i, closure (dom i) ⊆ (chartAt E (center i)).source
  closure_dom_subset_baseSet : ∀ i, closure (dom i) ⊆ (trivializationAt F V (center i)).baseSet
  iUnion_dom : ⋃ i, dom i = univ

variable {E M F V}

namespace FiniteBundleAtlas

/-- A compact Hausdorff manifold modelled on a locally compact space has a finite bundle atlas. -/
theorem nonempty [LocallyCompactSpace E] [CompactSpace M] [T2Space M] :
    Nonempty (FiniteBundleAtlas E M F V) := by
  have := ChartedSpace.locallyCompactSpace E M
  let U : M → Set M := fun x ↦ (chartAt E x).source ∩ (trivializationAt F V x).baseSet
  have hU (x : M) : IsOpen (U x) :=
    (chartAt E x).open_source.inter (trivializationAt F V x).open_baseSet
  have hxU (x : M) : x ∈ U x := ⟨mem_chart_source E x, mem_baseSet_trivializationAt F V x⟩
  -- Shrink each `U x` to the interior of a compact neighbourhood of `x` inside it.
  choose K hK hxK hKU using fun x ↦ exists_compact_subset (hU x) (hxU x)
  have hcl (x : M) : closure (interior (K x)) ⊆ U x :=
    (closure_mono interior_subset).trans ((hK x).isClosed.closure_subset.trans (hKU x))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x ↦ interior (K x))
    (fun x ↦ isOpen_interior) fun x _ ↦ mem_iUnion.2 ⟨x, hxK x⟩
  let c : Fin t.card → M := fun i ↦ (t.equivFin.symm i).1
  refine ⟨⟨t.card, c, fun i ↦ interior (K (c i)), fun i ↦ isOpen_interior,
    fun i ↦ (hK _).closure_of_subset interior_subset, fun i ↦ (hcl _).trans inter_subset_left,
    fun i ↦ (hcl _).trans inter_subset_right, eq_univ_of_forall fun x ↦ ?_⟩⟩
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.1 (ht (mem_univ x))
  exact mem_iUnion.2 ⟨t.equivFin ⟨y, hy⟩, by simpa [c] using hxy⟩

variable (A : FiniteBundleAtlas E M F V)

/-- The manifold chart of the `i`th bundle chart. -/
abbrev chart (i : Fin A.n) : OpenPartialHomeomorph M E :=
  chartAt E (A.center i)

/-- The bundle trivialization of the `i`th bundle chart. -/
abbrev triv (i : Fin A.n) : Trivialization F (π F V) :=
  trivializationAt F V (A.center i)

theorem dom_subset_chart_source (i : Fin A.n) : A.dom i ⊆ (A.chart i).source :=
  subset_closure.trans (A.closure_dom_subset_source i)

theorem dom_subset_baseSet (i : Fin A.n) : A.dom i ⊆ (A.triv i).baseSet :=
  subset_closure.trans (A.closure_dom_subset_baseSet i)

theorem exists_mem_dom (x : M) : ∃ i, x ∈ A.dom i :=
  mem_iUnion.1 (A.iUnion_dom ▸ mem_univ x)

/-- The open set `chart i '' dom i` of the model space on which sections are read in chart `i`. -/
def image (i : Fin A.n) : Opens E :=
  ⟨A.chart i '' A.dom i, (A.chart i).isOpen_image_of_subset_source (A.isOpen_dom i)
    (A.dom_subset_chart_source i)⟩

theorem mem_image {i : Fin A.n} {y : E} : y ∈ A.image i ↔ y ∈ A.chart i '' A.dom i :=
  Iff.rfl

/-- The overlap of the domains of charts `i` and `i'`, in the coordinates of chart `i'`. -/
def overlap (i i' : Fin A.n) : Set E :=
  A.chart i' '' (A.dom i ∩ A.dom i')

theorem isOpen_overlap (i i' : Fin A.n) : IsOpen (A.overlap i i') :=
  (A.chart i').isOpen_image_of_subset_source ((A.isOpen_dom i).inter (A.isOpen_dom i'))
    (inter_subset_right.trans (A.dom_subset_chart_source i'))

theorem overlap_subset_image (i i' : Fin A.n) : A.overlap i i' ⊆ A.image i' :=
  image_mono inter_subset_right

/-- The chart transition from chart `i'` to chart `i`. -/
def transition (i i' : Fin A.n) (y : E) : E :=
  A.chart i ((A.chart i').symm y)

theorem transition_chart {i i' : Fin A.n} {x : M} (hx : x ∈ A.dom i') :
    A.transition i i' (A.chart i' x) = A.chart i x := by
  rw [transition, (A.chart i').left_inv (A.dom_subset_chart_source i' hx)]

theorem transition_mem_overlap {i i' : Fin A.n} {y : E} (hy : y ∈ A.overlap i i') :
    A.transition i i' y ∈ A.overlap i' i := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [transition_chart A hx.2]
  exact ⟨x, ⟨hx.2, hx.1⟩, rfl⟩

theorem transition_transition {i i' : Fin A.n} {y : E} (hy : y ∈ A.overlap i i') :
    A.transition i' i (A.transition i i' y) = y := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [transition_chart A hx.2, transition_chart A hx.1]

/-- A section read in chart `i`: its coordinates in the trivialization of chart `i`, as a function
on the model space of `M`. -/
def coord (i : Fin A.n) (s : ∀ x, V x) (y : E) : F :=
  (A.triv i ⟨(A.chart i).symm y, s ((A.chart i).symm y)⟩).2

theorem coord_chart {i : Fin A.n} (s : ∀ x, V x) {x : M} (hx : x ∈ A.dom i) :
    A.coord i s (A.chart i x) = (A.triv i ⟨x, s x⟩).2 := by
  rw [coord, (A.chart i).left_inv (A.dom_subset_chart_source i hx)]

theorem symm_mem_dom {i : Fin A.n} {y : E} (hy : y ∈ A.image i) : (A.chart i).symm y ∈ A.dom i := by
  obtain ⟨x, hx, rfl⟩ := hy
  rwa [(A.chart i).left_inv (A.dom_subset_chart_source i hx)]

end FiniteBundleAtlas

end Atlas

section Coordinates

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {F : Type*} [TopologicalSpace F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas E M F V)

/-- Chart transitions are differentiable on the overlap of the chart domains. -/
theorem differentiableOn_transition [IsManifold 𝓘(ℝ, E) 1 M] (i i' : Fin A.n) :
    DifferentiableOn ℝ (A.transition i i') (A.overlap i i') := by
  refine ((contDiffOn_ext_coord_change (I := 𝓘(ℝ, E)) (A.center i) (A.center i')).differentiableOn
    one_ne_zero).congr_mono (fun y _ ↦ by simp [transition]) ?_
  rintro _ ⟨x, hx, rfl⟩
  have hx' : x ∈ (A.chart i').source := A.dom_subset_chart_source i' hx.2
  simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage,
    extChartAt_target, extChartAt_source, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq, range_id, inter_univ,
    preimage_id_eq]
  exact ⟨(A.chart i').map_source hx', by
    rw [(A.chart i').left_inv hx']; exact A.dom_subset_chart_source i hx.1⟩

/-- **Chart transitions preserve null sets.** A property holding almost everywhere on the image of
chart `i` holds, after composition with the chart transition, almost everywhere on the overlap of
charts `i` and `i'` read in chart `i'`. -/
theorem ae_restrict_overlap_transition [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [μ.IsAddHaarMeasure] [IsManifold 𝓘(ℝ, E) 1 M] {i i' : Fin A.n} {P : E → Prop}
    (h : ∀ᵐ z ∂μ.restrict (A.image i), P z) :
    ∀ᵐ y ∂μ.restrict (A.overlap i i'), P (A.transition i i' y) := by
  have hN : μ ({z | ¬P z} ∩ A.overlap i' i) = 0 := by
    rw [ae_iff, Measure.restrict_apply' (A.image i).isOpen.measurableSet] at h
    exact measure_mono_null (inter_subset_inter_right _ (A.overlap_subset_image i' i)) h
  have himage := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
    ((A.differentiableOn_transition i' i).mono inter_subset_right) hN
  rw [ae_iff, Measure.restrict_apply' (A.isOpen_overlap i i').measurableSet]
  refine measure_mono_null (fun y hy ↦ ?_) himage
  exact ⟨A.transition i i' y, ⟨hy.1, A.transition_mem_overlap hy.2⟩,
    A.transition_transition hy.2⟩

end FiniteBundleAtlas

end Coordinates

section Linear

variable {E : Type u} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

namespace FiniteBundleAtlas

variable (A : FiniteBundleAtlas E M F V)

theorem coord_add (i : Fin A.n) (s t : ∀ x, V x) {y : E} (hy : y ∈ A.image i) :
    A.coord i (s + t) y = A.coord i s y + A.coord i t y := by
  have h := A.dom_subset_baseSet i (A.symm_mem_dom hy)
  simp only [coord, Pi.add_apply, ← (A.triv i).continuousLinearMapAt_apply_of_mem (R := ℝ) h,
    map_add]

theorem coord_smul (i : Fin A.n) (c : ℝ) (s : ∀ x, V x) {y : E} (hy : y ∈ A.image i) :
    A.coord i (c • s) y = c • A.coord i s y := by
  have h := A.dom_subset_baseSet i (A.symm_mem_dom hy)
  simp only [coord, Pi.smul_apply, ← (A.triv i).continuousLinearMapAt_apply_of_mem (R := ℝ) h,
    map_smul]

theorem coord_zero (i : Fin A.n) {y : E} (hy : y ∈ A.image i) : A.coord i (0 : ∀ x, V x) y = 0 := by
  simpa using A.coord_smul i 0 0 hy

/-- On the overlap of two charts, the coordinates of a section in chart `i'` are the coordinate
change applied to its coordinates in chart `i` at the transition point. -/
theorem coord_eq_coordChange {i i' : Fin A.n} (s : ∀ x, V x) {y : E} (hy : y ∈ A.overlap i i') :
    A.coord i' s y = (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
      (A.coord i s (A.transition i i' y)) := by
  obtain ⟨x, hx, rfl⟩ := hy
  rw [transition_chart A hx.2, coord_chart A s hx.1, coord_chart A s hx.2,
    (A.chart i').left_inv (A.dom_subset_chart_source i' hx.2),
    Trivialization.coordChangeL_apply _ _
      ⟨A.dom_subset_baseSet i hx.1, A.dom_subset_baseSet i' hx.2⟩,
    (A.triv i).symm_apply_apply_mk (A.dom_subset_baseSet i hx.1)]

end FiniteBundleAtlas

end Linear

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]

variable (A : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞)
  [Fact (1 ≤ p)] (k : ℕ)

/-- Tuples of scalar Sobolev functions of order `k`, one on the image of each chart for each vector
of the standard basis `Module.finBasis ℝ F` of the model fibre. -/
abbrev SobolevData : Type u :=
  ∀ (i : Fin A.n) (_ : Fin (finrank ℝ F)), Wkp μ (A.image i) p k

namespace FiniteBundleAtlas

/-- The `F`-valued `Lᵖ` function on the image of chart `i` whose components in the basis
`Module.finBasis ℝ F` are the values of the chart-`i` entries of a tuple of Sobolev functions. -/
def chartValueL (i : Fin A.n) : SobolevData A μ p k →L[ℝ] Lp F p (μ.restrict (A.image i)) :=
  ∑ j, ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j)).compLpL p _).comp
    ((Wkp.valueL k).comp ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (finrank ℝ F) ↦ Wkp μ (A.image i) p k) j).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun i : Fin A.n ↦ ∀ _ : Fin (finrank ℝ F), Wkp μ (A.image i) p k) i)))

omit [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- Almost everywhere on the image of chart `i`, the chart data of a tuple are the combination of
the basis vectors of `F` with the values of its chart-`i` components. -/
theorem chartValueL_apply_ae (i : Fin A.n) (w : SobolevData A μ p k) :
    ∀ᵐ y ∂μ.restrict (A.image i),
      A.chartValueL μ p k i w y = ∑ j, Wkp.value k (w i j) y • finBasis ℝ F j := by
  have heq : A.chartValueL μ p k i w = ∑ j,
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j)).compLpL p _
        (Wkp.value k (w i j)) := by
    simp [chartValueL]
  have hsum := Lp.coeFn_finsetSum (μ := μ.restrict (A.image i)) (p := p) Finset.univ fun j ↦
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j)).compLpL p _
      (Wkp.value k (w i j))
  have hj (j : Fin (finrank ℝ F)) := ContinuousLinearMap.coeFn_compLpL (p := p)
    (μ := μ.restrict (A.image i)) (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j))
    (Wkp.value k (w i j))
  filter_upwards [hsum, ae_all_iff.2 hj] with y hy hy'
  rw [heq, hy, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ ↦ by simp [hy' j]

omit [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V] in
/-- Forgetting the highest derivative of every component does not change the chart data. -/
theorem chartValueL_lowerOrderL (i : Fin A.n) (w : SobolevData A μ p (k + 1)) :
    A.chartValueL μ p k i (fun i j ↦ Wkp.lowerOrderL k (w i j)) =
      A.chartValueL μ p (k + 1) i w := by
  simp only [chartValueL, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Wkp.valueL_apply, Wkp.valueL_apply, Wkp.value_succ, Wkp.lowerOrderL_apply]

/-- The chart-`i'` data of a tuple are related to its chart-`i` data by the coordinate change of
the bundle on the overlap of the two charts, almost everywhere. -/
def Compatible (w : SobolevData A μ p k) (i i' : Fin A.n) : Prop :=
  ∀ᵐ y ∂μ.restrict (A.overlap i i'), A.chartValueL μ p k i' w y =
    (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
      (A.chartValueL μ p k i w (A.transition i i' y))

end FiniteBundleAtlas

open FiniteBundleAtlas

/-- The tuples of chartwise Sobolev components of sections of `V`: a tuple `w` belongs to it when
some section `s` has, in every chart `i`, coordinates equal almost everywhere on `A.image i` to the
function assembled from the chart-`i` components of `w`. -/
def sobolevSections : Submodule ℝ (SobolevData A μ p k) where
  carrier := {w | ∃ s : ∀ x, V x, ∀ i,
    A.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s}
  add_mem' {w w'} := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s + t, fun i ↦ ?_⟩
    filter_upwards [hs i, ht i, ae_restrict_mem (A.image i).isOpen.measurableSet,
      Lp.coeFn_add (A.chartValueL μ p k i w) (A.chartValueL μ p k i w')] with y hy ht hyU hadd
    rw [map_add, hadd, Pi.add_apply, hy, ht, A.coord_add i s t hyU]
  zero_mem' := ⟨0, fun i ↦ by
    filter_upwards [ae_restrict_mem (A.image i).isOpen.measurableSet,
      Lp.coeFn_zero F p (μ.restrict (A.image i))] with y hyU h0
    rw [map_zero, h0, Pi.zero_apply, A.coord_zero i hyU]⟩
  smul_mem' c w := by
    rintro ⟨s, hs⟩
    refine ⟨c • s, fun i ↦ ?_⟩
    filter_upwards [hs i, ae_restrict_mem (A.image i).isOpen.measurableSet,
      Lp.coeFn_smul c (A.chartValueL μ p k i w)] with y hy hyU hsmul
    rw [map_smul, hsmul, Pi.smul_apply, hy, A.coord_smul i c s hyU]

theorem mem_sobolevSections_iff {w : SobolevData A μ p k} :
    w ∈ sobolevSections A μ p k ↔
      ∃ s : ∀ x, V x, ∀ i, A.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s :=
  Iff.rfl

namespace FiniteBundleAtlas

variable {A μ p k} [IsManifold 𝓘(ℝ, E) 1 M]

/-- The components of a section satisfy the cocycle relation on every overlap. -/
theorem compatible_of_mem {w : SobolevData A μ p k} (hw : w ∈ sobolevSections A μ p k)
    (i i' : Fin A.n) : A.Compatible μ p k w i i' := by
  obtain ⟨s, hs⟩ := hw
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (A.overlap_subset_image i i') (hs i'),
    A.ae_restrict_overlap_transition (i' := i') (hs i),
    ae_restrict_mem (A.isOpen_overlap i i').measurableSet] with y h' h hy
  rw [h', h, A.coord_eq_coordChange s hy]

omit [IsManifold 𝓘(ℝ, E) 1 M] in
/-- **Gluing.** Chart data satisfying the cocycle relation on every overlap are the components of
a section. At each point the section is read off from the data of any chart containing it. -/
theorem mem_of_forall_compatible {w : SobolevData A μ p k}
    (hw : ∀ i i', A.Compatible μ p k w i i') : w ∈ sobolevSections A μ p k := by
  classical
  let idx : M → Fin A.n := fun x ↦ (A.exists_mem_dom x).choose
  have hidx (x : M) : x ∈ A.dom (idx x) := (A.exists_mem_dom x).choose_spec
  let s : ∀ x, V x := fun x ↦
    (A.triv (idx x)).symm x (A.chartValueL μ p k (idx x) w (A.chart (idx x) x))
  refine ⟨s, fun i' ↦ ?_⟩
  have hall : ∀ᵐ y ∂μ.restrict (A.image i'), ∀ i, y ∈ A.overlap i i' →
      A.chartValueL μ p k i' w y = (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
        (A.chartValueL μ p k i w (A.transition i i' y)) := by
    rw [ae_all_iff]
    intro i
    exact ae_restrict_of_ae ((ae_restrict_iff' (A.isOpen_overlap i i').measurableSet).1 (hw i i'))
  filter_upwards [hall, ae_restrict_mem (A.image i').isOpen.measurableSet] with y hy hyU
  obtain ⟨x, hx, rfl⟩ := hyU
  have hxi := hidx x
  have hov : A.chart i' x ∈ A.overlap (idx x) i' := ⟨x, ⟨hxi, hx⟩, rfl⟩
  rw [hy (idx x) hov, A.coord_eq_coordChange s hov, A.transition_chart hx,
    A.coord_chart s hxi, (A.chart i').left_inv (A.dom_subset_chart_source i' hx)]
  simp only [s]
  rw [(A.triv (idx x)).apply_mk_symm (A.dom_subset_baseSet _ hxi)]

/-- A tuple consists of the chartwise Sobolev components of a section exactly when its chart data
satisfy the cocycle relation on every overlap. -/
theorem mem_sobolevSections_iff_forall_compatible {w : SobolevData A μ p k} :
    w ∈ sobolevSections A μ p k ↔ ∀ i i', A.Compatible μ p k w i i' :=
  ⟨compatible_of_mem, mem_of_forall_compatible⟩

/-- Each cocycle relation is a closed condition on tuples of Sobolev functions: convergence in
`Lᵖ` gives almost everywhere convergence along a subsequence. -/
theorem isClosed_setOf_compatible (i i' : Fin A.n) :
    IsClosed {w : SobolevData A μ p k | A.Compatible μ p k w i i'} := by
  refine IsSeqClosed.isClosed fun {w w₀} hw hlim ↦ ?_
  have hc (j : Fin A.n) : Tendsto (fun m ↦ A.chartValueL μ p k j (w m)) atTop
      (𝓝 (A.chartValueL μ p k j w₀)) :=
    ((A.chartValueL μ p k j).continuous.tendsto w₀).comp hlim
  -- Almost everywhere convergence of the chart-`i'` data along a subsequence, then of the
  -- chart-`i` data along a further subsequence.
  obtain ⟨ns, hns, hae'⟩ := (tendstoInMeasure_of_tendsto_Lp (hc i')).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((hc i).comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hrel : ∀ᵐ y ∂μ.restrict (A.overlap i i'), ∀ m, A.chartValueL μ p k i' (w m) y =
      (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
        (A.chartValueL μ p k i (w m) (A.transition i i' y)) :=
    ae_all_iff.2 fun m ↦ by simpa only [mem_ofPred_eq, Compatible] using hw m
  simp only [mem_ofPred_eq, Compatible]
  filter_upwards [hrel, ae_restrict_of_ae_restrict_of_subset (A.overlap_subset_image i i') hae',
    A.ae_restrict_overlap_transition (i' := i') hae] with y hy h' h
  refine tendsto_nhds_unique (h'.comp hms.tendsto_atTop) ?_
  refine ((((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)).continuous.tendsto
    _).comp h).congr fun m ↦ ?_
  exact (hy (ns (ms m))).symm

end FiniteBundleAtlas

variable [IsManifold 𝓘(ℝ, E) 1 M]

/-- The chartwise Sobolev components of sections form a closed subspace of the product of scalar
Sobolev spaces. -/
theorem isClosed_sobolevSections :
    IsClosed (sobolevSections A μ p k : Set (SobolevData A μ p k)) := by
  have : (sobolevSections A μ p k : Set (SobolevData A μ p k)) =
      ⋂ i, ⋂ i', {w | A.Compatible μ p k w i i'} := by
    ext w
    simp only [SetLike.mem_coe, mem_sobolevSections_iff_forall_compatible, mem_iInter,
      mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun i' ↦ isClosed_setOf_compatible i i'

/-- The Sobolev space `W^{k,p}(V)` of sections of `V` with respect to the finite bundle atlas `A`:
the tuples of chartwise Sobolev components of sections, with the maximum of the component norms. -/
abbrev SobolevSection : Type u :=
  sobolevSections A μ p k

/-- **Completeness.** The Sobolev space of sections of a vector bundle is a Banach space. -/
instance SobolevSection.instCompleteSpace : CompleteSpace (SobolevSection A μ p k) :=
  (isClosed_sobolevSections A μ p k).completeSpace_coe

namespace SobolevSection

omit [IsManifold 𝓘(ℝ, E) 1 M] in
/-- An element of `W^{k,p}(V)` consists of the chartwise components of a section. -/
theorem exists_section (w : SobolevSection A μ p k) :
    ∃ s : ∀ x, V x, ∀ i, A.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s :=
  w.2

/-- The continuous inclusion `W^{k+1,p}(V) → W^{k,p}(V)`, forgetting the highest derivative of
every component. -/
def lowerOrderL : SobolevSection A μ p (k + 1) →L[ℝ] SobolevSection A μ p k :=
  ((ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun j ↦ (Wkp.lowerOrderL k).comp
    ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (finrank ℝ F) ↦ Wkp μ (A.image i) p (k + 1)) j).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun i : Fin A.n ↦ ∀ _ : Fin (finrank ℝ F), Wkp μ (A.image i) p (k + 1)) i))).comp
    (sobolevSections A μ p (k + 1)).subtypeL).codRestrict (sobolevSections A μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := w.2
      refine ⟨s, fun i ↦ ?_⟩
      convert hs i using 2
      rw [← A.chartValueL_lowerOrderL μ p k i w]
      rfl

omit [IsManifold 𝓘(ℝ, E) 1 M] in
@[simp]
theorem lowerOrderL_apply (w : SobolevSection A μ p (k + 1)) (i : Fin A.n)
    (j : Fin (finrank ℝ F)) :
    (lowerOrderL A μ p k w : SobolevData A μ p k) i j =
      Wkp.lowerOrder k ((w : SobolevData A μ p (k + 1)) i j) := by
  rw [← Wkp.lowerOrderL_apply]
  rfl

end SobolevSection

end Sobolev

end TauCeti
