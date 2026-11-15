/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Analysis.Sobolev.Wkp.Restriction
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Basic
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Sobolev spaces of sections of a vector bundle

Let `M` be a `C¹` manifold without boundary modelled on a finite-dimensional real inner product
space `E`, and let `V → M` be a real vector bundle with finite-dimensional model fibre `F`. This
file constructs the Banach space `W^{k,p}(V)` of sections of `V` whose coordinates in finitely many
bundle charts are Sobolev functions of order `k`, for every natural number `k` and `1 ≤ p ≤ ∞`.

The construction only uses how sections are read in the charts, which is recorded by a
`TauCeti.SectionChartData E F S`: finitely many open sets `C.image i` of `E` on which the elements
`s` of a real vector space `S` of sections are read as `F`-valued functions `C.coord i s`, together
with overlaps `C.overlap i i' ⊆ C.image i'`, chart transitions and linear coordinate changes
relating the readings in charts `i` and `i'` on the overlaps, and a gluing property. Fixing a basis
of `F`, an element of the space is a tuple of scalar Sobolev functions `w i j ∈ W^{k,p}(C.image i)`
(the components in chart `i`), one for each chart and each basis vector, that are the components of
a single section: there is a section `s` with `C.chartValueL μ p k i w = C.coord i s` almost
everywhere on `C.image i` for every `i`, with respect to a Haar measure `μ` of `E`. These tuples
form the submodule `C.sobolevSections μ p k` of the finite product of scalar Sobolev spaces, which
carries the product norm, the maximum of the chartwise component norms.

Being the components of a section is equivalent to the chart data satisfying the cocycle relation
on every overlap (`TauCeti.SectionChartData.mem_sobolevSections_iff_forall_compatible`). In one
direction a section is glued from the chart data; in the other the relation is read off from the
section, which needs that chart transitions carry null sets to null sets
(`TauCeti.SectionChartData.AETransition`). Each relation is closed in the product of Sobolev
spaces, because convergence in `Lᵖ` gives almost everywhere convergence along a subsequence, so
the submodule is closed (`TauCeti.SectionChartData.isClosed_sobolevSections`) and complete.

A finite bundle atlas `A : TauCeti.FiniteBundleAtlas E M F V` gives chart data
`A.sectionChartData` on the chart images `A.image i`, whose chart transitions, being `C¹`
diffeomorphisms between open sets, carry null sets to null sets
(`TauCeti.SectionChartData.aeTransition_of_differentiableOn`). The space `W^{k,p}(V)` is
`TauCeti.SobolevSection A μ p k`; the analogue for bases with boundary is built from the same
construction in `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered.Basic`.

## Main definitions

* `TauCeti.SectionChartData`: chart data reading sections as functions on open subsets of `E`.
* `TauCeti.SectionChartData.SobolevData.mapL`: a continuous linear map on each chart applied to
  every component of a tuple in that chart.
* `TauCeti.SectionChartData.chartValueL`: the `F`-valued `Lᵖ` function on `C.image i` assembled
  from the chart-`i` Sobolev components of a tuple.
* `TauCeti.SectionChartData.sobolevSections`: the tuples of chartwise Sobolev components of
  sections.
* `TauCeti.SectionChartData.lowerOrderL`: the continuous inclusion of order `k + 1` into order `k`.
* `TauCeti.SectionChartData.constMapL`: a fibrewise map of sections read in every chart as a
  constant linear map `L` of the model fibre, applied to the Sobolev sections by the matrix of `L`
  (`TauCeti.SectionChartData.chartValueL_constMapL_ae`), which lifts the fibre map on the readings
  of sections (`TauCeti.SectionChartData.chartValueL_constMapL_ae_coord`).
* `TauCeti.SectionChartData.ofComponents`: the linear map into the Sobolev sections from a space of
  sections with chartwise Sobolev components.
* `TauCeti.SectionChartData.fiberMap`, `TauCeti.SectionChartData.fiberMapData`: a constant linear
  map between model fibres acting on the components of a tuple of scalar Sobolev functions,
  followed by restriction to smaller open subsets.
* `TauCeti.FiniteBundleAtlas.sectionChartData`: the chart data of a finite bundle atlas.
* `TauCeti.SobolevSection A μ p k`: the Banach space `W^{k,p}(V)`.

## Main results

* `TauCeti.SectionChartData.mem_sobolevSections_iff_forall_compatible`: a tuple consists of the
  components of a section exactly when its chart data satisfy the cocycle relations.
* `TauCeti.SectionChartData.aeTransition_of_differentiableOn`: differentiable chart transitions
  preserve null sets.
* `TauCeti.SectionChartData.isClosed_sobolevSections`,
  `TauCeti.SobolevSection.instCompleteSpace`: completeness.
* `TauCeti.SectionChartData.norm_le_sum_of_norm_le`: the norm is at most the sum of the component
  norms.
* `TauCeti.SectionChartData.eq_of_ae_eq_coord`: an element of the Sobolev sections is determined by
  the section whose readings its chart data are.
* `TauCeti.SectionChartData.chartValueL_ae_of_eq_fiberMap`: components related by a constant fibre
  map `L` have chart data related by `L`.
* `TauCeti.SobolevSection.eq_of_ae_eq_coord`: an element of `W^{k,p}(V)` is determined by the
  section whose coordinates its chart data are.
* `TauCeti.FiniteBundleAtlas.isFiniteMeasure_restrict_image`: chart images have finite measure for
  a measure that is finite on compact sets.
* `TauCeti.SectionChartData.chartValueL_ae_eq_smul`: multiplying the chart-`i` components of a
  tuple by a scalar function multiplies its chart data by that function.

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

/-- Chart data for sections: finitely many open sets `image i` of `E` on which the elements `s` of
a real vector space `S` of sections are read as `F`-valued functions `coord i s`, linearly at each
point of `image i`. On the overlap `overlap i i' ⊆ image i'` of charts `i` and `i'`, read in chart
`i'`, the two readings are related through the chart transition `transition i i'` and the linear
coordinate change `coordChange i i'`. Every family of functions, one per chart, glues to a section
that agrees at each point of `image i'` with the coordinate change of one of them. Off the
overlaps the chart transitions are the identity and the coordinate changes are `1`, and the
readings in chart `i` vanish off the points at which the laws read them: `image i` and the images
of the overlaps `overlap i i'` under the chart transitions `transition i i'`. So chart data are
determined by their sets and their values at these points (`TauCeti.SectionChartData.ext`).
Finite bundle atlases over manifolds with and without boundary give such data. -/
structure SectionChartData (E : Type*) [TopologicalSpace E] (F : Type*) [NormedAddCommGroup F]
    [NormedSpace ℝ F] (S : Type*) [AddCommGroup S] [Module ℝ S] where
  /-- The number of charts. -/
  n : ℕ
  /-- The open set on which sections are read in chart `i`. -/
  image : Fin n → Opens E
  /-- The overlap of charts `i` and `i'`, read in chart `i'`. -/
  overlap : Fin n → Fin n → Set E
  isOpen_overlap : ∀ i i', IsOpen (overlap i i')
  overlap_subset_image : ∀ i i', overlap i i' ⊆ image i'
  /-- The chart transition from chart `i'` to chart `i`. -/
  transition : Fin n → Fin n → E → E
  /-- The coordinate change from chart `i` to chart `i'`, at a point of chart `i'`. -/
  coordChange : Fin n → Fin n → E → F →L[ℝ] F
  /-- A section read in chart `i`. -/
  coord : Fin n → S → E → F
  transition_of_notMem : ∀ i i', ∀ y ∉ overlap i i', transition i i' y = y
  coordChange_of_notMem : ∀ i i', ∀ y ∉ overlap i i', coordChange i i' y = 1
  coord_of_notMem : ∀ i s, ∀ y ∉ (image i : Set E) ∪ ⋃ i', transition i i' '' overlap i i',
    coord i s y = 0
  coord_add : ∀ i s t, ∀ y ∈ image i, coord i (s + t) y = coord i s y + coord i t y
  coord_smul : ∀ i (c : ℝ) s, ∀ y ∈ image i, coord i (c • s) y = c • coord i s y
  coord_eq_coordChange : ∀ i i' s, ∀ y ∈ overlap i i',
    coord i' s y = coordChange i i' y (coord i s (transition i i' y))
  exists_glue : ∀ f : Fin n → E → F, ∃ s, ∀ i', ∀ y ∈ image i', ∃ i, y ∈ overlap i i' ∧
    coord i' s y = coordChange i i' y (f i (transition i i' y))

namespace SectionChartData

section Coordinates

variable {E : Type*} [TopologicalSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S] (C : SectionChartData E F S)

/-- **Extensionality.** Chart data are equal when they have the same sets, the same chart
transitions and coordinate changes on the overlaps, and the same readings in chart `i` on the
image of chart `i` and on the images of the overlaps under the chart transitions to chart `i`. -/
@[ext (iff := false)]
theorem ext {C C' : SectionChartData E F S} (hn : C.n = C'.n)
    (himage : ∀ i, C.image i = C'.image (Fin.cast hn i))
    (hoverlap : ∀ i i', C.overlap i i' = C'.overlap (Fin.cast hn i) (Fin.cast hn i'))
    (htransition : ∀ i i', ∀ y ∈ C.overlap i i',
      C.transition i i' y = C'.transition (Fin.cast hn i) (Fin.cast hn i') y)
    (hcoordChange : ∀ i i', ∀ y ∈ C.overlap i i',
      C.coordChange i i' y = C'.coordChange (Fin.cast hn i) (Fin.cast hn i') y)
    (hcoord : ∀ i s, ∀ y ∈ (C.image i : Set E) ∪ ⋃ i', C.transition i i' '' C.overlap i i',
      C.coord i s y = C'.coord (Fin.cast hn i) s y) :
    C = C' := by
  cases C with
  | mk n image overlap _ _ transition coordChange coord htr hcc hco _ _ _ _ =>
  cases C' with
  | mk n' image' overlap' _ _ transition' coordChange' coord' htr' hcc' hco' _ _ _ _ =>
  obtain rfl : n = n' := hn
  simp only [Fin.cast_eq_self] at himage hoverlap htransition hcoordChange hcoord
  obtain rfl : image = image' := funext himage
  obtain rfl : overlap = overlap' := funext fun i ↦ funext (hoverlap i)
  obtain rfl : transition = transition' := by
    funext i i' y
    by_cases hy : y ∈ overlap i i'
    exacts [htransition i i' y hy, (htr i i' y hy).trans (htr' i i' y hy).symm]
  obtain rfl : coordChange = coordChange' := by
    funext i i' y
    by_cases hy : y ∈ overlap i i'
    exacts [hcoordChange i i' y hy, (hcc i i' y hy).trans (hcc' i i' y hy).symm]
  obtain rfl : coord = coord' := by
    funext i s y
    by_cases hy : y ∈ (image i : Set E) ∪ ⋃ i', transition i i' '' overlap i i'
    exacts [hcoord i s y hy, (hco i s y hy).trans (hco' i s y hy).symm]
  rfl

theorem coord_zero (i : Fin C.n) {y : E} (hy : y ∈ C.image i) : C.coord i 0 y = 0 := by
  simpa using C.coord_smul i 0 0 y hy

/-- Chart transitions carry null sets to null sets: a property holding almost everywhere on the
image of chart `i` holds, after composition with the chart transition, almost everywhere on the
overlap of charts `i` and `i'`. -/
def AETransition [MeasurableSpace E] (μ : Measure E) : Prop :=
  ∀ ⦃i i' : Fin C.n⦄ ⦃P : E → Prop⦄, (∀ᵐ y ∂μ.restrict (C.image i), P y) →
    ∀ᵐ y ∂μ.restrict (C.overlap i i'), P (C.transition i i' y)

theorem aeTransition_iff [MeasurableSpace E] {μ : Measure E} :
    C.AETransition μ ↔ ∀ ⦃i i' : Fin C.n⦄ ⦃P : E → Prop⦄,
      (∀ᵐ y ∂μ.restrict (C.image i), P y) →
        ∀ᵐ y ∂μ.restrict (C.overlap i i'), P (C.transition i i' y) :=
  Iff.rfl

end Coordinates

section Transition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S] (C : SectionChartData E F S)

/-- **Chart transitions preserve null sets.** Chart transitions that are differentiable on the
overlaps and inverse to each other carry null sets of an additive Haar measure to null sets. -/
theorem aeTransition_of_differentiableOn {μ : Measure E} [μ.IsAddHaarMeasure]
    (hd : ∀ i i', DifferentiableOn ℝ (C.transition i i') (C.overlap i i'))
    (hmaps : ∀ i i', MapsTo (C.transition i i') (C.overlap i i') (C.overlap i' i))
    (hinv : ∀ i i', ∀ y ∈ C.overlap i i', C.transition i' i (C.transition i i' y) = y) :
    C.AETransition μ := by
  refine C.aeTransition_iff.2 fun i i' P h ↦ ?_
  have hN : μ ({z | ¬P z} ∩ C.overlap i' i) = 0 := by
    rw [ae_iff, Measure.restrict_apply' (C.image i).isOpen.measurableSet] at h
    exact measure_mono_null (inter_subset_inter_right _ (C.overlap_subset_image i' i)) h
  have himage := addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ
    ((hd i' i).mono inter_subset_right) hN
  rw [ae_iff, Measure.restrict_apply' (C.isOpen_overlap i i').measurableSet]
  refine measure_mono_null (fun y hy ↦ ?_) himage
  exact ⟨C.transition i i' y, ⟨hy.1, hmaps i i' hy.2⟩, hinv i i' y hy.2⟩

end Transition

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {S : Type*} [AddCommGroup S] [Module ℝ S]

variable (C : SectionChartData E F S) (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞)
  [Fact (1 ≤ p)] (k : ℕ)

/-- Tuples of scalar Sobolev functions of order `k`, one on the image of each chart for each vector
of the standard basis `Module.finBasis ℝ F` of the model fibre. -/
abbrev SobolevData : Type u :=
  ∀ (i : Fin C.n) (_ : Fin (finrank ℝ F)), Wkp μ (C.image i) p k

namespace SobolevData

variable {C μ p k} {p' : ℝ≥0∞} [Fact (1 ≤ p')] {k' : ℕ}

/-- Applies a continuous linear map between scalar Sobolev spaces of the image of chart `i` to
every chart-`i` component of a tuple. -/
def mapL (T : ∀ i : Fin C.n, Wkp μ (C.image i) p k →L[ℝ] Wkp μ (C.image i) p' k') :
    C.SobolevData μ p k →L[ℝ] C.SobolevData μ p' k' :=
  ContinuousLinearMap.piMap fun i ↦ ContinuousLinearMap.piMap fun _ ↦ T i

omit [FiniteDimensional ℝ F] in
@[simp]
theorem mapL_apply (T : ∀ i : Fin C.n, Wkp μ (C.image i) p k →L[ℝ] Wkp μ (C.image i) p' k')
    (w : C.SobolevData μ p k) (i : Fin C.n) (j : Fin (finrank ℝ F)) :
    mapL T w i j = T i (w i j) := by
  rfl

end SobolevData

/-- The `F`-valued `Lᵖ` function on the image of chart `i` whose components in the basis
`Module.finBasis ℝ F` are the values of the chart-`i` entries of a tuple of Sobolev functions. -/
def chartValueL (i : Fin C.n) : C.SobolevData μ p k →L[ℝ] Lp F p (μ.restrict (C.image i)) :=
  ∑ j, ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j)).compLpL p _).comp
    ((Wkp.valueL k).comp ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (finrank ℝ F) ↦ Wkp μ (C.image i) p k) j).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun i : Fin C.n ↦ ∀ _ : Fin (finrank ℝ F), Wkp μ (C.image i) p k) i)))

/-- Almost everywhere on the image of chart `i`, the chart data of a tuple are the combination of
the basis vectors of `F` with the values of its chart-`i` components. -/
theorem chartValueL_apply_ae (i : Fin C.n) (w : C.SobolevData μ p k) :
    ∀ᵐ y ∂μ.restrict (C.image i),
      C.chartValueL μ p k i w y = ∑ j, Wkp.value k (w i j) y • finBasis ℝ F j := by
  have heq : C.chartValueL μ p k i w = ∑ j,
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j)).compLpL p _
        (Wkp.value k (w i j)) := by
    simp [chartValueL]
  have hsum := Lp.coeFn_finsetSum (μ := μ.restrict (C.image i)) (p := p) Finset.univ fun j ↦
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j)).compLpL p _
      (Wkp.value k (w i j))
  have hj (j : Fin (finrank ℝ F)) := ContinuousLinearMap.coeFn_compLpL (p := p)
    (μ := μ.restrict (C.image i)) (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (finBasis ℝ F j))
    (Wkp.value k (w i j))
  filter_upwards [hsum, ae_all_iff.2 hj] with y hy hy'
  rw [heq, hy, Finset.sum_apply]
  exact Finset.sum_congr rfl fun j _ ↦ by simp [hy' j]

/-- A tuple whose chart-`i` components are, almost everywhere, the components of the reading of a
section `s` in chart `i` has chart data equal to that reading almost everywhere. -/
theorem chartValueL_ae_eq_coord {w : C.SobolevData μ p k} {s : S} {i : Fin C.n}
    (h : ∀ j, (Wkp.value k (w i j) : E → ℝ) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ (finBasis ℝ F).coord j (C.coord i s y)) :
    C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s := by
  filter_upwards [C.chartValueL_apply_ae μ p k i w, ae_all_iff.2 h] with y hy hj
  rw [hy]
  simp_rw [hj, Basis.coord_apply]
  exact (finBasis ℝ F).sum_repr _

/-- The chart data in chart `i` of a tuple equal the reading of a section `s` almost everywhere
exactly when its chart-`i` components are, almost everywhere, the components of that reading. -/
theorem chartValueL_ae_eq_coord_iff {w : C.SobolevData μ p k} {s : S} {i : Fin C.n} :
    C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s ↔
      ∀ j, (Wkp.value k (w i j) : E → ℝ) =ᵐ[μ.restrict (C.image i)]
        fun y ↦ (finBasis ℝ F).coord j (C.coord i s y) := by
  refine ⟨fun h j ↦ ?_, C.chartValueL_ae_eq_coord μ p k⟩
  filter_upwards [C.chartValueL_apply_ae μ p k i w, h] with y hy hy'
  rw [← hy', hy, Basis.coord_apply, (finBasis ℝ F).repr_sum_self]

/-- If the chart-`i` components of `w'` are those of `w` multiplied by a function `ψ` on the image
of chart `i`, almost everywhere, then so are the chart data in chart `i`. -/
theorem chartValueL_ae_eq_smul {w w' : C.SobolevData μ p k} {i : Fin C.n} {ψ : E → ℝ}
    (h : ∀ j, (Wkp.value k (w' i j) : E → ℝ) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ y * Wkp.value k (w i j) y) :
    C.chartValueL μ p k i w' =ᵐ[μ.restrict (C.image i)]
      fun y ↦ ψ y • C.chartValueL μ p k i w y := by
  filter_upwards [C.chartValueL_apply_ae μ p k i w', C.chartValueL_apply_ae μ p k i w,
    ae_all_iff.2 h] with y hy' hy hj
  rw [hy', hy, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ by rw [hj j, mul_smul]

variable {C μ p k} in
/-- The components of the chart data of a tuple of Sobolev functions are the values of its
entries: if the chart data in chart `i` agree with the reading of a section `s`, then the `j`th
component of that reading in the basis `Module.finBasis ℝ F` is the value of the entry `w i j`,
almost everywhere on `C.image i`. -/
theorem value_ae_eq_repr_coord {w : C.SobolevData μ p k} {s : S} {i : Fin C.n}
    (hs : C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s)
    (j : Fin (finrank ℝ F)) :
    (Wkp.value k (w i j) : E → ℝ) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ (finBasis ℝ F).repr (C.coord i s y) j := by
  simpa only [Basis.coord_apply] using (C.chartValueL_ae_eq_coord_iff μ p k).1 hs j

/-- Forgetting the highest derivative of every component does not change the chart data. -/
theorem chartValueL_lowerOrderL (i : Fin C.n) (w : C.SobolevData μ p (k + 1)) :
    C.chartValueL μ p k i (fun i j ↦ Wkp.lowerOrderL k (w i j)) =
      C.chartValueL μ p (k + 1) i w := by
  simp only [chartValueL, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, ContinuousLinearMap.proj_apply]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [Wkp.valueL_apply, Wkp.valueL_apply, Wkp.value_succ, Wkp.lowerOrderL_apply]

/-- The chart-`i'` data of a tuple are related to its chart-`i` data by the coordinate change on
the overlap of the two charts, almost everywhere. -/
def Compatible (w : C.SobolevData μ p k) (i i' : Fin C.n) : Prop :=
  ∀ᵐ y ∂μ.restrict (C.overlap i i'), C.chartValueL μ p k i' w y =
    C.coordChange i i' y (C.chartValueL μ p k i w (C.transition i i' y))

theorem compatible_iff {w : C.SobolevData μ p k} {i i' : Fin C.n} :
    C.Compatible μ p k w i i' ↔ ∀ᵐ y ∂μ.restrict (C.overlap i i'), C.chartValueL μ p k i' w y =
      C.coordChange i i' y (C.chartValueL μ p k i w (C.transition i i' y)) :=
  Iff.rfl

/-- The tuples of chartwise Sobolev components of sections: a tuple `w` belongs to it when some
section `s` has, in every chart `i`, reading equal almost everywhere on `C.image i` to the function
assembled from the chart-`i` components of `w`. -/
def sobolevSections : Submodule ℝ (C.SobolevData μ p k) where
  carrier := {w | ∃ s : S, ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s}
  add_mem' {w w'} := by
    rintro ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s + t, fun i ↦ ?_⟩
    filter_upwards [hs i, ht i, ae_restrict_mem (C.image i).isOpen.measurableSet,
      Lp.coeFn_add (C.chartValueL μ p k i w) (C.chartValueL μ p k i w')] with y hy ht hyU hadd
    rw [map_add, hadd, Pi.add_apply, hy, ht, C.coord_add i s t y hyU]
  zero_mem' := ⟨0, fun i ↦ by
    filter_upwards [ae_restrict_mem (C.image i).isOpen.measurableSet,
      Lp.coeFn_zero F p (μ.restrict (C.image i))] with y hyU h0
    rw [map_zero, h0, Pi.zero_apply, C.coord_zero i hyU]⟩
  smul_mem' c w := by
    rintro ⟨s, hs⟩
    refine ⟨c • s, fun i ↦ ?_⟩
    filter_upwards [hs i, ae_restrict_mem (C.image i).isOpen.measurableSet,
      Lp.coeFn_smul c (C.chartValueL μ p k i w)] with y hy hyU hsmul
    rw [map_smul, hsmul, Pi.smul_apply, hy, C.coord_smul i c s y hyU]

theorem mem_sobolevSections_iff {w : C.SobolevData μ p k} :
    w ∈ C.sobolevSections μ p k ↔
      ∃ s : S, ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s :=
  Iff.rfl

variable {C μ p k}

/-- The components of a section satisfy the cocycle relation on every overlap. -/
theorem compatible_of_mem (hC : C.AETransition μ) {w : C.SobolevData μ p k}
    (hw : w ∈ C.sobolevSections μ p k) (i i' : Fin C.n) : C.Compatible μ p k w i i' := by
  obtain ⟨s, hs⟩ := hw
  filter_upwards [ae_restrict_of_ae_restrict_of_subset (C.overlap_subset_image i i') (hs i'),
    C.aeTransition_iff.1 hC (i' := i') (hs i),
    ae_restrict_mem (C.isOpen_overlap i i').measurableSet] with y h' h hy
  rw [h', h, C.coord_eq_coordChange i i' s y hy]

/-- **Gluing.** Chart data satisfying the cocycle relation on every overlap are the components of
a section. -/
theorem mem_sobolevSections_of_forall_compatible {w : C.SobolevData μ p k}
    (hw : ∀ i i', C.Compatible μ p k w i i') : w ∈ C.sobolevSections μ p k := by
  obtain ⟨s, hs⟩ := C.exists_glue fun i ↦ C.chartValueL μ p k i w
  refine ⟨s, fun i' ↦ ?_⟩
  have hall : ∀ᵐ y ∂μ.restrict (C.image i'), ∀ i, y ∈ C.overlap i i' →
      C.chartValueL μ p k i' w y =
        C.coordChange i i' y (C.chartValueL μ p k i w (C.transition i i' y)) := by
    rw [ae_all_iff]
    intro i
    exact ae_restrict_of_ae ((ae_restrict_iff' (C.isOpen_overlap i i').measurableSet).1 (hw i i'))
  filter_upwards [hall, ae_restrict_mem (C.image i').isOpen.measurableSet] with y hy hyU
  obtain ⟨i, hov, hs⟩ := hs i' y hyU
  rw [hy i hov, hs]

/-- A tuple consists of the chartwise Sobolev components of a section exactly when its chart data
satisfy the cocycle relation on every overlap. -/
theorem mem_sobolevSections_iff_forall_compatible (hC : C.AETransition μ)
    {w : C.SobolevData μ p k} : w ∈ C.sobolevSections μ p k ↔ ∀ i i', C.Compatible μ p k w i i' :=
  ⟨compatible_of_mem hC, mem_sobolevSections_of_forall_compatible⟩

/-- Each cocycle relation is a closed condition on tuples of Sobolev functions: convergence in
`Lᵖ` gives almost everywhere convergence along a subsequence. -/
theorem isClosed_setOf_compatible (hC : C.AETransition μ) (i i' : Fin C.n) :
    IsClosed {w : C.SobolevData μ p k | C.Compatible μ p k w i i'} := by
  refine IsSeqClosed.isClosed fun {w w₀} hw hlim ↦ ?_
  have hc (j : Fin C.n) : Tendsto (fun m ↦ C.chartValueL μ p k j (w m)) atTop
      (𝓝 (C.chartValueL μ p k j w₀)) :=
    ((C.chartValueL μ p k j).continuous.tendsto w₀).comp hlim
  -- Almost everywhere convergence of the chart-`i'` data along a subsequence, then of the
  -- chart-`i` data along a further subsequence.
  obtain ⟨ns, hns, hae'⟩ := (tendstoInMeasure_of_tendsto_Lp (hc i')).exists_seq_tendsto_ae
  obtain ⟨ms, hms, hae⟩ := (tendstoInMeasure_of_tendsto_Lp
    ((hc i).comp hns.tendsto_atTop)).exists_seq_tendsto_ae
  have hrel : ∀ᵐ y ∂μ.restrict (C.overlap i i'), ∀ m, C.chartValueL μ p k i' (w m) y =
      C.coordChange i i' y (C.chartValueL μ p k i (w m) (C.transition i i' y)) :=
    ae_all_iff.2 fun m ↦ by simpa only [mem_ofPred_eq, compatible_iff] using hw m
  simp only [mem_ofPred_eq, compatible_iff]
  filter_upwards [hrel, ae_restrict_of_ae_restrict_of_subset (C.overlap_subset_image i i') hae',
    C.aeTransition_iff.1 hC (i' := i') hae] with y hy h' h
  refine tendsto_nhds_unique (h'.comp hms.tendsto_atTop) ?_
  refine (((C.coordChange i i' y).continuous.tendsto _).comp h).congr fun m ↦ ?_
  exact (hy (ns (ms m))).symm

/-- The chartwise Sobolev components of sections form a closed subspace of the product of scalar
Sobolev spaces. -/
theorem isClosed_sobolevSections (hC : C.AETransition μ) :
    IsClosed (C.sobolevSections μ p k : Set (C.SobolevData μ p k)) := by
  have : (C.sobolevSections μ p k : Set (C.SobolevData μ p k)) =
      ⋂ i, ⋂ i', {w | C.Compatible μ p k w i i'} := by
    ext w
    simp only [SetLike.mem_coe, mem_sobolevSections_iff_forall_compatible hC, mem_iInter,
      mem_ofPred_eq]
  rw [this]
  exact isClosed_iInter fun i ↦ isClosed_iInter fun i' ↦ isClosed_setOf_compatible hC i i'

/-- **Completeness.** The chartwise Sobolev components of sections form a Banach space. -/
theorem completeSpace_sobolevSections (hC : C.AETransition μ) :
    CompleteSpace (C.sobolevSections μ p k) :=
  (isClosed_sobolevSections hC).completeSpace_coe

variable (C μ p k)

/-- An element of the Sobolev sections consists of the chartwise components of a section. -/
theorem exists_section (w : C.sobolevSections μ p k) :
    ∃ s : S, ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s :=
  w.2

/-- Two elements of the Sobolev sections are equal when their components have equal values. -/
theorem sobolevSections_ext {w w' : C.sobolevSections μ p k}
    (h : ∀ i j, Wkp.value k ((w : C.SobolevData μ p k) i j) =
      Wkp.value k ((w' : C.SobolevData μ p k) i j)) : w = w' :=
  Subtype.ext <| funext fun i ↦ funext fun j ↦ Wkp.ext k (h i j)

variable {C μ p k} in
/-- **Uniqueness.** Two elements of the Sobolev sections whose chart data are the readings of the
same section are equal. -/
theorem eq_of_ae_eq_coord {w w' : C.sobolevSections μ p k} {s : S}
    (hw : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s)
    (hw' : ∀ i, C.chartValueL μ p k i w' =ᵐ[μ.restrict (C.image i)] C.coord i s) :
    w = w' :=
  C.sobolevSections_ext μ p k fun i j ↦ Lp.ext <|
    (value_ae_eq_repr_coord (hw i) j).trans (value_ae_eq_repr_coord (hw' i) j).symm

variable {C μ p k} in
/-- Two elements of the Sobolev sections with almost everywhere equal chart data are equal. -/
theorem eq_of_chartValueL_ae_eq {w w' : C.sobolevSections μ p k}
    (h : ∀ i, C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.chartValueL μ p k i w') :
    w = w' := by
  obtain ⟨s, hs⟩ := C.exists_section μ p k w'
  exact eq_of_ae_eq_coord (fun i ↦ (h i).trans (hs i)) hs

/-- The norm of an element of the Sobolev sections, the maximum of its component norms, is at most
any sum of bounds for the component norms. -/
theorem norm_le_sum_of_norm_le {w : C.sobolevSections μ p k}
    {b : Fin C.n → Fin (finrank ℝ F) → ℝ} (h : ∀ i j, ‖(w : C.SobolevData μ p k) i j‖ ≤ b i j) :
    ‖w‖ ≤ ∑ i, ∑ j, b i j := by
  have hb (i : Fin C.n) (j : Fin (finrank ℝ F)) : 0 ≤ b i j := (norm_nonneg _).trans (h i j)
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ ↦
    Finset.sum_nonneg fun j _ ↦ hb i j)).2 fun i ↦ ?_
  refine ((pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun j _ ↦ hb i j)).2 fun j ↦
    (h i j).trans (Finset.single_le_sum (fun j _ ↦ hb i j) (Finset.mem_univ j))).trans
      (Finset.single_le_sum (f := fun i ↦ ∑ j, b i j)
        (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hb i j) (Finset.mem_univ i))

/-- The continuous inclusion of the Sobolev sections of order `k + 1` into those of order `k`,
forgetting the highest derivative of every component. -/
def lowerOrderL : C.sobolevSections μ p (k + 1) →L[ℝ] C.sobolevSections μ p k :=
  ((SobolevData.mapL fun _ ↦ Wkp.lowerOrderL k).comp
    (C.sobolevSections μ p (k + 1)).subtypeL).codRestrict (C.sobolevSections μ p k) fun w ↦ by
      obtain ⟨s, hs⟩ := w.2
      refine ⟨s, fun i ↦ ?_⟩
      convert hs i using 2
      rw [← C.chartValueL_lowerOrderL μ p k i w]
      rfl

@[simp]
theorem lowerOrderL_apply (w : C.sobolevSections μ p (k + 1)) (i : Fin C.n)
    (j : Fin (finrank ℝ F)) :
    (C.lowerOrderL μ p k w : C.SobolevData μ p k) i j =
      Wkp.lowerOrder k ((w : C.SobolevData μ p (k + 1)) i j) := by
  rw [← Wkp.lowerOrderL_apply]
  rfl

/-- Forgetting the highest derivative does not change the chart data. -/
@[simp]
theorem chartValueL_coe_lowerOrderL (w : C.sobolevSections μ p (k + 1)) (i : Fin C.n) :
    C.chartValueL μ p k i (C.lowerOrderL μ p k w) = C.chartValueL μ p (k + 1) i w := by
  rw [← C.chartValueL_lowerOrderL μ p k i w]
  refine congrArg (C.chartValueL μ p k i) (funext fun i' ↦ funext fun j ↦ ?_)
  rw [lowerOrderL_apply, Wkp.lowerOrderL_apply]

section ConstMap

/-- Applies the constant matrix of a linear map `L` of the model fibre, in the basis
`Module.finBasis ℝ F`, to the components of a tuple in every chart. -/
def constMapData (L : F →L[ℝ] F) : C.SobolevData μ p k →L[ℝ] C.SobolevData μ p k :=
  ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun j ↦
    ∑ j', (finBasis ℝ F).repr (L (finBasis ℝ F j')) j •
      ((ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin (finrank ℝ F) ↦ Wkp μ (C.image i) p k) j').comp
        (ContinuousLinearMap.proj (R := ℝ)
          (φ := fun i : Fin C.n ↦ ∀ _ : Fin (finrank ℝ F), Wkp μ (C.image i) p k) i))

/-- The components of `constMapData L w` in chart `i` are those of `w` combined by the matrix of
`L`. -/
@[simp]
theorem constMapData_apply (L : F →L[ℝ] F) (w : C.SobolevData μ p k) (i : Fin C.n)
    (j : Fin (finrank ℝ F)) :
    constMapData C μ p k L w i j = ∑ j', (finBasis ℝ F).repr (L (finBasis ℝ F j')) j • w i j' := by
  simp [constMapData]

/-- The chart data of `constMapData L w` are those of `w` composed with `L`. -/
theorem chartValueL_constMapData_ae (L : F →L[ℝ] F) (w : C.SobolevData μ p k)
    (i : Fin C.n) :
    C.chartValueL μ p k i (constMapData C μ p k L w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ L (C.chartValueL μ p k i w y) := by
  have hval (j : Fin (finrank ℝ F)) :
      (Wkp.value k (constMapData C μ p k L w i j) : E → ℝ) =ᵐ[μ.restrict (C.image i)]
        fun y ↦ ∑ j', (finBasis ℝ F).repr (L (finBasis ℝ F j')) j * Wkp.value k (w i j') y := by
    have hsmul (c : ℝ) (u : Wkp μ (C.image i) p k) :
        (Wkp.value k (c • u) : E → ℝ) =ᵐ[μ.restrict (C.image i)] c • (Wkp.value k u : E → ℝ) := by
      rw [Wkp.value_smul]
      exact Lp.coeFn_smul c (Wkp.value k u)
    rw [constMapData_apply]
    filter_upwards [Wkp.value_finsetSum_ae k Finset.univ
      (fun j' ↦ (finBasis ℝ F).repr (L (finBasis ℝ F j')) j • w i j'),
      ae_all_iff.2 fun j' ↦ hsmul ((finBasis ℝ F).repr (L (finBasis ℝ F j')) j) (w i j')]
      with y hy hs
    rw [hy]
    exact Finset.sum_congr rfl fun j' _ ↦ by rw [hs j', Pi.smul_apply, smul_eq_mul]
  filter_upwards [C.chartValueL_apply_ae μ p k i (constMapData C μ p k L w),
    C.chartValueL_apply_ae μ p k i w, ae_all_iff.2 hval] with y h₁ h₂ h₃
  rw [h₁, h₂, map_sum]
  simp_rw [h₃, map_smul, Finset.sum_smul, mul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ ↦ ?_
  conv_rhs => rw [← (finBasis ℝ F).sum_repr (L (finBasis ℝ F j')), Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ smul_comm _ _ _

variable {C μ p k} in
/-- If the chart data of `w` in chart `i` are the readings of a section `s`, and the reading of a
section `s'` in chart `i` is that of `s` followed by the linear map `L` of the model fibre, then the
chart data of `constMapData L w` in chart `i` are the readings of `s'`. -/
theorem chartValueL_constMapData_ae_coord {L : F →L[ℝ] F} {w : C.SobolevData μ p k}
    {i : Fin C.n} {s s' : S} (hs' : ∀ y ∈ C.image i, C.coord i s' y = L (C.coord i s y))
    (hw : C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) :
    C.chartValueL μ p k i (constMapData C μ p k L w) =ᵐ[μ.restrict (C.image i)]
      C.coord i s' := by
  filter_upwards [chartValueL_constMapData_ae C μ p k L w i, hw,
    ae_restrict_mem (C.image i).isOpen.measurableSet] with y h hsy hy
  rw [h, hsy, hs' y hy]

variable {C} in
/-- A fibrewise map `Ψ` of sections whose chart readings are a constant linear map `L` of the model
fibre, applied to the Sobolev sections: the components in every chart are transformed by the
matrix of `L`. -/
def constMapL (L : F →L[ℝ] F) (Ψ : S → S)
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = L (C.coord i s y)) :
    C.sobolevSections μ p k →L[ℝ] C.sobolevSections μ p k :=
  ((constMapData C μ p k L).comp (C.sobolevSections μ p k).subtypeL).codRestrict _ fun w ↦ by
    obtain ⟨s, hs⟩ := (C.mem_sobolevSections_iff μ p k).1 w.2
    exact (C.mem_sobolevSections_iff μ p k).2
      ⟨Ψ s, fun i ↦ chartValueL_constMapData_ae_coord (hΨ i s) (hs i)⟩

variable {C} in
/-- The components of `constMapL μ p k L Ψ hΨ w` are those of `constMapData C μ p k L w`. -/
@[simp]
theorem coe_constMapL {L : F →L[ℝ] F} {Ψ : S → S}
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = L (C.coord i s y))
    (w : C.sobolevSections μ p k) :
    (constMapL μ p k L Ψ hΨ w : C.SobolevData μ p k) = constMapData C μ p k L w :=
  (rfl)

variable {C} in
/-- The chart data of `constMapL μ p k L Ψ hΨ w` are those of `w` composed with `L`. -/
theorem chartValueL_constMapL_ae {L : F →L[ℝ] F} {Ψ : S → S}
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = L (C.coord i s y))
    (w : C.sobolevSections μ p k) (i : Fin C.n) :
    C.chartValueL μ p k i (constMapL μ p k L Ψ hΨ w) =ᵐ[μ.restrict (C.image i)]
      fun y ↦ L (C.chartValueL μ p k i w y) :=
  chartValueL_constMapData_ae C μ p k L w i

variable {C μ p k} in
/-- **Lifting the fibre map.** If the chart data of `w` in chart `i` are the readings of a section
`s`, the chart data of `constMapL μ p k L Ψ hΨ w` are the readings of `Ψ s`. -/
theorem chartValueL_constMapL_ae_coord {L : F →L[ℝ] F} {Ψ : S → S}
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = L (C.coord i s y))
    {w : C.sobolevSections μ p k} {i : Fin C.n} {s : S}
    (hw : C.chartValueL μ p k i w =ᵐ[μ.restrict (C.image i)] C.coord i s) :
    C.chartValueL μ p k i (constMapL μ p k L Ψ hΨ w) =ᵐ[μ.restrict (C.image i)]
      C.coord i (Ψ s) :=
  chartValueL_constMapData_ae_coord (hΨ i s) hw

variable {C} in
/-- Forgetting the highest derivative commutes with a constant fibre map. -/
theorem lowerOrderL_constMapL {L : F →L[ℝ] F} {Ψ : S → S}
    (hΨ : ∀ i s, ∀ y ∈ C.image i, C.coord i (Ψ s) y = L (C.coord i s y))
    (w : C.sobolevSections μ p (k + 1)) :
    C.lowerOrderL μ p k (constMapL μ p (k + 1) L Ψ hΨ w) =
      constMapL μ p k L Ψ hΨ (C.lowerOrderL μ p k w) := by
  refine Subtype.ext <| funext fun i ↦ funext fun j ↦ ?_
  simp [← Wkp.lowerOrderL_apply]

end ConstMap

section Components

variable {T : Type*} [AddCommGroup T] [Module ℝ T] (ι : T →ₗ[ℝ] S)
  (h : ∀ t i j, ∃ w : Wkp μ (C.image i) p k, (Wkp.value k w : E → ℝ) =ᵐ[μ.restrict (C.image i)]
    fun y ↦ (finBasis ℝ F).coord j (C.coord i (ι t) y))

/-- **Sections with Sobolev components.** Given a linear map `ι` from a real vector space `T` to the
sections, such that every component of the reading of every `ι t` in every chart is a `W^{k,p}`
function, the linear map sending `t` to the element of the Sobolev sections whose components in
chart `i` are those of `C.coord i (ι t)` in the basis `Module.finBasis ℝ F`. -/
def ofComponents : T →ₗ[ℝ] C.sobolevSections μ p k where
  toFun t := ⟨fun i j ↦ (h t i j).choose,
    ⟨ι t, fun i ↦ C.chartValueL_ae_eq_coord μ p k fun j ↦ (h t i j).choose_spec⟩⟩
  map_add' t t' := C.sobolevSections_ext μ p k fun i j ↦ Lp.ext <| by
    filter_upwards [(h (t + t') i j).choose_spec, (h t i j).choose_spec, (h t' i j).choose_spec,
      Wkp.value_add k (h t i j).choose (h t' i j).choose ▸ Lp.coeFn_add _ _,
      ae_restrict_mem (C.image i).isOpen.measurableSet] with y h₀ h₁ h₂ hadd hy
    simp only [Submodule.coe_add, Pi.add_apply] at hadd ⊢
    rw [h₀, hadd, h₁, h₂, map_add, C.coord_add i _ _ y hy, map_add]
  map_smul' c t := C.sobolevSections_ext μ p k fun i j ↦ Lp.ext <| by
    filter_upwards [(h (c • t) i j).choose_spec, (h t i j).choose_spec,
      Wkp.value_smul k c (h t i j).choose ▸ Lp.coeFn_smul _ _,
      ae_restrict_mem (C.image i).isOpen.measurableSet] with y h₀ h₁ hsmul hy
    simp only [Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply] at hsmul ⊢
    rw [h₀, hsmul, h₁, map_smul, C.coord_smul i c _ y hy, map_smul, smul_eq_mul]

/-- The components in chart `i` of `C.ofComponents μ p k ι h t` are the components of
`C.coord i (ι t)` in the basis `Module.finBasis ℝ F`, almost everywhere on the image of the
chart. -/
theorem value_ofComponents_ae (t : T) (i : Fin C.n) (j : Fin (finrank ℝ F)) :
    (Wkp.value k ((C.ofComponents μ p k ι h t : C.SobolevData μ p k) i j) : E → ℝ)
      =ᵐ[μ.restrict (C.image i)] fun y ↦ (finBasis ℝ F).coord j (C.coord i (ι t) y) :=
  (h t i j).choose_spec

/-- The chart data in chart `i` of `C.ofComponents μ p k ι h t` are the reading `C.coord i (ι t)`,
almost everywhere on the image of the chart. -/
theorem chartValueL_ofComponents_ae (t : T) (i : Fin C.n) :
    C.chartValueL μ p k i (C.ofComponents μ p k ι h t) =ᵐ[μ.restrict (C.image i)]
      C.coord i (ι t) :=
  C.chartValueL_ae_eq_coord μ p k fun j ↦ (h t i j).choose_spec

/-- If `C.ofComponents μ p k ι h t` vanishes, the reading of `ι t` in every chart vanishes almost
everywhere on the image of the chart. -/
theorem coord_ae_eq_zero_of_ofComponents_eq_zero {t : T} (ht : C.ofComponents μ p k ι h t = 0)
    (i : Fin C.n) : C.coord i (ι t) =ᵐ[μ.restrict (C.image i)] 0 := by
  have h0 : C.chartValueL μ p k i (C.ofComponents μ p k ι h t : C.SobolevData μ p k) = 0 := by
    rw [ht, ZeroMemClass.coe_zero, map_zero]
  have hz := Lp.coeFn_zero F p (μ.restrict (C.image i))
  rw [← h0] at hz
  exact (C.chartValueL_ofComponents_ae μ p k ι h t i).symm.trans hz

end Components

section FiberMap

variable {G₁ : Type*} [NormedAddCommGroup G₁] [NormedSpace ℝ G₁] [FiniteDimensional ℝ G₁]
  {G₂ : Type*} [NormedAddCommGroup G₂] [NormedSpace ℝ G₂] [FiniteDimensional ℝ G₂]

/-- The constant fibre map `L : G₁ →L[ℝ] G₂` on the components of a tuple of scalar Sobolev
functions, followed by restriction to an open subset. -/
def fiberMap (L : G₁ →L[ℝ] G₂) {U U' : Opens E} (hU : U' ≤ U) :
    (Fin (finrank ℝ G₁) → Wkp μ U p k) →L[ℝ] (Fin (finrank ℝ G₂) → Wkp μ U' p k) :=
  ContinuousLinearMap.pi fun c ↦ ∑ a, LinearMap.toMatrix (finBasis ℝ G₁) (finBasis ℝ G₂)
    L.toLinearMap c a • (Wkp.restrictL hU k).comp (ContinuousLinearMap.proj a)

/-- Component `c` of the image of `w` under the constant fibre map `L` is the combination of the
restricted components of `w` with the coefficients of row `c` of the matrix of `L` in the bases
`Module.finBasis ℝ G₁` and `Module.finBasis ℝ G₂`. -/
@[simp]
theorem fiberMap_apply (L : G₁ →L[ℝ] G₂) {U U' : Opens E} (hU : U' ≤ U)
    (w : Fin (finrank ℝ G₁) → Wkp μ U p k) (c : Fin (finrank ℝ G₂)) :
    fiberMap μ p k L hU w c = ∑ a, LinearMap.toMatrix (finBasis ℝ G₁) (finBasis ℝ G₂)
      L.toLinearMap c a • Wkp.restrictL hU k (w a) := by
  simp [fiberMap]

/-- Almost everywhere on `U'`, the values of the components of the image of `w` under the constant
fibre map `L` are the matrix of `L` applied to the values of the components of `w`. -/
theorem value_fiberMap_ae (L : G₁ →L[ℝ] G₂) {U U' : Opens E} (hU : U' ≤ U)
    (w : Fin (finrank ℝ G₁) → Wkp μ U p k) :
    ∀ᵐ y ∂μ.restrict U', ∀ c, Wkp.value k (fiberMap μ p k L hU w c) y =
      (LinearMap.toMatrix (finBasis ℝ G₁) (finBasis ℝ G₂) L.toLinearMap).mulVec
        (fun a ↦ Wkp.value k (w a) y) c := by
  refine ae_all_iff.2 fun c ↦ ?_
  have hsmul (a : Fin (finrank ℝ G₁)) :=
    Lp.coeFn_smul (LinearMap.toMatrix (finBasis ℝ G₁) (finBasis ℝ G₂) L.toLinearMap c a)
      (Wkp.value k (Wkp.restrictL hU k (w a)))
  have hres (a : Fin (finrank ℝ G₁)) := Wkp.value_restrictL_ae hU k (w a)
  filter_upwards [Wkp.value_finsetSum_ae k Finset.univ fun a ↦
      LinearMap.toMatrix (finBasis ℝ G₁) (finBasis ℝ G₂) L.toLinearMap c a •
        Wkp.restrictL hU k (w a),
    ae_all_iff.2 hsmul, ae_all_iff.2 hres] with y hy hs hr
  rw [fiberMap_apply, hy, Matrix.mulVec, dotProduct]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [Wkp.value_smul, hs a, Pi.smul_apply, hr a, smul_eq_mul]

/-- The constant fibre map `L` on the components of a tuple, in every chart. -/
def fiberMapData (L : G₁ →L[ℝ] G₂) {n : ℕ} {U U' : Fin n → Opens E}
    (hU : ∀ i, U' i ≤ U i) :
    (∀ (i : Fin n) (_ : Fin (finrank ℝ G₁)), Wkp μ (U i) p k) →L[ℝ]
      (∀ (i : Fin n) (_ : Fin (finrank ℝ G₂)), Wkp μ (U' i) p k) :=
  ContinuousLinearMap.piMap fun i ↦ fiberMap μ p k L (hU i)

/-- In chart `i`, the constant fibre map on tuples acts as `fiberMap` on the chart-`i` components.
-/
@[simp]
theorem fiberMapData_apply (L : G₁ →L[ℝ] G₂) {n : ℕ} {U U' : Fin n → Opens E}
    (hU : ∀ i, U' i ≤ U i) (w : ∀ (i : Fin n) (_ : Fin (finrank ℝ G₁)), Wkp μ (U i) p k)
    (i : Fin n) : fiberMapData μ p k L hU w i = fiberMap μ p k L (hU i) (w i) := by
  simp [fiberMapData]

variable {S₁ : Type*} [AddCommGroup S₁] [Module ℝ S₁] {S₂ : Type*} [AddCommGroup S₂]
  [Module ℝ S₂]

/-- If the chart-`i₂` components of `w₂` are obtained from the chart-`i₁` components of `w₁` by
the constant fibre map `L`, then the chart data of `w₂` are `L` applied to those of `w₁`. -/
theorem chartValueL_ae_of_eq_fiberMap {C₁ : SectionChartData E G₁ S₁}
    {C₂ : SectionChartData E G₂ S₂} (L : G₁ →L[ℝ] G₂) {i₁ : Fin C₁.n} {i₂ : Fin C₂.n}
    (hU : C₂.image i₂ ≤ C₁.image i₁) {w₁ : C₁.SobolevData μ p k} {w₂ : C₂.SobolevData μ p k}
    (hw : w₂ i₂ = fiberMap μ p k L hU (w₁ i₁)) :
    C₂.chartValueL μ p k i₂ w₂ =ᵐ[μ.restrict (C₂.image i₂)]
      fun y ↦ L (C₁.chartValueL μ p k i₁ w₁ y) := by
  filter_upwards [C₂.chartValueL_apply_ae μ p k i₂ w₂,
    ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hU)
      (C₁.chartValueL_apply_ae μ p k i₁ w₁),
    value_fiberMap_ae μ p k L hU (w₁ i₁)] with y h₂ h₁ hv
  rw [h₂, h₁, hw]
  simp_rw [hv]
  have hL := Matrix.toLin_apply (finBasis ℝ G₁) (finBasis ℝ G₂)
    (LinearMap.toMatrix (finBasis ℝ G₁) (finBasis ℝ G₂) L.toLinearMap)
    (∑ a, Wkp.value k (w₁ i₁ a) y • finBasis ℝ G₁ a)
  rw [Matrix.toLin_toMatrix, (finBasis ℝ G₁).repr_sum_self] at hL
  exact hL.symm

end FiberMap

end Sobolev

end SectionChartData

namespace FiniteBundleAtlas

section FiniteMeasure

variable {E : Type*} [TopologicalSpace E] [T2Space E] [MeasurableSpace E] {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] {F : Type*} [TopologicalSpace F] {V : M → Type*}
  [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V]
  (A : FiniteBundleAtlas E M F V) (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

/-- The image of a chart of a finite bundle atlas has finite measure for a measure that is finite on
compact sets, such as a Haar measure, since its closure is compact. -/
instance isFiniteMeasure_restrict_image (i : Fin A.n) :
    IsFiniteMeasure (μ.restrict (A.image i)) :=
  isFiniteMeasure_restrict.2
    ((measure_mono subset_closure).trans_lt (A.isCompact_closure_image i).measure_lt_top).ne

end FiniteMeasure

variable {E : Type*} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V)

open Classical in
/-- The chart data of a finite bundle atlas: a section is read in chart `i` as `A.coord i s` on the
image `A.image i` of the chart, and as `0` off it. At each point the gluing of a family of functions
is read off from the function of any chart containing the point. -/
@[expose] def sectionChartData : SectionChartData E F (∀ x, V x) where
  n := A.n
  image := A.image
  overlap := A.overlap
  isOpen_overlap := A.isOpen_overlap
  overlap_subset_image := A.overlap_subset_image
  transition i i' := (A.overlap i i').piecewise (A.transition i i') id
  coordChange i i' := (A.overlap i i').piecewise
    (fun y ↦ (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)) 1
  coord i s := (A.image i : Set E).indicator (A.coord i s)
  transition_of_notMem _ _ _ hy := piecewise_eq_of_notMem _ _ _ hy
  coordChange_of_notMem _ _ _ hy := piecewise_eq_of_notMem _ _ _ hy
  coord_of_notMem _ _ _ hy := indicator_of_notMem (fun h ↦ hy (Or.inl h)) _
  coord_add i s t _ hy := by
    simp only [indicator_of_mem hy]
    exact A.coord_add i s t hy
  coord_smul i c s _ hy := by
    simp only [indicator_of_mem hy]
    exact A.coord_smul i c s hy
  coord_eq_coordChange i i' s _ hy := by
    rw [piecewise_eq_of_mem _ _ _ hy, piecewise_eq_of_mem _ _ _ hy,
      indicator_of_mem (A.overlap_subset_image i i' hy),
      indicator_of_mem (A.overlap_subset_image i' i (A.transition_mem_overlap hy))]
    exact A.coord_eq_coordChange s hy
  exists_glue f := by
    classical
    let idx : M → Fin A.n := fun x ↦ (A.exists_mem_dom x).choose
    have hidx (x : M) : x ∈ A.dom (idx x) := (A.exists_mem_dom x).choose_spec
    refine ⟨fun x ↦ (A.triv (idx x)).symm x (f (idx x) (A.chart (idx x) x)), fun i' y hy ↦ ?_⟩
    obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hy
    have hov := A.chart_mem_overlap (hidx x) hx
    refine ⟨idx x, hov, ?_⟩
    rw [piecewise_eq_of_mem _ _ _ hov, piecewise_eq_of_mem _ _ _ hov, indicator_of_mem hy,
      A.coord_eq_coordChange _ hov, A.transition_chart hx, A.coord_chart _ (hidx x),
      (A.triv (idx x)).apply_mk_symm (A.dom_subset_baseSet _ (hidx x))]
    rfl

@[simp]
theorem sectionChartData_image (i : Fin A.n) : A.sectionChartData.image i = A.image i :=
  rfl

@[simp]
theorem sectionChartData_overlap (i i' : Fin A.n) :
    A.sectionChartData.overlap i i' = A.overlap i i' :=
  rfl

theorem sectionChartData_transition_of_mem {i i' : Fin A.n} {y : E} (hy : y ∈ A.overlap i i') :
    A.sectionChartData.transition i i' y = A.transition i i' y := by
  classical
  exact piecewise_eq_of_mem _ _ _ hy

theorem sectionChartData_coordChange_of_mem {i i' : Fin A.n} {y : E} (hy : y ∈ A.overlap i i') :
    A.sectionChartData.coordChange i i' y =
      (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) := by
  classical
  simp only [sectionChartData, piecewise_eq_of_mem _ _ _ hy]

theorem sectionChartData_coord_of_mem {i : Fin A.n} (s : ∀ x, V x) {y : E} (hy : y ∈ A.image i) :
    A.sectionChartData.coord i s y = A.coord i s y :=
  indicator_of_mem hy _

/-- Almost everywhere on the image of chart `i`, a section is read in the chart data of the atlas
as `A.coord i s`. -/
theorem sectionChartData_coord_ae_eq [MeasurableSpace E] [OpensMeasurableSpace E] (μ : Measure E)
    (i : Fin A.n) (s : ∀ x, V x) :
    A.sectionChartData.coord i s =ᵐ[μ.restrict (A.image i)] A.coord i s := by
  filter_upwards [ae_restrict_mem (A.image i).isOpen.measurableSet] with y hy
  exact A.sectionChartData_coord_of_mem s hy

section FiniteMeasure

variable [T2Space E] [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

/-- The image of chart `i` in the chart data of a finite bundle atlas has finite measure. -/
instance isFiniteMeasure_restrict_sectionChartData_image (i : Fin A.sectionChartData.n) :
    IsFiniteMeasure (μ.restrict (A.sectionChartData.image i)) :=
  A.isFiniteMeasure_restrict_image μ i

/-- The image of chart `i` in the chart data of a finite bundle atlas has finite measure, for
`i` indexed by the charts of the atlas. Instance search does not identify `Fin A.n` with
`Fin A.sectionChartData.n`, so this is a separate instance. -/
instance isFiniteMeasure_restrict_sectionChartData_image' (i : Fin A.n) :
    IsFiniteMeasure (μ.restrict (A.sectionChartData.image i)) :=
  A.isFiniteMeasure_restrict_image μ i

end FiniteMeasure

end FiniteBundleAtlas

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

variable [MeasurableSpace E] [BorelSpace E]

variable (A : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞)
  [Fact (1 ≤ p)] (k : ℕ)

/-- The chart transitions of a finite bundle atlas, being `C¹` diffeomorphisms between open sets,
carry null sets to null sets. -/
theorem FiniteBundleAtlas.aeTransition_sectionChartData [IsManifold 𝓘(ℝ, E) 1 M] :
    A.sectionChartData.AETransition μ := by
  refine A.sectionChartData.aeTransition_of_differentiableOn
    (fun i i' ↦ (A.differentiableOn_transition i i').congr fun _ hy ↦
      A.sectionChartData_transition_of_mem hy) (fun _ _ _ hy ↦ ?_) fun _ _ _ hy ↦ ?_
  · rw [A.sectionChartData_transition_of_mem hy]
    exact A.transition_mem_overlap hy
  · rw [A.sectionChartData_transition_of_mem hy,
      A.sectionChartData_transition_of_mem (A.transition_mem_overlap hy)]
    exact A.transition_transition hy

variable [FiniteDimensional ℝ F]

/-- The Sobolev space `W^{k,p}(V)` of sections of `V` with respect to the finite bundle atlas `A`:
the tuples of chartwise Sobolev components of sections, with the maximum of the component norms. -/
abbrev SobolevSection : Type u :=
  A.sectionChartData.sobolevSections μ p k

/-- **Completeness.** The Sobolev space of sections of a vector bundle is a Banach space. -/
instance SobolevSection.instCompleteSpace [IsManifold 𝓘(ℝ, E) 1 M] :
    CompleteSpace (SobolevSection A μ p k) :=
  SectionChartData.completeSpace_sobolevSections (A.aeTransition_sectionChartData μ)

variable {A μ p k} in
/-- **Uniqueness.** Two elements of `W^{k,p}(V)` whose chart data are the coordinates `A.coord i s`
of the same section are equal. -/
theorem SobolevSection.eq_of_ae_eq_coord {w w' : SobolevSection A μ p k} {s : ∀ x, V x}
    (hw : ∀ i, A.sectionChartData.chartValueL μ p k i w =ᵐ[μ.restrict (A.image i)] A.coord i s)
    (hw' : ∀ i, A.sectionChartData.chartValueL μ p k i w' =ᵐ[μ.restrict (A.image i)] A.coord i s) :
    w = w' :=
  SectionChartData.eq_of_ae_eq_coord (s := s)
    (fun i ↦ (hw i).trans (A.sectionChartData_coord_ae_eq μ i s).symm)
    (fun i ↦ (hw' i).trans (A.sectionChartData_coord_ae_eq μ i s).symm)

end Sobolev

end TauCeti
