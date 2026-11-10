/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import TauCeti.Analysis.Sobolev.Wkp.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas

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
diffeomorphisms between open sets, carry null sets to null sets. The space `W^{k,p}(V)` is
`TauCeti.SobolevSection A μ p k`; the analogue for bases with boundary is built from the same
construction in `TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Bordered`.

## Main definitions

* `TauCeti.SectionChartData`: chart data reading sections as functions on open subsets of `E`.
* `TauCeti.SectionChartData.chartValueL`: the `F`-valued `Lᵖ` function on `C.image i` assembled
  from the chart-`i` Sobolev components of a tuple.
* `TauCeti.SectionChartData.sobolevSections`: the tuples of chartwise Sobolev components of
  sections.
* `TauCeti.SectionChartData.lowerOrderL`: the continuous inclusion of order `k + 1` into order `k`.
* `TauCeti.SectionChartData.ofComponents`: the linear map into the Sobolev sections from a space of
  sections with chartwise Sobolev components.
* `TauCeti.FiniteBundleAtlas.sectionChartData`: the chart data of a finite bundle atlas.
* `TauCeti.SobolevSection A μ p k`: the Banach space `W^{k,p}(V)`.

## Main results

* `TauCeti.SectionChartData.mem_sobolevSections_iff_forall_compatible`: a tuple consists of the
  components of a section exactly when its chart data satisfy the cocycle relations.
* `TauCeti.SectionChartData.isClosed_sobolevSections`,
  `TauCeti.SobolevSection.instCompleteSpace`: completeness.
* `TauCeti.SectionChartData.norm_le_sum_of_norm_le`: the norm is at most the sum of the component
  norms.

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
that agrees at each point of `image i'` with the coordinate change of one of them. Finite bundle
atlases over manifolds with and without boundary give such data. -/
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

theorem coord_zero (i : Fin C.n) {y : E} (hy : y ∈ C.image i) : C.coord i 0 y = 0 := by
  simpa using C.coord_smul i 0 0 y hy

/-- Chart transitions carry null sets to null sets: a property holding almost everywhere on the
image of chart `i` holds, after composition with the chart transition, almost everywhere on the
overlap of charts `i` and `i'`. -/
@[expose] def AETransition [MeasurableSpace E] (μ : Measure E) : Prop :=
  ∀ ⦃i i' : Fin C.n⦄ ⦃P : E → Prop⦄, (∀ᵐ y ∂μ.restrict (C.image i), P y) →
    ∀ᵐ y ∂μ.restrict (C.overlap i i'), P (C.transition i i' y)

end Coordinates

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
    hC (i' := i') (hs i), ae_restrict_mem (C.isOpen_overlap i i').measurableSet] with y h' h hy
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
    hC (i' := i') hae] with y hy h' h
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
theorem ext {w w' : C.sobolevSections μ p k}
    (h : ∀ i j, Wkp.value k ((w : C.SobolevData μ p k) i j) =
      Wkp.value k ((w' : C.SobolevData μ p k) i j)) : w = w' :=
  Subtype.ext <| funext fun i ↦ funext fun j ↦ Wkp.ext k (h i j)

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
  ((ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.pi fun j ↦ (Wkp.lowerOrderL k).comp
    ((ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin (finrank ℝ F) ↦ Wkp μ (C.image i) p (k + 1)) j).comp
      (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun i : Fin C.n ↦ ∀ _ : Fin (finrank ℝ F), Wkp μ (C.image i) p (k + 1)) i))).comp
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
  map_add' t t' := C.ext μ p k fun i j ↦ Lp.ext <| by
    filter_upwards [(h (t + t') i j).choose_spec, (h t i j).choose_spec, (h t' i j).choose_spec,
      Wkp.value_add k (h t i j).choose (h t' i j).choose ▸ Lp.coeFn_add _ _,
      ae_restrict_mem (C.image i).isOpen.measurableSet] with y h₀ h₁ h₂ hadd hy
    simp only [Submodule.coe_add, Pi.add_apply] at hadd ⊢
    rw [h₀, hadd, h₁, h₂, map_add, C.coord_add i _ _ y hy, map_add]
  map_smul' c t := C.ext μ p k fun i j ↦ Lp.ext <| by
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

end Components

end Sobolev

end SectionChartData

namespace FiniteBundleAtlas

variable {E : Type*} [TopologicalSpace E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]
  (A : FiniteBundleAtlas E M F V)

/-- The chart data of a finite bundle atlas: a section is read in chart `i` as `A.coord i s` on the
image `A.image i` of the chart. At each point the gluing of a family of functions is read off from
the function of any chart containing the point. -/
@[expose] def sectionChartData : SectionChartData E F (∀ x, V x) where
  n := A.n
  image := A.image
  overlap := A.overlap
  isOpen_overlap := A.isOpen_overlap
  overlap_subset_image := A.overlap_subset_image
  transition := A.transition
  coordChange i i' y := (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
  coord := A.coord
  coord_add i s t _ hy := A.coord_add i s t hy
  coord_smul i c s _ hy := A.coord_smul i c s hy
  coord_eq_coordChange _ _ s _ hy := A.coord_eq_coordChange s hy
  exists_glue f := by
    classical
    let idx : M → Fin A.n := fun x ↦ (A.exists_mem_dom x).choose
    have hidx (x : M) : x ∈ A.dom (idx x) := (A.exists_mem_dom x).choose_spec
    refine ⟨fun x ↦ (A.triv (idx x)).symm x (f (idx x) (A.chart (idx x) x)), fun i' y hy ↦ ?_⟩
    obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hy
    have hov := A.chart_mem_overlap (hidx x) hx
    refine ⟨idx x, hov, ?_⟩
    rw [A.coord_eq_coordChange _ hov, A.transition_chart hx, A.coord_chart _ (hidx x),
      (A.triv (idx x)).apply_mk_symm (A.dom_subset_baseSet _ (hidx x))]
    rfl

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
    A.sectionChartData.AETransition μ :=
  fun _ _ _ h ↦ A.ae_restrict_overlap_transition h

variable [FiniteDimensional ℝ F]

/-- The Sobolev space `W^{k,p}(V)` of sections of `V` with respect to the finite bundle atlas `A`:
the tuples of chartwise Sobolev components of sections, with the maximum of the component norms. -/
abbrev SobolevSection : Type u :=
  A.sectionChartData.sobolevSections μ p k

/-- **Completeness.** The Sobolev space of sections of a vector bundle is a Banach space. -/
instance SobolevSection.instCompleteSpace [IsManifold 𝓘(ℝ, E) 1 M] :
    CompleteSpace (SobolevSection A μ p k) :=
  SectionChartData.completeSpace_sobolevSections (A.aeTransition_sectionChartData μ)

end Sobolev

end TauCeti
