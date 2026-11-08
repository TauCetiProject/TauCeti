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

The charts are fixed by a `TauCeti.FiniteBundleAtlas`: finitely many relatively compact open sets
`dom i` covering `M`, inside preferred manifold charts and bundle trivializations. In chart
`i` a section `s` is read as the `F`-valued function `A.coord i s` on the open set
`A.image i = chart i '' dom i` of `E`. Fixing a basis of `F`, an element of the space is a tuple of
scalar Sobolev functions `w i j ∈ W^{k,p}(A.image i)` (the components in chart `i`), one for each
chart and each basis vector, that are the components of a single section: there is a section `s`
with `A.chartValueL μ p k i w = A.coord i s` almost everywhere on `A.image i` for every `i`, with
respect to the Haar measure `μ` of `E`. These tuples form the submodule
`TauCeti.sobolevSections A μ p k` of the finite product of scalar Sobolev spaces, and
`TauCeti.SobolevSection A μ p k` carries the product norm, the maximum of the chartwise component
norms.

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

theorem compatible_iff {w : SobolevData A μ p k} {i i' : Fin A.n} :
    A.Compatible μ p k w i i' ↔ ∀ᵐ y ∂μ.restrict (A.overlap i i'), A.chartValueL μ p k i' w y =
      (A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y)
        (A.chartValueL μ p k i w (A.transition i i' y)) :=
  Iff.rfl

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
  obtain ⟨x, hx, rfl⟩ := A.mem_image.1 hyU
  have hxi := hidx x
  have hov : A.chart i' x ∈ A.overlap (idx x) i' := A.chart_mem_overlap hxi hx
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
    ae_all_iff.2 fun m ↦ by simpa only [mem_ofPred_eq, compatible_iff] using hw m
  simp only [mem_ofPred_eq, compatible_iff]
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

omit [IsManifold 𝓘(ℝ, E) 1 M] in
/-- Two elements of `W^{k,p}(V)` are equal when their components have equal values. -/
theorem ext {w w' : SobolevSection A μ p k}
    (h : ∀ i j, Wkp.value k ((w : SobolevData A μ p k) i j) =
      Wkp.value k ((w' : SobolevData A μ p k) i j)) : w = w' :=
  Subtype.ext <| funext fun i ↦ funext fun j ↦ Wkp.ext k (h i j)

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
