/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import TauCeti.Analysis.Sobolev.Leibniz
public import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients
public import TauCeti.Geometry.Manifold.MFDeriv.ModelChart
public import TauCeti.Geometry.Manifold.VectorBundle.FiniteBundleAtlas.Transfer
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic

/-!
# Transfer of chart data of Sobolev sections between charts

Let `M` be a smooth manifold without boundary modelled on a finite-dimensional real inner product
space `E`, let `V → M` be a smooth real vector bundle with finite-dimensional model fibre `F`, and
let `A` be a finite bundle atlas. This file compares the chart data of an element of `W^{k,p}(V)`,
for `1 ≤ p ≤ ∞`, in two charts.

On an open set `P` of chart-`j` coordinates with compact closure inside the open set
`A.transferDomain i j`, where chart `i` and both bundle charts are defined, the chart coordinate
change `(A.chart j).symm ≫ₕ A.chart i` is a change of variables of order `k` in the sense of
`TauCeti.Wkp.IsChangeOfVariables` as soon as `M` is `C^(max k 1)`, and the coordinate change of
the bundle is a smooth operator-valued coefficient. The continuous linear map
`TauCeti.FiniteBundleAtlas.transferL` sends chart-`i` data on an open set `Q` containing the image
of `P` under the chart coordinate change to chart-`j` data on `P`: it precomposes with the chart
coordinate change and then multiplies by the coordinate change of the bundle
(`TauCeti.Wkp.contDiffOnCLMApplyL`). If `P` lies in the overlap of the two chart domains and
`Q ⊆ A.image i`, the chart-`j` data of an element of `W^{k,p}(V)` restricted to `P` are the
transfer of its chart-`i` data restricted to `Q`
(`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`).

For order-one weak derivatives, `TauCeti.FiniteBundleAtlas.chartDerivL_ae_overlap` gives the
chain and operator Leibniz formula under only the original `C¹` manifold and vector-bundle
structure, for arbitrary finite-dimensional real inner-product models and `1 ≤ p ≤ ∞`.

## Main definitions

* `TauCeti.FiniteBundleAtlas.transferL`: the transfer of chart-`i` data to chart-`j` data.

## Main results

* `TauCeti.FiniteBundleAtlas.chartDerivL_ae_overlap`: native weak chart derivatives obey the
  chain and Leibniz rules on overlaps for arbitrary real finite-dimensional model spaces.

* `TauCeti.FiniteBundleAtlas.value_transferL_ae_of_coord`: transfer preserves the readings of
  an actual section, without requiring global Sobolev membership.

* `TauCeti.FiniteBundleAtlas.exists_isChangeOfVariables_chart_symm_trans`: chart coordinate
  changes are changes of variables of every order on relatively compact subsets of the transfer
  domain.
* `TauCeti.FiniteBundleAtlas.ae_comp_chart_symm_trans`: almost-everywhere statements pull back
  along chart coordinate changes.
* `TauCeti.FiniteBundleAtlas.value_transferL_ae`, `TauCeti.FiniteBundleAtlas.eq_transferL_iff`:
  the components of a transfer are those of the bundle coordinate change applied to the
  precomposed input values, and this characterizes the transfer.
* `TauCeti.FiniteBundleAtlas.value_transferL_ae_congr`: the values of a transfer only depend on
  the values of the input, whatever the order and the exponent.
* `TauCeti.FiniteBundleAtlas.lowerOrder_transferL`: transfer commutes with forgetting the highest
  weak derivative.
* `TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`: chart data of a Sobolev section are
  transferred between charts.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

universe u

namespace TauCeti

section WeakOverlap

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle ℝ F V]

variable [MeasurableSpace E] [BorelSpace E]

variable (A : FiniteBundleAtlas E M F V) (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞)
  [Fact (1 ≤ p)]

variable [FiniteDimensional ℝ F]

variable [IsManifold 𝓘(ℝ, E) 1 M] [ContMDiffVectorBundle 1 F V 𝓘(ℝ, E)] in
/-- On the overlap of charts `i` and `i'`, the weak derivative of the chart data in chart `i'` of an
order-one Sobolev section is that of `y ↦ g y (uᵢ (τ y))`, by the weak chain and Leibniz rules. -/
theorem FiniteBundleAtlas.chartDerivL_ae_overlap (w : A.sectionChartData.sobolevSections μ p 1)
    (i i' : Fin A.n) :
    ∀ᵐ y ∂μ.restrict (A.overlap i i'),
      A.sectionChartData.chartDerivL μ p i' w y =
        ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm y) : F →L[ℝ] F).comp
          ((A.sectionChartData.chartDerivL μ p i w (A.transition i i' y)).comp
            (fderiv ℝ (A.transition i i') y)) +
        (fderiv ℝ (fun z ↦ ((A.triv i).coordChangeL ℝ (A.triv i') ((A.chart i').symm z) :
          F →L[ℝ] F)) y).flip
          (A.sectionChartData.chartValueL μ p 1 i w (A.transition i i' y)) := by
  let O : Opens E := ⟨A.overlap i i', A.isOpen_overlap i i'⟩
  have hC := A.aeTransition_sectionChartData μ
  have hτ := (A.sectionChartData.hasWeakFDerivOn_chartValueL μ p i w).comp_contDiffOn_diffeo
    (U := O) (A.contDiffOn_transition i i')
    (fun y hy y' hy' h ↦ by rw [← A.transition_transition hy, h, A.transition_transition hy'])
    (fun y hy ↦ by
      rw [A.fderiv_transition hy]
      exact ContinuousLinearEquiv.toLinearEquiv _ |>.isUnit_det'.ne_zero)
    fun y hy ↦ A.overlap_subset_image i' i (A.transition_mem_overlap hy)
  have hcoord := (A.contDiffOn_coordChangeL_transferDomain (n := 1) i i').mono
    (A.overlap_subset_transferDomain i i')
  have hprod := hτ.contDiffOn_clm_apply_of_ne_zero hcoord one_ne_zero
  have hcompat : ∀ᵐ y ∂μ.restrict O, ((A.triv i).coordChangeL ℝ (A.triv i')
      ((A.chart i').symm y) : F →L[ℝ] F)
        (A.sectionChartData.chartValueL μ p 1 i w (A.transition i i' y)) =
      A.sectionChartData.chartValueL μ p 1 i' w y := by
    filter_upwards [(A.sectionChartData.compatible_iff μ p 1).1
      (SectionChartData.compatible_of_mem hC w.property i i'),
      ae_restrict_mem (A.isOpen_overlap i i').measurableSet] with y h hy
    rw [A.sectionChartData_coordChange_of_mem hy, A.sectionChartData_transition_of_mem hy] at h
    exact h.symm
  -- `O` is the overlap as an open set and `A.sectionChartData.image i'` is the image of chart `i'`
  -- as an open set; the type ascription states the inclusion of overlap into image as one of
  -- `Opens E`, which `A.overlap_subset_image` proves for the underlying sets.
  have hO : O ≤ A.sectionChartData.image i' := A.overlap_subset_image i i'
  exact ((A.sectionChartData.hasWeakFDerivOn_chartValueL μ p i' w).mono hO).ae_eq
      (hprod.congr_ae hcompat)

end WeakOverlap

section ChangeOfVariables

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] {F : Type*} [TopologicalSpace F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] (A : FiniteBundleAtlas E M F V)

namespace FiniteBundleAtlas

/-- **Chart coordinate changes are changes of variables.** On a `C^(max k 1)` manifold, on an open
set `P` with compact closure inside the transfer domain, the coordinate change from chart `j` to
chart `i` is a change of variables of order `k` from `P` into any open set containing its image. -/
theorem exists_isChangeOfVariables_chart_symm_trans (k : ℕ)
    [IsManifold 𝓘(ℝ, E) (max k 1 : ℕ) M]
    {i j : Fin A.n} {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart j).symm ≫ₕ A.chart i) P Q) :
    ∃ L c, Wkp.IsChangeOfVariables k P Q ((A.chart j).symm ≫ₕ A.chart i) L c := by
  have hn : (1 : WithTop ℕ∞) ≤ (max k 1 : ℕ) := by exact_mod_cast le_max_right k 1
  have hj := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := (max k 1 : ℕ)) (A.center j)
  have hi := IsManifold.chart_mem_maximalAtlas (I := 𝓘(ℝ, E)) (n := (max k 1 : ℕ)) (A.center i)
  have hPO := hPD.trans (transferDomain_subset_source A i j)
  exact Wkp.IsChangeOfVariables.exists_of_isCompact_closure
    ((A.chart j).symm ≫ₕ A.chart i).open_source (contDiffOn_symm_trans_of_mem_maximalAtlas hj hi)
    (by exact_mod_cast le_max_left k 1) hn
    (((A.chart j).symm ≫ₕ A.chart i).injOn.mono (subset_closure.trans hPO))
    (fun x hx ↦ det_fderiv_symm_trans_ne_zero (zero_lt_one.trans_le hn).ne' hj hi (hPO hx))
    hPc hPO hPQ

/-- **Almost-everywhere statements pull back along chart coordinate changes.** On a `C^1`
manifold, on an open set `P` with compact closure inside the transfer domain, a property holding
almost everywhere on an open set `Q` containing the image of `P` under the coordinate change
`(A.chart j).symm ≫ₕ A.chart i` holds almost everywhere on `P` after composing with it. -/
theorem ae_comp_chart_symm_trans [IsManifold 𝓘(ℝ, E) 1 M] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
    {i j : Fin A.n} {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart j).symm ≫ₕ A.chart i) P Q) {R : E → Prop}
    (hR : ∀ᵐ z ∂μ.restrict Q, R z) :
    ∀ᵐ y ∂μ.restrict P, R (((A.chart j).symm ≫ₕ A.chart i) y) := by
  have : IsManifold 𝓘(ℝ, E) (max 0 1 : ℕ) M := by simpa using ‹IsManifold 𝓘(ℝ, E) 1 M›
  obtain ⟨L, c, h⟩ := A.exists_isChangeOfVariables_chart_symm_trans 0 hPc hPD hPQ
  exact h.ae_comp hR

end FiniteBundleAtlas

end ChangeOfVariables

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] (A : FiniteBundleAtlas E M F V)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

variable (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

namespace FiniteBundleAtlas

/-- **Transfer of chart data.** For `1 ≤ p ≤ ∞`, an open set `P` of chart-`j` coordinates with
compact closure in the transfer domain, and an open set `Q` containing the image of `P` under the
chart coordinate change `(A.chart j).symm ≫ₕ A.chart i`, the continuous linear map sending
chart-`i` components `u` on `Q` to the chart-`j` components on `P` of
`y ↦ g y (u (A.chart i ((A.chart j).symm y)))`, where `g` is the coordinate change from bundle
chart `i` to bundle chart `j`. The chart data of a
Sobolev section are related by this map (`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`). -/
def transferL (i j : Fin A.n) {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart j).symm ≫ₕ A.chart i) P Q) :
    (Fin (finrank ℝ F) → Wkp μ Q p k) →L[ℝ] (Fin (finrank ℝ F) → Wkp μ P p k) :=
  (Wkp.contDiffOnCLMApplyL (A.isOpen_transferDomain i j).uniqueDiffOn hPc hPD k (finBasis ℝ F)
      (finBasis ℝ F) (A.contDiffOn_coordChangeL_transferDomain i j)).comp
    (ContinuousLinearMap.piMap fun _ ↦ Wkp.compL
      (A.exists_isChangeOfVariables_chart_symm_trans k hPc hPD hPQ).choose_spec.choose_spec)

/-- The chart-`j` components of a transfer are, almost everywhere on `P`, the components of the
coordinate change from bundle chart `i` to bundle chart `j` applied to the vector whose components
are the values of the input at the image of the point under the chart coordinate change. -/
theorem value_transferL_ae (i j : Fin A.n) {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart j).symm ≫ₕ A.chart i) P Q) (u : Fin (finrank ℝ F) → Wkp μ Q p k)
    (m : Fin (finrank ℝ F)) :
    (Wkp.value k (A.transferL μ p k i j hPc hPD hPQ u m) : E → ℝ) =ᵐ[μ.restrict P]
      fun y ↦ (finBasis ℝ F).repr ((A.triv i).coordChangeL ℝ (A.triv j) ((A.chart j).symm y)
        (∑ l, Wkp.value k (u l) (((A.chart j).symm ≫ₕ A.chart i) y) • finBasis ℝ F l)) m := by
  set h := (A.exists_isChangeOfVariables_chart_symm_trans k hPc hPD hPQ).choose_spec.choose_spec
  filter_upwards [Wkp.value_contDiffOnCLMApplyL_ae (A.isOpen_transferDomain i j).uniqueDiffOn
      hPc hPD k
      (finBasis ℝ F) (finBasis ℝ F) (A.contDiffOn_coordChangeL_transferDomain i j)
      ((ContinuousLinearMap.piMap fun _ ↦ Wkp.compL h) u) m,
    ae_all_iff.2 fun l ↦ Wkp.value_compL_ae h (u l)] with y hy hl
  rw [transferL, ContinuousLinearMap.comp_apply, hy]
  simp only [ContinuousLinearMap.coe_piMap', Pi.map_apply, hl, ContinuousLinearEquiv.coe_coe]

/-- Transferring components that represent a section in one chart represents that same section
in the other chart. No global Sobolev membership of the section is assumed. -/
theorem value_transferL_ae_of_coord {i j : Fin A.n} {P Q : Opens E}
    (hP : (P : Set E) ⊆ A.overlap i j) (hPc : IsCompact (closure (P : Set E)))
    (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart j).symm ≫ₕ A.chart i) P Q)
    (s : ∀ x, V x) (u : Fin (finrank ℝ F) → Wkp μ Q p k)
    (hu : ∀ l, (Wkp.value k (u l) : E → ℝ) =ᵐ[μ.restrict Q]
      fun y ↦ (finBasis ℝ F).repr (A.coord i s y) l) (m : Fin (finrank ℝ F)) :
    (Wkp.value k (A.transferL μ p k i j hPc hPD hPQ u m) : E → ℝ)
      =ᵐ[μ.restrict P] fun y ↦ (finBasis ℝ F).repr (A.coord j s y) m := by
  have hc := (A.exists_isChangeOfVariables_chart_symm_trans k hPc hPD hPQ).choose_spec.choose_spec
  filter_upwards [A.value_transferL_ae μ p k i j hPc hPD hPQ u m,
    hc.ae_comp (ae_all_iff.2 hu), ae_restrict_mem P.isOpen.measurableSet] with y hy hu hyP
  rw [hy]
  have hsum : ∑ l, Wkp.value k (u l) (((A.chart j).symm ≫ₕ A.chart i) y) •
      finBasis ℝ F l = A.coord i s (((A.chart j).symm ≫ₕ A.chart i) y) := by
    simp_rw [hu]
    exact (finBasis ℝ F).sum_repr _
  rw [hsum]
  have htr : A.transition i j y = ((A.chart j).symm ≫ₕ A.chart i) y := by
    obtain ⟨x, hx, rfl⟩ := A.mem_overlap.1 (hP hyP)
    rw [A.transition_chart hx.2, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      (A.chart j).left_inv (A.dom_subset_chart_source j hx.2)]
  rw [A.coord_eq_coordChange s (hP hyP), htr]

/-- A transfer is characterized by its components: `v` is the transfer of `u` exactly when the
components of `v` are, almost everywhere on `P`, those described in
`TauCeti.FiniteBundleAtlas.value_transferL_ae`. -/
theorem eq_transferL_iff (i j : Fin A.n) {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart j).symm ≫ₕ A.chart i) P Q) (u : Fin (finrank ℝ F) → Wkp μ Q p k)
    (v : Fin (finrank ℝ F) → Wkp μ P p k) :
    v = A.transferL μ p k i j hPc hPD hPQ u ↔ ∀ m,
      (Wkp.value k (v m) : E → ℝ) =ᵐ[μ.restrict P]
        fun y ↦ (finBasis ℝ F).repr ((A.triv i).coordChangeL ℝ (A.triv j) ((A.chart j).symm y)
          (∑ l, Wkp.value k (u l) (((A.chart j).symm ≫ₕ A.chart i) y) • finBasis ℝ F l)) m := by
  refine ⟨fun hv m ↦ hv ▸ A.value_transferL_ae μ p k i j hPc hPD hPQ u m, fun hv ↦ ?_⟩
  funext m
  exact Wkp.ext k (Lp.ext ((hv m).trans (A.value_transferL_ae μ p k i j hPc hPD hPQ u m).symm))

variable {μ k} in
/-- The values of the transfer of a family of Sobolev functions on `Q` only depend on the values of
the family almost everywhere on `Q`, whatever the order and the exponent. -/
theorem value_transferL_ae_congr {i j : Fin A.n} {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart j).symm ≫ₕ A.chart i) P Q) {q r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    {k' : ℕ} (u : Fin (finrank ℝ F) → Wkp μ Q q k)
    (v : Fin (finrank ℝ F) → Wkp μ Q r k')
    (huv : ∀ l, (Wkp.value k (u l) : E → ℝ) =ᵐ[μ.restrict Q] Wkp.value k' (v l))
    (m : Fin (finrank ℝ F)) :
    (Wkp.value k (A.transferL μ q k i j hPc hPD hPQ u m) : E → ℝ) =ᵐ[μ.restrict P]
      Wkp.value k' (A.transferL μ r k' i j hPc hPD hPQ v m) := by
  obtain ⟨_, _, h⟩ := A.exists_isChangeOfVariables_chart_symm_trans k hPc hPD hPQ
  filter_upwards [A.value_transferL_ae μ q k i j hPc hPD hPQ u m,
    A.value_transferL_ae μ r k' i j hPc hPD hPQ v m,
    h.ae_comp (ae_all_iff.2 huv)] with y hu hv hy
  rw [hu, hv]
  simp only [hy]

/-- Transfer commutes with forgetting the highest weak derivative. -/
theorem lowerOrder_transferL (i j : Fin A.n) {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart j).symm ≫ₕ A.chart i) P Q)
    (u : Fin (finrank ℝ F) → Wkp μ Q p (k + 1)) (m : Fin (finrank ℝ F)) :
    Wkp.lowerOrder k (A.transferL μ p (k + 1) i j hPc hPD hPQ u m) =
      A.transferL μ p k i j hPc hPD hPQ (fun l ↦ Wkp.lowerOrder k (u l)) m := by
  refine congrFun ((A.eq_transferL_iff μ p k i j hPc hPD hPQ _
    fun m ↦ Wkp.lowerOrder k (A.transferL μ p (k + 1) i j hPc hPD hPQ u m)).2 fun m ↦ ?_) m
  simp only [← Wkp.value_succ]
  exact A.value_transferL_ae μ p (k + 1) i j hPc hPD hPQ u m

/-- **Chart data of Sobolev sections are transferred between charts.** Let `1 ≤ p ≤ ∞`. If `P`
lies in the overlap of the domains of charts `i` and `j` (read in chart `j`) and has compact
closure in the transfer domain, and `Q ⊆ A.image i` contains the image of `P` under the chart
coordinate change `(A.chart j).symm ≫ₕ A.chart i`, then the chart-`j` components of an element of
`W^{k,p}(V)` restricted to `P` are the transfer of its chart-`i` components restricted to `Q`. -/
theorem restrictL_eq_transferL {w : A.sectionChartData.SobolevData μ p k}
    (hw : w ∈ A.sectionChartData.sobolevSections μ p k) {i j : Fin A.n} {P Q : Opens E}
    (hP : (P : Set E) ⊆ A.overlap i j) (hPc : IsCompact (closure (P : Set E)))
    (hPD : closure (P : Set E) ⊆ A.transferDomain i j) (hQ : Q ≤ A.image i)
    (hPQ : MapsTo ((A.chart j).symm ≫ₕ A.chart i) P Q) (m : Fin (finrank ℝ F)) :
    Wkp.restrictL (SetLike.coe_subset_coe.1 (hP.trans (A.overlap_subset_image i j))) k (w j m) =
      A.transferL μ p k i j hPc hPD hPQ (fun l ↦ Wkp.restrictL hQ k (w i l)) m := by
  have hPj : P ≤ A.image j := SetLike.coe_subset_coe.1 (hP.trans (A.overlap_subset_image i j))
  refine Wkp.ext k (Lp.ext ?_)
  have hcompat := ae_restrict_of_ae_restrict_of_subset hP
    ((SectionChartData.compatible_iff _ _ _ _).1
      (SectionChartData.compatible_of_mem (A.aeTransition_sectionChartData μ) hw i j))
  have hj := ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hPj)
    (A.sectionChartData.chartValueL_apply_ae μ p k j w)
  have hi : ∀ᵐ y ∂μ.restrict P,
      A.sectionChartData.chartValueL μ p k i w (((A.chart j).symm ≫ₕ A.chart i) y) =
        ∑ l, Wkp.value k (w i l) (((A.chart j).symm ≫ₕ A.chart i) y) • finBasis ℝ F l :=
    A.ae_comp_chart_symm_trans hPc hPD hPQ (ae_restrict_of_ae_restrict_of_subset
      (SetLike.coe_subset_coe.2 hQ) (A.sectionChartData.chartValueL_apply_ae μ p k i w))
  have hres : ∀ᵐ y ∂μ.restrict P, ∀ l, Wkp.value k (Wkp.restrictL hQ k (w i l))
      (((A.chart j).symm ≫ₕ A.chart i) y) =
        Wkp.value k (w i l) (((A.chart j).symm ≫ₕ A.chart i) y) :=
    A.ae_comp_chart_symm_trans hPc hPD hPQ
      (ae_all_iff.2 fun l ↦ Wkp.value_restrictL_ae hQ k (w i l))
  filter_upwards [Wkp.value_restrictL_ae hPj k (w j m), hcompat, hj, hi, hres,
    A.value_transferL_ae μ p k i j hPc hPD hPQ (fun l ↦ Wkp.restrictL hQ k (w i l)) m,
    ae_restrict_mem P.isOpen.measurableSet] with y hy₁ hy₂ hy₃ hy₄ hy₅ hy₆ hyP
  rw [A.sectionChartData_coordChange_of_mem (hP hyP),
    A.sectionChartData_transition_of_mem (hP hyP),
    A.transition_eq_symm_trans] at hy₂
  have hval : Wkp.value k (w j m) y =
      (finBasis ℝ F).repr (A.sectionChartData.chartValueL μ p k j w y) m := by
    rw [hy₃, (finBasis ℝ F).repr_sum_self]
  refine hy₁.trans ((hval.trans ?_).trans hy₆.symm)
  rw [hy₂, hy₄]
  simp only [hy₅, ContinuousLinearEquiv.coe_coe]

end FiniteBundleAtlas

end Sobolev

end TauCeti
