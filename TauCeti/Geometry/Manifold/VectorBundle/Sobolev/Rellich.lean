/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ShrinkingLemma
public import TauCeti.Analysis.Normed.Operator.Compact.Pi
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
public import TauCeti.Analysis.Sobolev.Wkp.FiniteCover
public import TauCeti.Analysis.Sobolev.Wkp.Local.Compactness
public import TauCeti.Analysis.Sobolev.Wkp.SmoothCoefficients
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Basic

/-!
# Rellich compactness for Sobolev sections of a vector bundle

Let `M` be a smooth Hausdorff manifold without boundary modelled on a finite-dimensional real inner
product space `E`, let `V → M` be a smooth real vector bundle with finite-dimensional model fibre
`F`, and let `A` be a finite bundle atlas, so that `M` is compact. For `1 ≤ p < ∞` and every order
`k`, the inclusion `W^{k+1,p}(V) → W^{k,p}(V)` of `TauCeti.SectionChartData.lowerOrderL` is a
compact operator (`TauCeti.SobolevSection.isCompactOperator_lowerOrderL`).

The local input is Rellich compactness on relatively compact subdomains,
`TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL`. It does not apply directly to the chart
images `A.image i`, whose closures need not lie inside an open set on which the chart data are
controlled. Instead the chart data in chart `i` are transferred from the other charts.

**Chart transfer.** On an open set `P` of chart-`i` coordinates with compact closure inside the open
set `A.transferDomain i j`, where chart `j` and both bundle charts are defined, the chart coordinate
change `(A.chart i).symm ≫ₕ A.chart j` is a change of variables of every order in the sense of
`TauCeti.Wkp.IsChangeOfVariables`, and the coordinate change of the bundle is a smooth
operator-valued coefficient. If `P` lies in the overlap of the two chart domains, where the chart
coordinate change is the transition `A.transition j i`, the chart-`i` data of an element of
`W^{k,p}(V)` restricted to `P` are the image of its chart-`j` data restricted to any open set `Q`
containing the image of `P` under the continuous linear map `TauCeti.FiniteBundleAtlas.transferL`:
precomposition with the chart coordinate change followed by multiplication by the coordinate change
of the bundle (`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`). The multiplication is
`TauCeti.Wkp.contDiffOnOperatorSMulL`.

**Compactness.** Shrink the chart domains to open sets `D j` with `closure (D j) ⊆ A.dom j` that
still cover `M`. The chart image `A.image i` is covered by the finitely many pieces
`A.chart i '' (A.dom i ∩ D j)`. On each piece the chart-`i` data are transferred from the
chart-`j` data restricted to `A.chart j '' D j`, which has compact closure inside `A.image j`, so
the piece data depend compactly on the section from order `k + 1` to order `k`. Gluing the pieces
with `TauCeti.Wkp.restrictCompatibleEquiv` gives compactness on `A.image i`, and the space of
Sobolev sections is closed in the product of the chartwise Sobolev spaces.

## Main definitions

* `TauCeti.FiniteBundleAtlas.transferDomain`: the chart-`i` coordinates on which chart `j` and the
  bundle charts `i` and `j` are defined.
* `TauCeti.FiniteBundleAtlas.transferL`: the transfer of chart-`j` data to chart-`i` data.

## Main results

* `TauCeti.FiniteBundleAtlas.exists_isChangeOfVariables_coordChange`: chart coordinate changes are
  changes of variables of every order on relatively compact subsets of the transfer domain.
* `TauCeti.FiniteBundleAtlas.contDiffOn_coordChangeL_transferDomain`: the coordinate change of the
  bundle, read in chart `i`, is smooth on the transfer domain.
* `TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`: chart data of a Sobolev section are
  transferred between charts.
* `TauCeti.SobolevSection.isCompactOperator_lowerOrderL`: **Rellich's theorem** for Sobolev
  sections, `W^{k+1,p}(V) → W^{k,p}(V)` is compact.
* `TauCeti.SobolevSection.isCompactOperator_lowerOrderL_zero`: the inclusion
  `W^{1,p}(V) → W^{0,p}(V) = Lᵖ(V)` is compact.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton (1989), Chapter III, Theorem 2.6.
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Module Set TopologicalSpace
open scoped Manifold ContDiff ENNReal Topology

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
theorem isOpen_transferDomain (i j : Fin A.n) : IsOpen (A.transferDomain i j) :=
  (A.chart i).isOpen_inter_preimage_symm ((A.chart j).open_source.inter
    ((A.triv i).open_baseSet.inter (A.triv j).open_baseSet))

omit [NormedSpace ℝ E] in
private theorem transferDomain_subset_source (i j : Fin A.n) :
    A.transferDomain i j ⊆ ((A.chart i).symm ≫ₕ A.chart j).source := fun _ hy ↦ by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source]
  exact ⟨hy.1, hy.2.1⟩

omit [NormedSpace ℝ E] in
/-- A finite bundle atlas of a Hausdorff manifold has a shrinking: open sets `D j` with
`closure (D j) ⊆ A.dom j` still covering `M`. The manifold is compact, being covered by the
finitely many compact sets `closure (A.dom j)`, hence normal. -/
private theorem exists_shrinking [T2Space M] :
    ∃ D : Fin A.n → Set M, (∀ j, IsOpen (D j)) ∧ (∀ j, closure (D j) ⊆ A.dom j) ∧
      ∀ x, ∃ j, x ∈ D j := by
  have hcpt : CompactSpace M := by
    refine ⟨?_⟩
    have huniv : (univ : Set M) = ⋃ i, closure (A.dom i) :=
      (eq_univ_of_univ_subset (A.iUnion_dom ▸ iUnion_mono fun i ↦ subset_closure)).symm
    rw [huniv]
    exact isCompact_iUnion fun i ↦ A.isCompact_closure_dom i
  obtain ⟨D, hcov, hDo, hD⟩ := exists_subset_iUnion_closure_subset isClosed_univ A.isOpen_dom
    (fun _ _ ↦ toFinite _) (A.iUnion_dom ▸ subset_rfl)
  exact ⟨D, hDo, hD, fun x ↦ mem_iUnion.1 (hcov (mem_univ x))⟩

omit [NormedSpace ℝ E] in
/-- **Transfer cover.** For a finite bundle atlas of a Hausdorff manifold, the image of each chart
`i` is covered by finitely many open pieces `P i j`. The piece `P i j` lies in the overlap of the
domains of charts `j` and `i`, has compact closure in the transfer domain, and is mapped by the
chart coordinate change into an open set `Q j` with compact closure inside the image of chart `j`.
The pieces are `A.chart i '' (A.dom i ∩ D j)` and `Q j = A.chart j '' D j` for a shrinking `D` of
the chart domains. -/
private theorem exists_transfer_cover [T2Space M] :
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

/-! ### Chart coordinate changes

The coordinate change from chart `i` to chart `j` is `(A.chart i).symm ≫ₕ A.chart j`. Its source
consists of the chart-`i` coordinates whose preimage lies in the source of chart `j`; on the overlap
of the chart domains it agrees with `A.transition j i`. -/

variable [IsManifold 𝓘(ℝ, E) ∞ M]

private theorem contDiffOn_chart_coordChange (i j : Fin A.n) :
    ContDiffOn ℝ ∞ ((A.chart i).symm ≫ₕ A.chart j) ((A.chart i).symm ≫ₕ A.chart j).source := by
  refine ((contDiffOn_ext_coord_change (I := 𝓘(ℝ, E)) (n := ∞) (A.center j)
    (A.center i))).congr_mono (fun y _ ↦ by simp) ?_
  intro y hy
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hy
  obtain ⟨hy, hy'⟩ := hy
  simp only [PartialEquiv.trans_source, PartialEquiv.symm_source, mem_inter_iff, mem_preimage,
    extChartAt_target, extChartAt_source, extChartAt_coe_symm, modelWithCornersSelf_coe,
    modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq, range_id, inter_univ,
    preimage_id_eq]
  exact ⟨hy, hy'⟩

private theorem differentiableAt_chart_coordChange {i j : Fin A.n} {y : E}
    (hy : y ∈ ((A.chart i).symm ≫ₕ A.chart j).source) :
    DifferentiableAt ℝ ((A.chart i).symm ≫ₕ A.chart j) y :=
  ((contDiffOn_chart_coordChange A i j).differentiableOn (by simp)).differentiableAt
    (((A.chart i).symm ≫ₕ A.chart j).open_source.mem_nhds hy)

/-- The Jacobian determinant of a chart coordinate change does not vanish: the reverse coordinate
change is a differentiable left inverse near every point. -/
private theorem det_fderiv_chart_coordChange_ne_zero {i j : Fin A.n} {y : E}
    (hy : y ∈ ((A.chart i).symm ≫ₕ A.chart j).source) :
    (fderiv ℝ ((A.chart i).symm ≫ₕ A.chart j) y).det ≠ 0 := by
  set e := (A.chart i).symm ≫ₕ A.chart j with he_def
  have he : e.symm = (A.chart j).symm ≫ₕ A.chart i := by
    rw [he_def, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hz : e y ∈ ((A.chart j).symm ≫ₕ A.chart i).source := by
    rw [← he, OpenPartialHomeomorph.symm_source]
    exact e.map_source hy
  have hd : DifferentiableAt ℝ e.symm (e y) := by
    rw [he]
    exact differentiableAt_chart_coordChange A hz
  have hid : e.symm ∘ e =ᶠ[𝓝 y] id := e.eventually_left_inverse hy
  have hcomp : (fderiv ℝ e.symm (e y)).comp (fderiv ℝ e y) = ContinuousLinearMap.id ℝ E := by
    rw [← fderiv_comp y hd (differentiableAt_chart_coordChange A hy), hid.fderiv_eq, fderiv_id]
  intro h0
  have hdet := congrArg ContinuousLinearMap.det hcomp
  change LinearMap.det ((fderiv ℝ e.symm (e y) : E →ₗ[ℝ] E) ∘ₗ (fderiv ℝ e y : E →ₗ[ℝ] E)) =
    LinearMap.det (ContinuousLinearMap.id ℝ E : E →ₗ[ℝ] E) at hdet
  rw [LinearMap.det_comp, show LinearMap.det (fderiv ℝ e y : E →ₗ[ℝ] E) = 0 from h0, mul_zero]
    at hdet
  simp at hdet

end FiniteBundleAtlas

end Geometry

section Sobolev

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] (A : FiniteBundleAtlas E M F V)

namespace FiniteBundleAtlas

/-- A smooth map on an open set `Ω`, injective on `P`, mapping `P` into `Q`, with invertible
derivative on the compact set `closure P ⊆ Ω`, is a change of variables of every order from `P`
into `Q`: derivative bounds and a lower bound for the Jacobian come from compactness. -/
private theorem exists_isChangeOfVariables_of_isCompact_closure {k : ℕ} {Ω : Set E} {Φ : E → E}
    {P Q : Opens E} (hΩ : IsOpen Ω) (hΦ : ContDiffOn ℝ ∞ Φ Ω) (hinj : InjOn Φ P)
    (hdet : ∀ x ∈ closure (P : Set E), (fderiv ℝ Φ x).det ≠ 0)
    (hPc : IsCompact (closure (P : Set E))) (hPΩ : closure (P : Set E) ⊆ Ω)
    (hPQ : MapsTo Φ P Q) : ∃ L c, Wkp.IsChangeOfVariables k P Q Φ L c := by
  have hsum : ContinuousOn
      (fun x ↦ ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i Φ x‖) (closure (P : Set E)) :=
    continuousOn_finsetSum _ fun i _ ↦ (ContinuousOn.continuousOn_iteratedFDeriv hΦ hΩ
      (by exact_mod_cast le_top)).norm.mono hPΩ
  obtain ⟨L, hL⟩ := hPc.exists_bound_of_continuousOn hsum
  have hdetc : ContinuousOn (fun x ↦ |(fderiv ℝ Φ x).det|) (closure (P : Set E)) :=
    (ContinuousLinearMap.continuous_det.comp_continuousOn
      ((hΦ.continuousOn_fderiv_of_isOpen hΩ (by simp)).mono hPΩ)).abs
  obtain ⟨c, hc, hcdet⟩ := hPc.exists_forall_le' hdetc fun x hx ↦ abs_pos.2 (hdet x hx)
  refine ⟨L, c,
    { contDiffOn := (hΦ.mono (subset_closure.trans hPΩ)).of_le (by exact_mod_cast le_top)
      differentiableOn := (hΦ.mono (subset_closure.trans hPΩ)).differentiableOn (by simp)
      injOn := hinj
      mapsTo := hPQ
      norm_iteratedFDeriv_le := fun i _ hik x hx ↦ ?_
      pos := hc
      le_abs_det := fun x hx ↦ hcdet x (subset_closure hx) }⟩
  have hx := hL x (subset_closure hx)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)] at hx
  exact (Finset.single_le_sum (fun j _ ↦ norm_nonneg (iteratedFDeriv ℝ j Φ x))
    (Finset.mem_range.2 (Nat.lt_succ_of_le hik))).trans hx

end FiniteBundleAtlas

variable [IsManifold 𝓘(ℝ, E) ∞ M]

namespace FiniteBundleAtlas

omit [NormedSpace ℝ F] in
/-- **Chart coordinate changes are changes of variables.** On an open set `P` with compact closure
inside the transfer domain, the coordinate change from chart `i` to chart `j` is a change of
variables of every order from `P` into any open set containing its image. -/
theorem exists_isChangeOfVariables_coordChange (k : ℕ) {i j : Fin A.n} {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart i).symm ≫ₕ A.chart j) P Q) :
    ∃ L c, Wkp.IsChangeOfVariables k P Q ((A.chart i).symm ≫ₕ A.chart j) L c := by
  have hPO := hPD.trans (transferDomain_subset_source A i j)
  exact exists_isChangeOfVariables_of_isCompact_closure
    ((A.chart i).symm ≫ₕ A.chart j).open_source (contDiffOn_chart_coordChange A i j)
    (((A.chart i).symm ≫ₕ A.chart j).injOn.mono (subset_closure.trans hPO))
    (fun x hx ↦ det_fderiv_chart_coordChange_ne_zero A (hPO hx)) hPc hPO hPQ

end FiniteBundleAtlas

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

namespace FiniteBundleAtlas


omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F] in
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

variable (μ : Measure E) [μ.IsAddHaarMeasure] (p : ℝ≥0∞) [Fact (1 ≤ p)] (k : ℕ)

namespace FiniteBundleAtlas


/-- **Transfer of chart data.** For an open set `P` of chart-`i` coordinates with compact closure in
the transfer domain, and an open set `Q` containing the image of `P` under the chart transition,
the continuous linear map sending chart-`j` components `u` on `Q` to the chart-`i` components on
`P` of `y ↦ g y (u (A.chart j ((A.chart i).symm y)))`, where `g` is the coordinate change from
bundle chart `j` to bundle chart `i`. The chart data of a Sobolev section are related by this map
(`TauCeti.FiniteBundleAtlas.restrictL_eq_transferL`). -/
def transferL (hp : p ≠ ⊤) (i j : Fin A.n) {P Q : Opens E}
    (hPc : IsCompact (closure (P : Set E))) (hPD : closure (P : Set E) ⊆ A.transferDomain i j)
    (hPQ : MapsTo ((A.chart i).symm ≫ₕ A.chart j) P Q) :
    (Fin (finrank ℝ F) → Wkp μ Q p k) →L[ℝ] (Fin (finrank ℝ F) → Wkp μ P p k) :=
  (Wkp.contDiffOnOperatorSMulL (A.isOpen_transferDomain i j) hPc hPD k (finBasis ℝ F)
      (finBasis ℝ F) (A.contDiffOn_coordChangeL_transferDomain i j)).comp
    (ContinuousLinearMap.piMap fun _ ↦ Wkp.compL
      (A.exists_isChangeOfVariables_coordChange k hPc hPD hPQ).choose_spec.choose_spec hp)

/-- **Chart data of Sobolev sections are transferred between charts.** If `P` lies in the overlap
of the domains of charts `j` and `i` (read in chart `i`) and has compact closure in the transfer
domain, and `Q ⊆ A.image j` contains the image of `P` under the chart transition, then the chart-`i`
components of an element of `W^{k,p}(V)` restricted to `P` are the transfer of its chart-`j`
components restricted to `Q`. -/
theorem restrictL_eq_transferL (hp : p ≠ ⊤) {w : A.sectionChartData.SobolevData μ p k}
    (hw : w ∈ A.sectionChartData.sobolevSections μ p k) {i j : Fin A.n} {P Q : Opens E}
    (hP : (P : Set E) ⊆ A.overlap j i) (hPc : IsCompact (closure (P : Set E)))
    (hPD : closure (P : Set E) ⊆ A.transferDomain i j) (hQ : Q ≤ A.image j)
    (hPQ : MapsTo ((A.chart i).symm ≫ₕ A.chart j) P Q) :
    (fun m ↦ Wkp.restrictL (SetLike.coe_subset_coe.1 (hP.trans (A.overlap_subset_image j i))) k
        (w i m)) =
      A.transferL μ p k hp i j hPc hPD hPQ fun l ↦ Wkp.restrictL hQ k (w j l) := by
  set h := (A.exists_isChangeOfVariables_coordChange k hPc hPD hPQ).choose_spec.choose_spec
  have hPi : P ≤ A.image i := SetLike.coe_subset_coe.1 (hP.trans (A.overlap_subset_image j i))
  funext m
  refine Wkp.ext k (Lp.ext ?_)
  have hcompat := ae_restrict_of_ae_restrict_of_subset hP
    ((SectionChartData.compatible_iff _ _ _ _).1
      (SectionChartData.compatible_of_mem (A.aeTransition_sectionChartData μ) hw j i))
  have htr : ∀ y ∈ (P : Set E), A.transition j i y = ((A.chart i).symm ≫ₕ A.chart j) y := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := A.mem_overlap.1 (hP hy)
    rw [A.transition_chart hx.2, OpenPartialHomeomorph.coe_trans, Function.comp_apply,
      (A.chart i).left_inv (A.dom_subset_chart_source i hx.2)]
  have hi := ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hPi)
    (A.sectionChartData.chartValueL_apply_ae μ p k i w)
  have hj : ∀ᵐ y ∂μ.restrict P,
      A.sectionChartData.chartValueL μ p k j w (((A.chart i).symm ≫ₕ A.chart j) y) =
        ∑ l, Wkp.value k (w j l) (((A.chart i).symm ≫ₕ A.chart j) y) • finBasis ℝ F l :=
    h.ae_comp (ae_restrict_of_ae_restrict_of_subset (SetLike.coe_subset_coe.2 hQ)
      (A.sectionChartData.chartValueL_apply_ae μ p k j w))
  have hres : ∀ᵐ y ∂μ.restrict P, ∀ l, Wkp.value k (Wkp.restrictL hQ k (w j l))
      (((A.chart i).symm ≫ₕ A.chart j) y) =
        Wkp.value k (w j l) (((A.chart i).symm ≫ₕ A.chart j) y) :=
    h.ae_comp (ae_all_iff.2 fun l ↦ Wkp.value_restrictL_ae hQ k (w j l))
  have hcomp : ∀ᵐ y ∂μ.restrict P, ∀ l,
      Wkp.value k (Wkp.compL h hp (Wkp.restrictL hQ k (w j l))) y =
        Wkp.value k (Wkp.restrictL hQ k (w j l)) (((A.chart i).symm ≫ₕ A.chart j) y) :=
    ae_all_iff.2 fun l ↦ Wkp.value_compL_ae h hp _
  have hop := Wkp.value_contDiffOnOperatorSMulL_ae (A.isOpen_transferDomain i j) hPc hPD k
    (finBasis ℝ F) (finBasis ℝ F) (A.contDiffOn_coordChangeL_transferDomain i j)
    (fun l ↦ Wkp.compL h hp (Wkp.restrictL hQ k (w j l))) m
  filter_upwards [Wkp.value_restrictL_ae hPi k (w i m), hcompat, hi, hj, hres, hcomp, hop,
    ae_restrict_mem P.isOpen.measurableSet] with y hy₁ hy₂ hy₃ hy₄ hy₅ hy₆ hy₇ hyP
  rw [A.sectionChartData_coordChange_of_mem (hP hyP),
    A.sectionChartData_transition_of_mem (hP hyP), htr y hyP] at hy₂
  have hval : Wkp.value k (w i m) y =
      (finBasis ℝ F).repr (A.sectionChartData.chartValueL μ p k i w y) m := by
    rw [hy₃, (finBasis ℝ F).repr_sum_self]
  simp only [transferL, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [show (ContinuousLinearMap.piMap fun _ ↦ Wkp.compL h hp)
      (fun l ↦ Wkp.restrictL hQ k (w j l)) =
        fun l ↦ Wkp.compL h hp (Wkp.restrictL hQ k (w j l)) from rfl]
  erw [hy₁, hval, hy₂, hy₄, hy₇]
  simp only [hy₆, hy₅, ContinuousLinearEquiv.coe_coe]

end FiniteBundleAtlas

/-! ### Rellich compactness -/

namespace SobolevSection

/-- **Rellich's theorem for Sobolev sections.** On a compact manifold without boundary, given by a
finite bundle atlas of a Hausdorff manifold, the inclusion `W^{k+1,p}(V) → W^{k,p}(V)` is a compact
operator for every order `k` and every `1 ≤ p < ∞`. -/
theorem isCompactOperator_lowerOrderL [T2Space M] (hp : p ≠ ⊤) :
    IsCompactOperator (A.sectionChartData.lowerOrderL μ p k) := by
  obtain ⟨P, Q, hP, hPc, hPD, hQc, hQ, hPQ, hcov⟩ := A.exists_transfer_cover
  have hPi (i j : Fin A.n) : P i j ≤ A.image i :=
    SetLike.coe_subset_coe.1 ((hP i j).trans (A.overlap_subset_image j i))
  have hQi (j : Fin A.n) : Q j ≤ A.image j :=
    SetLike.coe_subset_coe.1 (subset_closure.trans (hQ j))
  -- On each piece, the chart-`i` data are transferred from the chart-`j` data on `Q j`, which
  -- depend compactly on the section by local Rellich compactness.
  have hpiece (i j : Fin A.n) (m : Fin (finrank ℝ F)) :
      IsCompactOperator fun w : SobolevSection A μ p (k + 1) ↦
        Wkp.restrictL (hPi i j) k
          (Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m)) := by
    have hrel : IsCompactOperator fun w : SobolevSection A μ p (k + 1) ↦ fun l ↦
        Wkp.restrictL (hQi j) k
          (Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) j l)) :=
      IsCompactOperator.pi fun l ↦ by
        convert (Wkp.isCompactOperator_restrictL_lowerOrderL (hQc j) (hQ j) k).comp_clm
          ((ContinuousLinearMap.proj l).comp
            ((ContinuousLinearMap.proj j).comp
              (A.sectionChartData.sobolevSections μ p (k + 1)).subtypeL))
          using 1
        funext w
        simp only [Function.comp_apply, ContinuousLinearMap.coe_comp]
        rw [Wkp.lowerOrderL_apply]
        rfl
    convert hrel.clm_comp ((ContinuousLinearMap.proj m).comp
      (A.transferL μ p k hp i j (hPc i j) (hPD i j) (hPQ i j))) using 1
    funext w
    have e (i' : Fin A.n) (m' : Fin (finrank ℝ F)) :
        (A.sectionChartData.lowerOrderL μ p k w : A.sectionChartData.SobolevData μ p k) i' m' =
          Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i' m') :=
      SectionChartData.lowerOrderL_apply _ _ _ _ w i' m'
    exact (congrArg (Wkp.restrictL (hPi i j) k) (e i m).symm).trans
      ((congrFun (A.restrictL_eq_transferL μ p k hp (A.sectionChartData.lowerOrderL μ p k w).2
        (hP i j) (hPc i j) (hPD i j) (hQi j) (hPQ i j)) m).trans
        (congrArg (fun u ↦ A.transferL μ p k hp i j (hPc i j) (hPD i j) (hPQ i j) u m)
          (funext fun l ↦ congrArg (Wkp.restrictL (hQi j) k) (e j l))))
  -- Gluing the pieces gives compactness of the chart-`i` components.
  have hchart (i : Fin A.n) (m : Fin (finrank ℝ F)) :
      IsCompactOperator fun w : SobolevSection A μ p (k + 1) ↦
        Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m) := by
    let R := Wkp.restrictCompatibleEquiv (mu := μ) (p := p) (Omega := A.sectionChartData.image i)
      (hPi i) (hcov i) k
    have hfam : IsCompactOperator fun w : SobolevSection A μ p (k + 1) ↦
        R (Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m)) := by
      convert (IsCompactOperator.pi fun j ↦ hpiece i j m).codRestrict
        (fun w ↦ Wkp.restrictL_mem_compatibleFamilies (hPi i) k
          (Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m)))
        (Wkp.isClosed_compatibleFamilies _ k) using 1
      funext w
      exact Subtype.ext (funext fun j ↦ by
        rw [Set.val_codRestrict_apply]
        exact Wkp.restrictCompatibleEquiv_apply_coe _ _ _ _ j)
    convert hfam.clm_comp R.symm.toContinuousLinearMap using 1
    funext w
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]
  have hmem (w : SobolevSection A μ p (k + 1)) :
      (fun i m ↦ Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m)) ∈
        A.sectionChartData.sobolevSections μ p k := by
    convert (A.sectionChartData.lowerOrderL μ p k w).2 using 1
    funext i m
    rw [SectionChartData.lowerOrderL_apply]
  have key : ⇑(A.sectionChartData.lowerOrderL μ p k) = fun w : SobolevSection A μ p (k + 1) ↦
      (⟨fun i m ↦ Wkp.lowerOrder k ((w : A.sectionChartData.SobolevData μ p (k + 1)) i m),
        hmem w⟩ : A.sectionChartData.sobolevSections μ p k) :=
    funext fun w ↦ Subtype.ext <| funext fun i ↦ funext fun m ↦
      SectionChartData.lowerOrderL_apply A.sectionChartData μ p k w i m
  rw [key]
  exact (IsCompactOperator.pi fun (i : Fin A.sectionChartData.n) ↦
    IsCompactOperator.pi fun m ↦ hchart i m).codRestrict hmem
    (SectionChartData.isClosed_sobolevSections (A.aeTransition_sectionChartData μ))

/-- **Compact inclusion into `Lᵖ`.** The inclusion `W^{1,p}(V) → W^{0,p}(V)` of first-order Sobolev
sections into sections with `Lᵖ` chart data is compact for `1 ≤ p < ∞`. -/
theorem isCompactOperator_lowerOrderL_zero [T2Space M] (hp : p ≠ ⊤) :
    IsCompactOperator (A.sectionChartData.lowerOrderL μ p 0) :=
  isCompactOperator_lowerOrderL A μ p 0 hp

end SobolevSection

end Sobolev

end TauCeti
