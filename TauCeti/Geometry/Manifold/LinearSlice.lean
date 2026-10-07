/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Algebra.Module.Complement

/-!
# Manifold structures from linear slice charts

Ambient charts flattening a subset onto a fixed linear slice induce a manifold structure
on the subset with its original topology. If the ambient charts and their inverses are
`C^n`, the induced atlas and the inclusion into the ambient space are `C^n`.

The construction requires neither finite dimension nor completeness. It reuses
`IsSliceChart.subtypeChart`; the smooth-atlas argument follows the preferred-chart argument
in `TauCeti.Geometry.Lie.Subgroup.Manifold`, without its group translations.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Chapter 5.
-/

public section

namespace TauCeti

open Set Topology
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {s : Set E}
  (e : s → OpenPartialHomeomorph E (F × G))
  (he : ∀ x, IsSliceChart (e x) ((univ : Set F) ×ˢ ({0} : Set G)) s)

/-- The induced chart at a point of the subset. The base point supplies the fallback value
of the partial inverse outside the chart target, so no nonemptiness assumption is needed. -/
noncomputable def linearSliceChart (x : s) : OpenPartialHomeomorph s F :=
  letI : Nonempty s := ⟨x⟩
  (he x).subtypeChart

/-- The induced chart source is the part of the subset in the ambient source. -/
@[simp]
theorem linearSliceChart_source (x : s) :
    (linearSliceChart e he x).source = Subtype.val ⁻¹' (e x).source := by
  let : Nonempty s := ⟨x⟩
  unfold linearSliceChart
  apply IsSliceChart.subtypeChart_source

/-- The induced chart target is the zero-slice part of the ambient target. -/
@[simp]
theorem linearSliceChart_target (x : s) :
    (linearSliceChart e he x).target = (fun v : F ↦ (v, (0 : G))) ⁻¹' (e x).target := by
  let : Nonempty s := ⟨x⟩
  unfold linearSliceChart
  apply IsSliceChart.subtypeChart_target

/-- The induced chart reads the tangential coordinate of the ambient chart. -/
@[simp]
theorem linearSliceChart_apply (x y : s) :
    linearSliceChart e he x y = (e x y).1 := by
  let : Nonempty s := ⟨x⟩
  unfold linearSliceChart
  apply IsSliceChart.subtypeChart_apply

/-- On the target, the induced inverse is the ambient inverse evaluated on the zero slice. -/
@[simp]
theorem coe_linearSliceChart_symm_apply (x : s) {v : F}
    (hv : (v, (0 : G)) ∈ (e x).target) :
    ((linearSliceChart e he x).symm v : E) = (e x).symm (v, 0) := by
  let : Nonempty s := ⟨x⟩
  unfold linearSliceChart
  apply IsSliceChart.coe_subtypeChart_symm_apply
  exact hv

/-- A covering family of ambient linear-slice charts gives a charted-space structure on the
subset, with its original topology and atlas exactly the induced charts. -/
@[instance_reducible]
noncomputable def linearSliceChartedSpace (hcover : ∀ x : s, (x : E) ∈ (e x).source) :
    ChartedSpace F s where
  atlas := range (linearSliceChart e he)
  chartAt := linearSliceChart e he
  mem_chart_source x := by rw [linearSliceChart_source]; exact hcover x
  chart_mem_atlas := mem_range_self

/-- The atlas consists exactly of the induced linear-slice charts. -/
@[simp]
theorem linearSliceChartedSpace_atlas (hcover : ∀ x : s, (x : E) ∈ (e x).source) :
    @atlas F _ s _ (linearSliceChartedSpace e he hcover) = range (linearSliceChart e he) := (rfl)

/-- The chosen chart at a point is its induced linear-slice chart. -/
@[simp]
theorem linearSliceChartedSpace_chartAt (hcover : ∀ x : s, (x : E) ∈ (e x).source) (x : s) :
    @chartAt F _ s _ (linearSliceChartedSpace e he hcover) x = linearSliceChart e he x := (rfl)

variable {n : ℕ∞ω}
  (hsmooth : ∀ x, ∀ z ∈ (e x).source, ContDiffAt 𝕜 n (e x) z)
  (hinv : ∀ x, ∀ z ∈ (e x).target, ContDiffAt 𝕜 n (e x).symm z)

include hsmooth hinv

/-- Transitions between induced charts insert the zero transverse coordinate, apply the
ambient inverse and the other ambient chart, and read the tangential coordinate. -/
theorem contDiffOn_linearSliceChart_transition (x y : s) :
    ContDiffOn 𝕜 n ((linearSliceChart e he x).symm.trans (linearSliceChart e he y))
      ((linearSliceChart e he x).symm.trans (linearSliceChart e he y)).source := by
  intro v hv
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hv
  have hvt : (v, (0 : G)) ∈ (e x).target := by
    simpa only [linearSliceChart_target, mem_preimage] using hv.1
  have hzs : (e x).symm (v, 0) ∈ (e y).source := by
    simpa only [linearSliceChart_source, mem_preimage,
      coe_linearSliceChart_symm_apply e he x hvt] using hv.2
  have h := ((hsmooth y _ hzs).comp v
    ((hinv x _ hvt).comp v (contDiff_id.prodMk contDiff_const).contDiffAt)).fst
  exact h.contDiffWithinAt.congr_of_mem (fun w hw ↦ by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw
    have hwt : (w, (0 : G)) ∈ (e x).target := by
      simpa only [linearSliceChart_target, mem_preimage] using hw.1
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, linearSliceChart_apply,
      coe_linearSliceChart_symm_apply e he x hwt, OpenPartialHomeomorph.coe_toPartialEquiv,
      id_eq]) hv

/-- Smooth ambient slice charts induce a `C^n` manifold structure on the subset. -/
theorem isManifold_linearSliceChartedSpace (hcover : ∀ x : s, (x : E) ∈ (e x).source) :
    letI := linearSliceChartedSpace e he hcover
    IsManifold 𝓘(𝕜, F) n s := by
  let := linearSliceChartedSpace e he hcover
  refine isManifold_of_contDiffOn _ _ _ ?_
  rw [linearSliceChartedSpace_atlas]
  rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
  simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id,
    inter_univ, preimage_id, Function.comp_id, Function.id_comp] using
    contDiffOn_linearSliceChart_transition e he hsmooth hinv x y

omit hsmooth in
/-- The inclusion of a subset equipped with its linear-slice atlas is `C^n` when the ambient
inverse charts are `C^n`. -/
theorem contMDiff_subtypeVal_linearSliceChartedSpace
    (hcover : ∀ x : s, (x : E) ∈ (e x).source) :
    letI := linearSliceChartedSpace e he hcover
    ContMDiff 𝓘(𝕜, F) 𝓘(𝕜, E) n (Subtype.val : s → E) := by
  let := linearSliceChartedSpace e he hcover
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  have hx : linearSliceChart e he x x ∈ (linearSliceChart e he x).target :=
    (linearSliceChart e he x).map_source (by rw [linearSliceChart_source]; exact hcover x)
  have hxt : (linearSliceChart e he x x, (0 : G)) ∈ (e x).target := by
    simpa only [linearSliceChart_target, mem_preimage] using hx
  have hd := (hinv x _ hxt).comp (linearSliceChart e he x x)
    (contDiff_id.prodMk contDiff_const).contDiffAt
  have hd' : ContDiffAt 𝕜 n (Subtype.val ∘ (linearSliceChart e he x).symm)
      (linearSliceChart e he x x) := by
    apply hd.congr_of_eventuallyEq
    filter_upwards [(linearSliceChart e he x).open_target.mem_nhds hx] with v hv
    have hvt : (v, (0 : G)) ∈ (e x).target := by
      simpa only [linearSliceChart_target, mem_preimage] using hv
    exact coe_linearSliceChart_symm_apply e he x hvt
  -- Extended charts for the self model only insert identity maps.
  convert hd'.contDiffWithinAt using 1 <;>
    simp only [PartialEquiv.refl_coe, Function.id_comp, extChartAt,
      linearSliceChartedSpace_chartAt, chartAt_self_eq, OpenPartialHomeomorph.extend,
      OpenPartialHomeomorph.refl_partialEquiv, OpenPartialHomeomorph.coe_toPartialEquiv,
      PartialEquiv.coe_trans, PartialEquiv.coe_trans_symm, ModelWithCorners.toPartialEquiv_coe,
      ModelWithCorners.toPartialEquiv_coe_symm, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, Function.comp_id, Function.id_comp]
  rfl

omit e he hsmooth hinv in
/-- A subset locally flattened onto a complemented linear subspace is a `C^n` manifold
modelled on that subspace, and its inclusion into the ambient space is `C^n`. -/
theorem exists_isManifold_of_linearSubspaceCharts {L N : Submodule 𝕜 E}
    (hcompl : Submodule.IsTopCompl L N)
    (hcharts : ∀ y : s, ∃ q : OpenPartialHomeomorph E E, (y : E) ∈ q.source ∧
      (∀ z ∈ q.source, ContDiffAt 𝕜 n q z) ∧
      (∀ z ∈ q.target, ContDiffAt 𝕜 n q.symm z) ∧
      ∀ z ∈ q.source, z ∈ s ↔ q z ∈ L) :
    ∃ C : ChartedSpace L s, letI := C
      IsManifold 𝓘(𝕜, L) n s ∧ ContMDiff 𝓘(𝕜, L) 𝓘(𝕜, E) n (Subtype.val : s → E) := by
  classical
  choose q hq hqs hqi hqmem using hcharts
  let A := (L.prodEquivOfIsTopCompl N hcompl).symm
  let e (y : s) := (q y).transHomeomorph A.toHomeomorph
  have he (y : s) : IsSliceChart (e y) ((univ : Set L) ×ˢ ({0} : Set N)) s := by
    refine isSliceChart_iff.2 fun z hz ↦ ?_
    rw [OpenPartialHomeomorph.transHomeomorph_source] at hz
    rw [hqmem y z hz]
    simp only [e, OpenPartialHomeomorph.transHomeomorph_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply, mem_prod, mem_univ,
      mem_singleton_iff, true_and, A,
      Submodule.coe_symm_prodEquivOfIsTopCompl]
    exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero L N hcompl.isCompl).symm
  have hcover (y : s) : (y : E) ∈ (e y).source := by
    simpa only [e, OpenPartialHomeomorph.transHomeomorph_source] using hq y
  have hs (y : s) (z : E) (hz : z ∈ (e y).source) : ContDiffAt 𝕜 n (e y) z := by
    rw [OpenPartialHomeomorph.transHomeomorph_source] at hz
    simpa only [e, OpenPartialHomeomorph.transHomeomorph_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_def] using
      A.contDiff.contDiffAt.comp z (hqs y z hz)
  have hi (y : s) (z : L × N) (hz : z ∈ (e y).target) :
      ContDiffAt 𝕜 n (e y).symm z := by
    have hzt : A.symm z ∈ (q y).target := by
      simpa only [e, OpenPartialHomeomorph.transHomeomorph_target, mem_preimage,
        ContinuousLinearEquiv.coe_symm_toHomeomorph] using hz
    simpa only [e, OpenPartialHomeomorph.transHomeomorph_symm_apply,
      ContinuousLinearEquiv.coe_symm_toHomeomorph, Function.comp_def] using
      (hqi y _ hzt).comp z A.symm.contDiff.contDiffAt
  exact ⟨linearSliceChartedSpace e he hcover,
    isManifold_linearSliceChartedSpace e he hs hi hcover,
    contMDiff_subtypeVal_linearSliceChartedSpace e he hi hcover⟩

end TauCeti
