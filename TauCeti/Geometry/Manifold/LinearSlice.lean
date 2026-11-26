/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.LocallyFlat.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Topology.Algebra.Module.Complement
public import Mathlib.Geometry.Manifold.SmoothEmbedding

import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import TauCeti.Topology.Algebra.Module.SubspaceExchange

/-!
# Manifold structures from linear slice charts

Ambient charts flattening a subset of a manifold onto a fixed linear slice induce a manifold
structure on the subset with its original topology. If the ambient charts and their inverses are
`C^n`, the induced atlas and the inclusion into the ambient manifold are `C^n`. A subset of a
normed space is the case of the space modelled on itself. For a boundaryless ambient manifold,
a linear identification of the product coordinates with the model vector space makes the inclusion
a smooth embedding, with the transverse model as its immersion complement.

The existence statements `TauCeti.exists_isSmoothEmbedding_of_linearSubspaceCharts` and
`TauCeti.exists_isSmoothEmbedding_of_finrankSubspaceCharts` record this embedding for a subset of
a boundaryless manifold flattened near each of its points by smooth charts with values in the model
vector space.

The construction requires neither finite dimension nor completeness. It reuses
`IsSliceChart.subtypeChart`; the smooth-atlas argument follows the preferred-chart argument
in `TauCeti.Geometry.Lie.Subgroup.Manifold`, without its group translations. The variant
`exists_isManifold_of_finrankSubspaceCharts`, in which the flattening subspace may change from
point to point and only its dimension is fixed, assumes a finite-dimensional model over a complete
field: there linear isomorphisms are continuous and every subspace has a closed complement.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Chapter 5.
-/

public section

namespace TauCeti

open Set Topology
open scoped ContDiff Manifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {s : Set M}

/-- The derivative of a `C^n` chart `q` with values in the model vector space and with `C^n`
inverse, for `n ≠ 0`, is invertible at each point of its source, so the preimage under it of a
subspace `V` of the model space has the dimension of `V`. -/
theorem _root_.OpenPartialHomeomorph.finrank_comap_mfderiv {n : ℕ∞ω} (hn : n ≠ 0)
    {q : OpenPartialHomeomorph M E} (hq : ∀ z ∈ q.source, ContMDiffAt I 𝓘(𝕜, E) n q z)
    (hqs : ∀ z ∈ q.target, ContMDiffAt 𝓘(𝕜, E) I n q.symm z) (V : Submodule 𝕜 E) {x : M}
    (hx : x ∈ q.source) :
    Module.finrank 𝕜 (V.comap (mfderiv I 𝓘(𝕜, E) q x).toLinearMap) = Module.finrank 𝕜 V := by
  have he : q.MDifferentiable I 𝓘(𝕜, E) :=
    ⟨fun z hz ↦ ((hq z hz).mdifferentiableAt hn).mdifferentiableWithinAt,
      fun z hz ↦ ((hqs z hz).mdifferentiableAt hn).mdifferentiableWithinAt⟩
  let e : TangentSpace I x ≃ₗ[𝕜] E := (he.mfderiv hx).toLinearEquiv
  have key : Module.finrank 𝕜 (V.comap (e : TangentSpace I x →ₗ[𝕜] E)) = Module.finrank 𝕜 V := by
    rw [Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  -- The underlying linear map of `e` is the derivative of `q` at `x` by definition, but its
  -- codomain is `E` rather than the tangent space `TangentSpace 𝓘(𝕜, E) (q x)`, which `rw` does
  -- not see through, so the two statements are matched up to definitional unfolding.
  exact key

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  (e : s → OpenPartialHomeomorph M (F × G))
  (he : ∀ x, IsSliceChart (e x) ((univ : Set F) ×ˢ ({0} : Set G)) s)
  {n : ℕ∞ω}
  (hsmooth : ∀ x, ∀ z ∈ (e x).source, ContMDiffAt I 𝓘(𝕜, F × G) n (e x) z)
  (hinv : ∀ x, ∀ z ∈ (e x).target, ContMDiffAt 𝓘(𝕜, F × G) I n (e x).symm z)

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
  have hmk : ContMDiffAt 𝓘(𝕜, F) 𝓘(𝕜, F × G) n (fun w : F ↦ (w, (0 : G))) v :=
    (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt
  have h := contMDiffAt_iff_contDiffAt.1 (contDiff_fst.contMDiff.contMDiffAt.comp v
    ((hsmooth y _ hzs).comp v ((hinv x _ hvt).comp v hmk)))
  exact h.contDiffWithinAt.congr_of_mem (fun w hw ↦ by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hw
    have hwt : (w, (0 : G)) ∈ (e x).target := by
      simpa only [linearSliceChart_target, mem_preimage] using hw.1
    simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, linearSliceChart_apply,
      coe_linearSliceChart_symm_apply e he x hwt, OpenPartialHomeomorph.coe_toPartialEquiv]) hv

/-- Smooth ambient slice charts induce a `C^n` manifold structure on the subset. -/
theorem isManifold_linearSliceChartedSpace (hcover : ∀ x : s, (x : M) ∈ (e x).source) :
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
    (hcover : ∀ x : s, (x : M) ∈ (e x).source) :
    letI := linearSliceChartedSpace e he hcover
    ContMDiff 𝓘(𝕜, F) I n (Subtype.val : s → M) := by
  let := linearSliceChartedSpace e he hcover
  intro x
  have hxs : x ∈ (linearSliceChart e he x).source := by
    rw [linearSliceChart_source]; exact hcover x
  have hxt : (linearSliceChart e he x x, (0 : G)) ∈ (e x).target := by
    simpa only [linearSliceChart_target, mem_preimage] using
      (linearSliceChart e he x).map_source hxs
  have hmk : ContMDiffAt 𝓘(𝕜, F) 𝓘(𝕜, F × G) n (fun w : F ↦ (w, (0 : G)))
      (linearSliceChart e he x x) :=
    (contDiff_id.prodMk contDiff_const).contMDiff.contMDiffAt
  have hsymm : ContMDiffAt 𝓘(𝕜, F) I n ((e x).symm ∘ fun w : F ↦ (w, (0 : G)))
      (linearSliceChart e he x x) :=
    ContMDiffAt.comp (linearSliceChart e he x x) (hinv x _ hxt) hmk
  have hd : ContMDiffAt 𝓘(𝕜, F) I n (fun y : s ↦ (e x).symm (linearSliceChart e he x y, 0)) x :=
    hsymm.comp x <| by
      -- The preferred chart is smooth at its centre, with no compatibility condition.
      simpa only [extChartAt_coe, linearSliceChartedSpace_chartAt, modelWithCornersSelf_coe,
        Function.id_comp] using contMDiffAt_extChartAt (I := 𝓘(𝕜, F)) (n := n) (x := x)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [(linearSliceChart e he x).open_source.mem_nhds hxs] with y hy
  rw [linearSliceChart_source] at hy
  rw [linearSliceChart_apply, (he x).mk_fst_zero_eq hy y.property, (e x).left_inv hy]

omit hsmooth hinv in
/-- For smooth linear-slice charts of a boundaryless manifold, the inclusion is an immersion with
the transverse model as complement. The linear equivalence identifies the product coordinates with
the model vector space `E`, which the model `I` identifies with the model space `H`. -/
theorem isImmersionOfComplement_subtypeVal_linearSliceChartedSpace
    (A : s → (F × G) ≃L[𝕜] E) [I.Boundaryless] [IsManifold I n M]
    (hs : ∀ x, ContMDiffOn I 𝓘(𝕜, F × G) n (e x) (e x).source)
    (hi : ∀ x, ContMDiffOn 𝓘(𝕜, F × G) I n (e x).symm (e x).target)
    (hcover : ∀ x : s, (x : M) ∈ (e x).source) :
    letI := linearSliceChartedSpace e he hcover
    Manifold.IsImmersionOfComplement G 𝓘(𝕜, F) I n (Subtype.val : s → M) := by
  let := linearSliceChartedSpace e he hcover
  have := isManifold_linearSliceChartedSpace e he
    (fun x z hz ↦ (hs x).contMDiffAt ((e x).open_source.mem_nhds hz))
    (fun x z hz ↦ (hi x).contMDiffAt ((e x).open_target.mem_nhds hz)) hcover
  have hI : ContMDiff 𝓘(𝕜, E) I n I.symm :=
    contMDiffOn_univ.1 (I.range_eq_univ ▸ I.contMDiffOn_symm)
  intro x
  -- The ambient chart reads the slice chart in `E` through `A x`, then in `H` through `I.symm`.
  let c := (e x).transHomeomorph ((A x).toHomeomorph.trans I.toHomeomorph.symm)
  have hc : c ∈ IsManifold.maximalAtlas I n M := by
    apply OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn
    · exact hI.comp_contMDiffOn ((A x).contDiff.contMDiff.comp_contMDiffOn (hs x))
    · refine (hi x).comp ((A x).symm.contDiff.contMDiff.comp (I.contMDiff (n := n))).contMDiffOn
        fun z hz ↦ ?_
      simpa [c] using hz
  refine Manifold.IsImmersionAtOfComplement.mk_of_charts (A x)
    (linearSliceChart e he x) c ?_ ?_ ?_ hc ?_ ?_
  · simpa only [linearSliceChart_source, Set.mem_preimage] using hcover x
  · exact hcover x
  · rw [← linearSliceChartedSpace_chartAt e he hcover x]
    exact IsManifold.chart_mem_maximalAtlas (I := 𝓘(𝕜, F)) x
  · simpa only [linearSliceChart_source, c, OpenPartialHomeomorph.transHomeomorph_source] using
      (Set.Subset.rfl : Subtype.val ⁻¹' (e x).source ⊆ Subtype.val ⁻¹' (e x).source)
  · intro v hv
    have hv' : (v, (0 : G)) ∈ (e x).target := by
      simpa only [OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe,
        modelWithCornersSelf_coe_symm, Set.preimage_id,
        Set.range_id, Set.inter_univ, linearSliceChart_target, Set.mem_preimage] using hv
    -- The domain model is a self-model, whose extension leaves the chart formula intact.
    simp only [Function.comp_apply, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_coe_symm,
      modelWithCornersSelf_coe_symm, id_eq, OpenPartialHomeomorph.transHomeomorph_apply,
      Homeomorph.trans_apply, ContinuousLinearEquiv.coe_toHomeomorph, c,
      coe_linearSliceChart_symm_apply e he x hv', (e x).right_inv hv']
    exact I.toHomeomorph.apply_symm_apply _

omit hsmooth hinv in
/-- The inclusion equipped with its smooth linear-slice atlas into a boundaryless manifold is a
smooth embedding. -/
theorem isSmoothEmbedding_subtypeVal_linearSliceChartedSpace
    (A : s → (F × G) ≃L[𝕜] E) [I.Boundaryless] [IsManifold I n M]
    (hs : ∀ x, ContMDiffOn I 𝓘(𝕜, F × G) n (e x) (e x).source)
    (hi : ∀ x, ContMDiffOn 𝓘(𝕜, F × G) I n (e x).symm (e x).target)
    (hcover : ∀ x : s, (x : M) ∈ (e x).source) :
    letI := linearSliceChartedSpace e he hcover
    Manifold.IsSmoothEmbedding 𝓘(𝕜, F) I n (Subtype.val : s → M) := by
  let := linearSliceChartedSpace e he hcover
  exact ⟨(isImmersionOfComplement_subtypeVal_linearSliceChartedSpace
    e he A hs hi hcover).isImmersion,
    IsEmbedding.subtypeVal⟩

omit e he hsmooth hinv in
/-- Ambient charts flattening `s` onto a complemented subspace `L` of the model, read in the
product coordinates `L × N`, are linear-slice charts onto `L × {0}`. -/
private theorem exists_linearSliceCharts_of_linearSubspaceCharts {L N : Submodule 𝕜 E}
    (hcompl : Submodule.IsTopCompl L N)
    (hcharts : ∀ y : s, ∃ q : OpenPartialHomeomorph M E, (y : M) ∈ q.source ∧
      (∀ z ∈ q.source, ContMDiffAt I 𝓘(𝕜, E) n q z) ∧
      (∀ z ∈ q.target, ContMDiffAt 𝓘(𝕜, E) I n q.symm z) ∧
      ∀ z ∈ q.source, z ∈ s ↔ q z ∈ L) :
    ∃ e : s → OpenPartialHomeomorph M (L × N),
      (∀ y, IsSliceChart (e y) ((univ : Set L) ×ˢ ({0} : Set N)) s) ∧
      (∀ y : s, (y : M) ∈ (e y).source) ∧
      (∀ y, ∀ z ∈ (e y).source, ContMDiffAt I 𝓘(𝕜, L × N) n (e y) z) ∧
      ∀ y, ∀ z ∈ (e y).target, ContMDiffAt 𝓘(𝕜, L × N) I n (e y).symm z := by
  classical
  choose q hq hqs hqi hqmem using hcharts
  let A := (L.prodEquivOfIsTopCompl N hcompl).symm
  refine ⟨fun y ↦ (q y).transHomeomorph A.toHomeomorph, fun y ↦ ?_, fun y ↦ ?_,
    fun y z hz ↦ ?_, fun y z hz ↦ ?_⟩
  · refine isSliceChart_iff.2 fun z hz ↦ ?_
    rw [OpenPartialHomeomorph.transHomeomorph_source] at hz
    rw [hqmem y z hz]
    simp only [OpenPartialHomeomorph.transHomeomorph_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_apply, mem_prod, mem_univ,
      mem_singleton_iff, true_and, A,
      Submodule.coe_symm_prodEquivOfIsTopCompl]
    exact (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero L N hcompl.isCompl).symm
  · simpa only [OpenPartialHomeomorph.transHomeomorph_source] using hq y
  · rw [OpenPartialHomeomorph.transHomeomorph_source] at hz
    simpa only [OpenPartialHomeomorph.transHomeomorph_apply,
      ContinuousLinearEquiv.coe_toHomeomorph, Function.comp_def] using
      A.contDiff.contMDiff.contMDiffAt.comp z (hqs y z hz)
  · have hzt : A.symm z ∈ (q y).target := by
      simpa only [OpenPartialHomeomorph.transHomeomorph_target, mem_preimage,
        ContinuousLinearEquiv.coe_symm_toHomeomorph] using hz
    simpa only [OpenPartialHomeomorph.transHomeomorph_symm_apply,
      ContinuousLinearEquiv.coe_symm_toHomeomorph, Function.comp_def] using
      (hqi y _ hzt).comp z A.symm.contDiff.contMDiff.contMDiffAt

omit e he hsmooth hinv in
/-- A subset of a manifold locally flattened onto a complemented linear subspace of the model is a
`C^n` manifold modelled on that subspace, and its inclusion into the ambient manifold is `C^n`. -/
theorem exists_isManifold_of_linearSubspaceCharts {L N : Submodule 𝕜 E}
    (hcompl : Submodule.IsTopCompl L N)
    (hcharts : ∀ y : s, ∃ q : OpenPartialHomeomorph M E, (y : M) ∈ q.source ∧
      (∀ z ∈ q.source, ContMDiffAt I 𝓘(𝕜, E) n q z) ∧
      (∀ z ∈ q.target, ContMDiffAt 𝓘(𝕜, E) I n q.symm z) ∧
      ∀ z ∈ q.source, z ∈ s ↔ q z ∈ L) :
    ∃ C : ChartedSpace L s, letI := C
      IsManifold 𝓘(𝕜, L) n s ∧ ContMDiff 𝓘(𝕜, L) I n (Subtype.val : s → M) := by
  obtain ⟨e, he, hcover, hs, hi⟩ :=
    exists_linearSliceCharts_of_linearSubspaceCharts hcompl hcharts
  exact ⟨linearSliceChartedSpace e he hcover,
    isManifold_linearSliceChartedSpace e he hs hi hcover,
    contMDiff_subtypeVal_linearSliceChartedSpace e he hi hcover⟩

omit e he hsmooth hinv in
/-- Charts of a finite-dimensional model flattening `s` near each of its points onto some subspace
of dimension `d` can be replaced by charts flattening `s` onto any fixed subspace `L` of dimension
`d`, which has a complement. -/
private theorem exists_linearSubspaceCharts_of_finrankSubspaceCharts [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] {L : Submodule 𝕜 E}
    (hcharts : ∀ y ∈ s, ∃ (q : OpenPartialHomeomorph M E) (V : Submodule 𝕜 E), y ∈ q.source ∧
      (∀ z ∈ q.source, ContMDiffAt I 𝓘(𝕜, E) n q z) ∧
      (∀ z ∈ q.target, ContMDiffAt 𝓘(𝕜, E) I n q.symm z) ∧
      (∀ z ∈ q.source, z ∈ s ↔ q z ∈ V) ∧ Module.finrank 𝕜 V = Module.finrank 𝕜 L) :
    ∃ N : Submodule 𝕜 E, Submodule.IsTopCompl L N ∧
      ∀ y : s, ∃ q : OpenPartialHomeomorph M E, (y : M) ∈ q.source ∧
        (∀ z ∈ q.source, ContMDiffAt I 𝓘(𝕜, E) n q z) ∧
        (∀ z ∈ q.target, ContMDiffAt 𝓘(𝕜, E) I n q.symm z) ∧
        ∀ z ∈ q.source, z ∈ s ↔ q z ∈ L := by
  obtain ⟨N, hN⟩ := L.exists_isCompl
  refine ⟨N, Submodule.IsCompl.isTopCompl_of_isClosed_of_finiteDimensional hN
    L.isClosed_of_finiteDimensional, fun y ↦ ?_⟩
  obtain ⟨q, V, hy, hq, hqs, hmem, hdim⟩ := hcharts y y.property
  obtain ⟨Φ, hΦ⟩ := V.exists_continuousLinearEquiv_mem_iff L hdim
  refine ⟨q.transHomeomorph Φ.toHomeomorph, by simpa using hy, fun z hz ↦ ?_, fun z hz ↦ ?_,
    fun z hz ↦ ?_⟩
  · rw [OpenPartialHomeomorph.transHomeomorph_source] at hz
    exact Φ.contDiff.contMDiff.contMDiffAt.comp z (hq z hz)
  · have hz' : Φ.symm z ∈ q.target := by simpa using hz
    exact (hqs _ hz').comp z Φ.symm.contDiff.contMDiff.contMDiffAt
  · rw [OpenPartialHomeomorph.transHomeomorph_source] at hz
    simpa [hΦ] using hmem z hz

omit e he hsmooth hinv in
/-- A subset of a manifold modelled on a finite-dimensional space that is flattened near each of its
points by a `C^n` chart onto some subspace of dimension `d` of the model is a `C^n` manifold
modelled on any subspace `L` of dimension `d`, and its inclusion is `C^n`. -/
theorem exists_isManifold_of_finrankSubspaceCharts [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E]
    {L : Submodule 𝕜 E}
    (hcharts : ∀ y ∈ s, ∃ (q : OpenPartialHomeomorph M E) (V : Submodule 𝕜 E), y ∈ q.source ∧
      (∀ z ∈ q.source, ContMDiffAt I 𝓘(𝕜, E) n q z) ∧
      (∀ z ∈ q.target, ContMDiffAt 𝓘(𝕜, E) I n q.symm z) ∧
      (∀ z ∈ q.source, z ∈ s ↔ q z ∈ V) ∧ Module.finrank 𝕜 V = Module.finrank 𝕜 L) :
    ∃ C : ChartedSpace L s, letI := C
      IsManifold 𝓘(𝕜, L) n s ∧ ContMDiff 𝓘(𝕜, L) I n (Subtype.val : s → M) := by
  obtain ⟨N, hLN, hcharts'⟩ := exists_linearSubspaceCharts_of_finrankSubspaceCharts hcharts
  exact exists_isManifold_of_linearSubspaceCharts hLN hcharts'

/-! ### Smooth embeddings into a boundaryless manifold -/

section Embedding

variable [I.Boundaryless] [IsManifold I n M]

omit e he hsmooth hinv in
/-- A subset of a boundaryless manifold, locally flattened onto a complemented linear subspace `L`
of the model vector space `E` by `C^n` charts with values in `E`, is a `C^n` manifold modelled on
`L`, and its inclusion into the ambient manifold is a `C^n` embedding. The atlas of the ambient
manifold takes values in its model space `H`. -/
theorem exists_isSmoothEmbedding_of_linearSubspaceCharts {L N : Submodule 𝕜 E}
    (hcompl : Submodule.IsTopCompl L N)
    (hcharts : ∀ y : s, ∃ q : OpenPartialHomeomorph M E, (y : M) ∈ q.source ∧
      (∀ z ∈ q.source, ContMDiffAt I 𝓘(𝕜, E) n q z) ∧
      (∀ z ∈ q.target, ContMDiffAt 𝓘(𝕜, E) I n q.symm z) ∧
      ∀ z ∈ q.source, z ∈ s ↔ q z ∈ L) :
    ∃ C : ChartedSpace L s, letI := C
      IsManifold 𝓘(𝕜, L) n s ∧
        Manifold.IsSmoothEmbedding 𝓘(𝕜, L) I n (Subtype.val : s → M) := by
  obtain ⟨e, he, hcover, hs, hi⟩ :=
    exists_linearSliceCharts_of_linearSubspaceCharts hcompl hcharts
  have hs' (y : s) : ContMDiffOn I 𝓘(𝕜, L × N) n (e y) (e y).source :=
    fun z hz ↦ (hs y z hz).contMDiffWithinAt
  have hi' (y : s) : ContMDiffOn 𝓘(𝕜, L × N) I n (e y).symm (e y).target :=
    fun z hz ↦ (hi y z hz).contMDiffWithinAt
  exact ⟨linearSliceChartedSpace e he hcover,
    isManifold_linearSliceChartedSpace e he hs hi hcover,
    isSmoothEmbedding_subtypeVal_linearSliceChartedSpace e he
      (fun _ ↦ L.prodEquivOfIsTopCompl N hcompl) hs' hi' hcover⟩

omit e he hsmooth hinv in
/-- A subset of a boundaryless manifold modelled on a finite-dimensional vector space `E`, flattened
near each of its points by a `C^n` chart with values in `E` onto some subspace of dimension `d` of
`E`, is a `C^n` manifold modelled on any subspace `L` of dimension `d`, and its inclusion is a
`C^n` embedding. The atlas of the ambient manifold takes values in its model space `H`, while each
flattening chart takes values in `E`. -/
theorem exists_isSmoothEmbedding_of_finrankSubspaceCharts [CompleteSpace 𝕜]
    [FiniteDimensional 𝕜 E] {L : Submodule 𝕜 E}
    (hcharts : ∀ y ∈ s, ∃ (q : OpenPartialHomeomorph M E) (V : Submodule 𝕜 E), y ∈ q.source ∧
      (∀ z ∈ q.source, ContMDiffAt I 𝓘(𝕜, E) n q z) ∧
      (∀ z ∈ q.target, ContMDiffAt 𝓘(𝕜, E) I n q.symm z) ∧
      (∀ z ∈ q.source, z ∈ s ↔ q z ∈ V) ∧ Module.finrank 𝕜 V = Module.finrank 𝕜 L) :
    ∃ C : ChartedSpace L s, letI := C
      IsManifold 𝓘(𝕜, L) n s ∧
        Manifold.IsSmoothEmbedding 𝓘(𝕜, L) I n (Subtype.val : s → M) := by
  obtain ⟨N, hLN, hcharts'⟩ := exists_linearSubspaceCharts_of_finrankSubspaceCharts hcharts
  exact exists_isSmoothEmbedding_of_linearSubspaceCharts hLN hcharts'

end Embedding

end TauCeti
