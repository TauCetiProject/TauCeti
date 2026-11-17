/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.Tangent
public import Mathlib.Topology.VectorBundle.Hom
public import TauCeti.Analysis.Calculus.Jet.FirstOrder
public import TauCeti.Geometry.Manifold.ExtChartAt
public import TauCeti.Topology.VectorBundle.Trivialization
import TauCeti.Analysis.Calculus.FDeriv.ContinuousLinearMap

/-!
# The first-jet bundle of a vector bundle

For a `C^1` vector bundle `V → M` with model fibre `F` over a `C^1` manifold modelled on `E`, the
first-jet bundle `J¹V` records the value and the first derivative of local sections. We construct
it as a vector bundle with fibre `F × (E →L[𝕜] F)`. Over the domain of the preferred chart `φᵢ`
of `M` and the preferred trivialization `eᵢ` of `V` at a point `i`, a first jet is the value and
the chart derivative of a local representative `z ↦ eᵢ (s (φᵢ⁻¹ z))` of a section `s`. Changing
from `i` to `j` transforms these by `ContinuousLinearMap.firstJetPullback`: the value by the
coordinate change `g` of `V`, the derivative by the product rule for `g` and the chain rule for the
change of charts.

## Main definitions and results

* `TauCeti.FirstJetBundle.coordChange`: the first-jet coordinate changes. They satisfy the identity
  and cocycle laws (`TauCeti.FirstJetBundle.coordChange_self_apply`,
  `TauCeti.FirstJetBundle.coordChange_comp_apply`), the latter by the product and chain rules
  `TauCeti.FirstJetBundle.fderivWithin_fiberCoordChange_trans`, and they are `C^n` when `V` and `M`
  are `C^(n+1)` (`TauCeti.FirstJetBundle.contMDiffOn_coordChange`).
* `TauCeti.firstJetBundleCore` and `TauCeti.FirstJetBundle`: the vector bundle core and the
  first-jet bundle itself, a `C^n` vector bundle when `V` and `M` are `C^(n+1)`
  (`TauCeti.FirstJetBundle.contMDiffVectorBundle`).
* `TauCeti.FirstJetBundle.localRep`: the local representative of a section in a chart and
  trivialization. Local representatives in two charts are related by the coordinate change of `V`
  and the change of charts (`TauCeti.FirstJetBundle.localRep_eventuallyEq_fiberCoordChange`).
* `TauCeti.FirstJetBundle.jet`: the first jet `j¹s(x)` of a section. For a section differentiable
  at the point, in every chart it is the value and the chart derivative of the local
  representative (`TauCeti.FirstJetBundle.trivializationAt_jet`), and it is a `C^n` section of
  `J¹V` for a `C^(n+1)` section `s` (`TauCeti.FirstJetBundle.contMDiff_jet`).
  For the trivial bundle over a model space it is `(s x, fderiv 𝕜 s x)`.
* `TauCeti.FirstJetBundle.jet_eq_zero_iff`,
  `TauCeti.FirstJetBundle.jet_eq_zero_iff_hasFDerivWithinAt`,
  `TauCeti.FirstJetBundle.jet_eq_zero_iff_of_mem_baseSet`: characterization and chart independence
  of vanishing first jets.
* `TauCeti.FirstJetBundle.hasFDerivWithinAt_localRep_congr_chart_of_eq_zero`,
  `TauCeti.FirstJetBundle.hasFDerivWithinAt_localRep_clm_apply_of_eq_zero`, and
  `TauCeti.FirstJetBundle.hasFDerivWithinAt_localRep_smul_of_eq_zero`: at a zero of a section `s`,
  changing charts, applying a continuous Hom-bundle section `A`, and multiplying by a continuous
  scalar function `f` all act tensorially on the derivative of the local representative; in
  particular, they preserve vanishing first jets (`TauCeti.FirstJetBundle.jet_clm_apply_eq_zero`,
  `TauCeti.FirstJetBundle.jet_smul_eq_zero`).
* `TauCeti.FirstJetBundle.value` and `TauCeti.FirstJetBundle.ofDeriv`: the fibres of the projection
  `J¹V → V` and of the inclusion `Hom(TM, V) → J¹V` of continuous linear maps (for
  finite-dimensional fibres, `Hom(TM, V) = T*M ⊗ V`). The projection sends `j¹s(x)` to
  `s x` and is surjective (`TauCeti.FirstJetBundle.value_surjective`), the inclusion is injective
  (`TauCeti.FirstJetBundle.ofDeriv_injective`), their composite is zero
  (`TauCeti.FirstJetBundle.value_comp_ofDeriv`), and the sequence
  `0 → Hom(TₓM, Vₓ) → J¹Vₓ → Vₓ → 0` is exact in the middle
  (`TauCeti.FirstJetBundle.range_ofDeriv`), hence exact. The
  inclusion is intrinsic: in every chart it reads `L` in that chart and trivialization
  (`TauCeti.FirstJetBundle.coordChange_ofDeriv`).

The construction follows Mathlib's `tangentBundleCore`: the bundle is indexed by the points of `M`,
and derivatives in charts are taken within `range I`, so manifolds with boundary are allowed.

## References

* I. Kolář, P. W. Michor and J. Slovák, *Natural Operations in Differential Geometry*,
  §§12.16–12.17.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners 𝕜 E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*)

namespace FirstJetBundle

variable [TopologicalSpace F]
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V]

/-- The domain of the first-jet chart at `i`: the points where both the preferred trivialization
of `V` and the preferred chart of `M` at `i` are defined. -/
def baseSet (i : M) : Set M :=
  (trivializationAt F V i).baseSet ∩ (chartAt H i).source

/-- A point lies in the first-jet chart domain at `i` when both the preferred trivialization of
`V` and the preferred chart of `M` at `i` are defined there. -/
@[simp]
theorem mem_baseSet_iff {i y : M} :
    y ∈ baseSet (H := H) F V i ↔
      y ∈ (trivializationAt F V i).baseSet ∧ y ∈ (chartAt H i).source :=
  (Iff.rfl)

/-- The first-jet chart domains are open. -/
theorem isOpen_baseSet (i : M) : IsOpen (baseSet (H := H) F V i) :=
  (trivializationAt F V i).open_baseSet.inter (chartAt H i).open_source

/-- A point lies in the domain of its own first-jet chart. -/
theorem mem_baseSet_self (i : M) : i ∈ baseSet (H := H) F V i :=
  ⟨mem_baseSet_trivializationAt F V i, mem_chart_source H i⟩

variable {F V}

/-- A point of the first-jet chart domain at `i` lies in the source of the extended chart at
`i`. -/
theorem mem_extChartAt_source_of_mem_baseSet {i y : M}
    (hy : y ∈ baseSet (H := H) F V i) : y ∈ (extChartAt I i).source := by
  rw [extChartAt_source]
  exact hy.2

/-- Near the image in the extended chart at `j` of a point `y` of the first-jet chart domain at `i`
and the chart domain at `j`, the inverse of that extended chart lands in the first-jet chart domain
at `i`. -/
theorem eventually_extChartAt_symm_mem_baseSet {i j y : M}
    (hi : y ∈ baseSet (H := H) F V i) (hj : y ∈ (chartAt H j).source) :
    ∀ᶠ z in 𝓝[range I] extChartAt I j y, (extChartAt I j).symm z ∈ baseSet (H := H) F V i :=
  mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds'
    (by rwa [extChartAt_source]) ((isOpen_baseSet F V i).mem_nhds hi))

end FirstJetBundle

section

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommMonoid (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]

namespace FirstJetBundle

/-- The coordinate change of `V` from the trivialization at `i` to the one at `j`, written in
the extended chart at `j`. -/
def fiberCoordChange (i j : M) (z : E) : F →L[𝕜] F :=
  (trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) ((extChartAt I j).symm z)

/-- `fiberCoordChange` is the coordinate change of `V` at the point with chart coordinate `z`. -/
theorem fiberCoordChange_apply (i j : M) (z : E) :
    fiberCoordChange I F V i j z =
      (trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) ((extChartAt I j).symm z) :=
  (rfl)

variable {I F V}

/-- At the image of a point of the chart domain, `fiberCoordChange` is the coordinate change of
`V` at that point. -/
theorem fiberCoordChange_extChartAt {i j y : M} (hy : y ∈ (chartAt H j).source) :
    fiberCoordChange I F V i j (extChartAt I j y) =
      (trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) y := by
  rw [fiberCoordChange_apply, (extChartAt I j).left_inv (by rwa [extChartAt_source])]

/-- The coordinate change of `V`, written in a chart, is `C^n` when `M` and `V` are. -/
theorem contDiffWithinAt_fiberCoordChange {n : ℕ∞ω} [IsManifold I n M]
    [ContMDiffVectorBundle n F V I] {i j y : M} (hi : y ∈ (trivializationAt F V i).baseSet)
    (hj : y ∈ baseSet (H := H) F V j) :
    ContDiffWithinAt 𝕜 n (fiberCoordChange I F V i j) (range I) (extChartAt I j y) := by
  have hy := mem_extChartAt_source_of_mem_baseSet I hj
  have h₁ : ContMDiffAt I 𝓘(𝕜, F →L[𝕜] F) n (fun b ↦
      ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) b : F →L[𝕜] F))
      ((extChartAt I j).symm (extChartAt I j y)) := by
    rw [(extChartAt I j).left_inv hy]
    exact contMDiffAt_coordChangeL hi hj.1
  exact contMDiffWithinAt_iff_contDiffWithinAt.1 (h₁.comp_contMDiffWithinAt _
    (contMDiffWithinAt_extChartAt_symm_range j ((extChartAt I j).map_source hy)))

/-- The coordinate change of `V`, written in a chart, has its chart derivative as a derivative
when `M` and `V` are `C^1`. -/
theorem hasFDerivWithinAt_fiberCoordChange [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]
    {i j y : M} (hi : y ∈ (trivializationAt F V i).baseSet) (hj : y ∈ baseSet (H := H) F V j) :
    HasFDerivWithinAt (fiberCoordChange I F V i j)
      (fderivWithin 𝕜 (fiberCoordChange I F V i j) (range I) (extChartAt I j y)) (range I)
      (extChartAt I j y) :=
  ((contDiffWithinAt_fiberCoordChange (n := 1) hi hj).differentiableWithinAt
    one_ne_zero).hasFDerivWithinAt

section

variable (I F V) [IsManifold I 1 M]

/-- The change of first-jet coordinates at `y` from the chart and trivialization at `i` to the
ones at `j`: the value transforms by the coordinate change of `V`, and the derivative by the
product rule for this coordinate change and the chain rule for the change of charts. -/
def coordChange (i j y : M) : (F × (E →L[𝕜] F)) →L[𝕜] F × (E →L[𝕜] F) :=
  ContinuousLinearMap.firstJetPullback
    ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) y)
    (fderivWithin 𝕜 (fiberCoordChange I F V i j) (range I) (extChartAt I j y))
    (tangentCoordChange I j i y)

/-- The first-jet coordinate change, written out on a jet `(v, A)`. -/
theorem coordChange_apply (i j y : M) (v : F × (E →L[𝕜] F)) :
    coordChange I F V i j y v =
      ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) y v.1,
        (fderivWithin 𝕜 (fiberCoordChange I F V i j) (range I) (extChartAt I j y)).flip v.1 +
          ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) y : F →L[𝕜] F).comp
            (v.2.comp (tangentCoordChange I j i y))) :=
  ContinuousLinearMap.firstJetPullback_apply _ _ _ _

end

/-- The first-jet coordinate changes of a `C^(n+1)` vector bundle over a `C^(n+1)` manifold are
`C^n`. -/
theorem contMDiffOn_coordChange {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [ContMDiffVectorBundle (n + 1) F V I] (i j : M) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    ContMDiffOn I 𝓘(𝕜, (F × (E →L[𝕜] F)) →L[𝕜] F × (E →L[𝕜] F)) n (coordChange I F V i j)
      (baseSet (H := H) F V i ∩ baseSet (H := H) F V j) := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : IsManifold I n M := .of_le (n := n + 1) le_self_add
  set U := baseSet (H := H) F V i ∩ baseSet (H := H) F V j
  have hUj : U ⊆ (chartAt H j).source := fun y hy ↦ hy.2.2
  set T := (extChartAt I j).target ∩ (extChartAt I j).symm ⁻¹'
    (baseSet (H := H) F V i ∩ baseSet (H := H) F V j)
  have hT : ∀ z ∈ T, ContDiffWithinAt 𝕜 (n + 1) (fiberCoordChange I F V i j) (range I) z := by
    rintro z ⟨hz, hzU⟩
    rw [← (extChartAt I j).right_inv hz]
    exact contDiffWithinAt_fiberCoordChange hzU.1.1 hzU.2
  have hTr : T ⊆ range I := fun z hz ↦ extChartAt_target_subset_range j hz.1
  -- The coordinate change, written in the chart at `j`.
  have hΨ : ContDiffOn 𝕜 n (fun z ↦ ContinuousLinearMap.firstJetPullback
      (fiberCoordChange I F V i j z) (fderivWithin 𝕜 (fiberCoordChange I F V i j) (range I) z)
      (fderivWithin 𝕜 (extChartAt I i ∘ (extChartAt I j).symm) (range I) z)) T := by
    refine ContDiffOn.firstJetPullback (fun z hz ↦ ((hT z hz).mono hTr).of_le le_self_add)
      (fun z hz ↦ (((hT z hz).fderivWithin_right I.uniqueDiffOn le_rfl (hTr hz))).mono hTr) ?_
    refine (contDiffOn_fderiv_coord_change (I := I) (n := n) ⟨chartAt H j, chart_mem_atlas H j⟩
      ⟨chartAt H i, chart_mem_atlas H i⟩).mono ?_
    rintro z ⟨hz, hzU⟩
    refine ⟨hz, ?_⟩
    simp only [mem_preimage, PartialEquiv.symm_symm, OpenPartialHomeomorph.extend_source]
    exact hzU.1.2
  have hmaps : MapsTo (extChartAt I j) U T := fun y hy ↦ by
    have hy' := mem_extChartAt_source_of_mem_baseSet I hy.2
    exact ⟨(extChartAt I j).map_source hy', by rwa [mem_preimage, (extChartAt I j).left_inv hy']⟩
  refine ((contMDiffOn_iff_contDiffOn.2 hΨ).comp (contMDiffOn_extChartAt.mono hUj)
    hmaps).congr fun y hy ↦ ?_
  rw [Function.comp_apply, fiberCoordChange_extChartAt (hUj hy), coordChange,
    tangentCoordChange_def]

variable [IsManifold I 1 M]

/-- The first-jet coordinate change from a chart to itself is the identity. -/
theorem coordChange_self_apply {i y : M} (hy : y ∈ baseSet (H := H) F V i)
    (v : F × (E →L[𝕜] F)) : coordChange I F V i i y v = v := by
  have hy' := mem_extChartAt_source_of_mem_baseSet I hy
  have hderiv : fderivWithin 𝕜 (fiberCoordChange I F V i i) (range I) (extChartAt I i y) = 0 := by
    refine ((hasFDerivWithinAt_const (ContinuousLinearMap.id 𝕜 F) _ _).congr_of_eventuallyEq
      ?_ ?_).fderivWithin (I.uniqueDiffOn _ (extChartAt_target_subset_range i
        ((extChartAt I i).map_source hy')))
    · filter_upwards [eventually_extChartAt_symm_mem_baseSet I hy hy.2] with z hz
      ext w
      exact (trivializationAt F V i).coordChangeL_same_apply 𝕜 hz.1 w
    · ext w
      rw [fiberCoordChange_extChartAt hy.2]
      exact (trivializationAt F V i).coordChangeL_same_apply 𝕜 hy.1 w
  have hc : tangentCoordChange I i i y = ContinuousLinearMap.id 𝕜 E := by
    ext w
    exact tangentCoordChange_self hy'
  rw [coordChange_apply, hderiv, hc]
  refine Prod.ext ((trivializationAt F V i).coordChangeL_same_apply 𝕜 hy.1 v.1) ?_
  ext w
  simp [(trivializationAt F V i).coordChangeL_same_apply 𝕜 hy.1]

variable [ContMDiffVectorBundle 1 F V I]

/-- **Product and chain rule for the coordinate changes of `V`**: the chart derivative of the
coordinate change from `i` to `k` is assembled from those from `i` to `j` and from `j` to `k`. -/
theorem fderivWithin_fiberCoordChange_trans {i j k y : M}
    (hi : y ∈ (trivializationAt F V i).baseSet) (hj : y ∈ baseSet (H := H) F V j)
    (hk : y ∈ baseSet (H := H) F V k) :
    fderivWithin 𝕜 (fiberCoordChange I F V i k) (range I) (extChartAt I k y) =
      (ContinuousLinearMap.compL 𝕜 F F F
          ((trivializationAt F V j).coordChangeL 𝕜 (trivializationAt F V k) y)).comp
        ((fderivWithin 𝕜 (fiberCoordChange I F V i j) (range I) (extChartAt I j y)).comp
          (tangentCoordChange I k j y)) +
      ((ContinuousLinearMap.compL 𝕜 F F F).flip
          ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) y)).comp
        (fderivWithin 𝕜 (fiberCoordChange I F V j k) (range I) (extChartAt I k y)) := by
  have hj' := mem_extChartAt_source_of_mem_baseSet I hj
  have hk' := mem_extChartAt_source_of_mem_baseSet I hk
  have hy : (extChartAt I j ∘ (extChartAt I k).symm) (extChartAt I k y) = extChartAt I j y := by
    rw [Function.comp_apply, (extChartAt I k).left_inv hk']
  -- The derivative of the coordinate change from `i` to `j`, along the change of charts.
  have hij : HasFDerivWithinAt (fun z ↦ fiberCoordChange I F V i j
      ((extChartAt I j ∘ (extChartAt I k).symm) z))
      ((fderivWithin 𝕜 (fiberCoordChange I F V i j) (range I) (extChartAt I j y)).comp
        (tangentCoordChange I k j y)) (range I) (extChartAt I k y) := by
    have h : HasFDerivWithinAt (fiberCoordChange I F V i j)
        (fderivWithin 𝕜 (fiberCoordChange I F V i j) (range I) (extChartAt I j y)) (range I)
        ((extChartAt I j ∘ (extChartAt I k).symm) (extChartAt I k y)) := by
      rw [hy]
      exact hasFDerivWithinAt_fiberCoordChange hi hj
    exact h.comp _ (hasFDerivWithinAt_tangentCoordChange ⟨hk', hj'⟩)
      (mapsTo_extChartAt_comp_extChartAt_symm I j k _)
  have hprod := (hasFDerivWithinAt_fiberCoordChange (I := I) hj.1 hk).clm_comp hij
  rw [fiberCoordChange_extChartAt hk.2, hy, fiberCoordChange_extChartAt hj.2] at hprod
  refine (hprod.congr_of_eventuallyEq ?_ ?_).fderivWithin
    (I.uniqueDiffOn _ (extChartAt_target_subset_range k ((extChartAt I k).map_source hk')))
  · filter_upwards [mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds' hk'
        ((trivializationAt F V i).open_baseSet.mem_nhds hi)),
      eventually_extChartAt_symm_mem_baseSet I hj hk.2,
      eventually_extChartAt_symm_mem_baseSet I hk hk.2] with z hzi hzj hzk
    ext w
    simp only [fiberCoordChange_apply, Function.comp_apply, ContinuousLinearMap.coe_comp,
      (extChartAt I j).left_inv (mem_extChartAt_source_of_mem_baseSet I hzj)]
    exact ((trivializationAt F V i).coordChangeL_coordChangeL_apply 𝕜 _ _ hzi hzj.1
      hzk.1 w).symm
  · ext w
    simp only [fiberCoordChange_extChartAt hk.2, ContinuousLinearMap.coe_comp,
      Function.comp_apply, (extChartAt I k).left_inv hk', fiberCoordChange_extChartAt hj.2]
    exact ((trivializationAt F V i).coordChangeL_coordChangeL_apply 𝕜 _ _ hi hj.1 hk.1
      w).symm

/-- **Cocycle law for first-jet coordinate changes**. -/
theorem coordChange_comp_apply {i j k y : M} (hi : y ∈ baseSet (H := H) F V i)
    (hj : y ∈ baseSet (H := H) F V j) (hk : y ∈ baseSet (H := H) F V k)
    (v : F × (E →L[𝕜] F)) :
    coordChange I F V j k y (coordChange I F V i j y v) = coordChange I F V i k y v := by
  have hcomp : (tangentCoordChange I j i y).comp (tangentCoordChange I k j y) =
      tangentCoordChange I k i y := by
    ext w
    exact tangentCoordChange_comp ⟨⟨mem_extChartAt_source_of_mem_baseSet I hk,
      mem_extChartAt_source_of_mem_baseSet I hj⟩, mem_extChartAt_source_of_mem_baseSet I hi⟩
  have ha : ((trivializationAt F V j).coordChangeL 𝕜 (trivializationAt F V k) y :
      F →L[𝕜] F).comp
        ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) y : F →L[𝕜] F) =
      ((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V k) y : F →L[𝕜] F) := by
    ext w
    exact (trivializationAt F V i).coordChangeL_coordChangeL_apply 𝕜 _ _ hi.1 hj.1 hk.1 w
  rw [coordChange, coordChange, coordChange, ← ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.firstJetPullback_comp, ha, hcomp,
    fderivWithin_fiberCoordChange_trans hi.1 hj hk]

end FirstJetBundle

section

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]

/-- The vector bundle core of the first-jet bundle of `V`, indexed by the points of `M`. Over the
chart at `i`, a first jet is described by the value and the chart derivative of the local
representative of a section in the preferred trivialization of `V` at `i`. -/
def firstJetBundleCore : VectorBundleCore 𝕜 M (F × (E →L[𝕜] F)) M where
  baseSet := FirstJetBundle.baseSet F V
  isOpen_baseSet := FirstJetBundle.isOpen_baseSet F V
  indexAt := id
  mem_baseSet_at := FirstJetBundle.mem_baseSet_self F V
  coordChange := FirstJetBundle.coordChange I F V
  coordChange_self _ _ hy v := FirstJetBundle.coordChange_self_apply hy v
  continuousOn_coordChange i j := by
    have : IsManifold I (0 + 1) M := by simpa
    have : ContMDiffVectorBundle (0 + 1) F V I := by simpa
    exact (FirstJetBundle.contMDiffOn_coordChange (n := 0) i j).continuousOn
  coordChange_comp _ _ _ _ hy v := FirstJetBundle.coordChange_comp_apply hy.1.1 hy.1.2 hy.2 v

/-- The first-jet chart domains are the domains of `FirstJetBundle.baseSet`. -/
@[simp]
theorem firstJetBundleCore_baseSet :
    (firstJetBundleCore I F V).baseSet = FirstJetBundle.baseSet (H := H) F V := (rfl)

/-- The first-jet chart at a point is the one indexed by that point. -/
@[simp]
theorem firstJetBundleCore_indexAt (x : M) : (firstJetBundleCore I F V).indexAt x = x := (rfl)

/-- The coordinate changes of `firstJetBundleCore` are `FirstJetBundle.coordChange`. -/
@[simp]
theorem firstJetBundleCore_coordChange :
    (firstJetBundleCore I F V).coordChange = FirstJetBundle.coordChange I F V := (rfl)

/-- The first-jet bundle `J¹V` of a vector bundle `V`. Its fibre over `x` is
`F × (E →L[𝕜] F)`, read as the value and the chart derivative of the local representative of a
section in the preferred chart of `M` and the preferred trivialization of `V` at `x`. -/
abbrev FirstJetBundle : M → Type _ :=
  (firstJetBundleCore I F V).Fiber

end

/-- The vector bundle core of the first-jet bundle of a `C^(n+1)` vector bundle over a `C^(n+1)`
manifold has `C^n` coordinate changes. -/
theorem firstJetBundleCore_isContMDiff {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [ContMDiffVectorBundle (n + 1) F V I] :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffVectorBundle 1 F V I := .of_le (n := n + 1) le_add_self
    (firstJetBundleCore I F V).IsContMDiff I n :=
  ⟨FirstJetBundle.contMDiffOn_coordChange⟩

/-- The first-jet bundle of a `C^(n+1)` vector bundle over a `C^(n+1)` manifold is a `C^n`
vector bundle. -/
theorem FirstJetBundle.contMDiffVectorBundle {n : ℕ∞ω} [IsManifold I (n + 1) M]
    [ContMDiffVectorBundle (n + 1) F V I] :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffVectorBundle 1 F V I := .of_le (n := n + 1) le_add_self
    ContMDiffVectorBundle n (F × (E →L[𝕜] F)) (FirstJetBundle I F V) I := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : ContMDiffVectorBundle 1 F V I := .of_le (n := n + 1) le_add_self
  have := firstJetBundleCore_isContMDiff I F V (n := n)
  exact (firstJetBundleCore I F V).instContMDiffVectorBundle

/-- The first-jet bundle of a smooth vector bundle over a smooth manifold is smooth. -/
instance [IsManifold I ∞ M] [ContMDiffVectorBundle ∞ F V I] :
    ContMDiffVectorBundle ∞ (F × (E →L[𝕜] F)) (FirstJetBundle I F V) I := by
  have : IsManifold I (∞ + 1) M := by simpa using (inferInstance : IsManifold I ∞ M)
  have : ContMDiffVectorBundle (∞ + 1) F V I := by
    simpa using (inferInstance : ContMDiffVectorBundle ∞ F V I)
  exact FirstJetBundle.contMDiffVectorBundle I F V

/-- The first-jet bundle of an analytic vector bundle over an analytic manifold is analytic. -/
instance [IsManifold I ω M] [ContMDiffVectorBundle ω F V I] :
    ContMDiffVectorBundle ω (F × (E →L[𝕜] F)) (FirstJetBundle I F V) I := by
  have : IsManifold I (ω + 1) M := by simpa using (inferInstance : IsManifold I ω M)
  have : ContMDiffVectorBundle (ω + 1) F V I := by
    simpa using (inferInstance : ContMDiffVectorBundle ω F V I)
  exact FirstJetBundle.contMDiffVectorBundle I F V

end

namespace FirstJetBundle

section

variable [TopologicalSpace F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V]

/-- The local representative `z ↦ eᵢ (s (φᵢ⁻¹ z))` of a section `s` of `V` in the extended chart
`φᵢ` and the preferred trivialization `eᵢ` at `i`. -/
def localRep (s : ∀ x, V x) (i : M) (z : E) : F :=
  (trivializationAt F V i ⟨(extChartAt I i).symm z, s ((extChartAt I i).symm z)⟩).2

/-- The local representative at `z` is the value of the section at the point with chart
coordinate `z`, read in the trivialization at `i`. -/
theorem localRep_apply (s : ∀ x, V x) (i : M) (z : E) :
    localRep I F s i z =
      (trivializationAt F V i ⟨(extChartAt I i).symm z, s ((extChartAt I i).symm z)⟩).2 :=
  (rfl)

/-- At the image of a point of the chart domain, the local representative is the trivialized
value of the section. -/
theorem localRep_extChartAt (s : ∀ x, V x) {i y : M} (hy : y ∈ (chartAt H i).source) :
    localRep I F s i (extChartAt I i y) = (trivializationAt F V i ⟨y, s y⟩).2 := by
  rw [localRep_apply, (extChartAt I i).left_inv (by rwa [extChartAt_source])]

end

section

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommMonoid (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- The local representative in the chart and trivialization at `i` of a section that is `C^n` at
a point `y` of the first-jet chart domain at `i` is `C^n` within `range I` at the image of `y`. -/
theorem contDiffWithinAt_localRep {n : ℕ∞ω} [IsManifold I n M] [ContMDiffVectorBundle n F V I]
    {s : ∀ x, V x} {i y : M}
    (hs : ContMDiffAt I (I.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (s x)) y)
    (hi : y ∈ baseSet (H := H) F V i) :
    ContDiffWithinAt 𝕜 n (localRep I F s i) (range I) (extChartAt I i y) := by
  have hy := mem_extChartAt_source_of_mem_baseSet I hi
  have h₁ : ContMDiffAt I 𝓘(𝕜, F) n (fun x ↦ (trivializationAt F V i ⟨x, s x⟩).2)
      ((extChartAt I i).symm (extChartAt I i y)) := by
    rw [(extChartAt I i).left_inv hy]
    exact ((trivializationAt F V i).contMDiffAt_section_iff hi.1).1 hs
  exact contMDiffWithinAt_iff_contDiffWithinAt.1 (h₁.comp_contMDiffWithinAt _
    (contMDiffWithinAt_extChartAt_symm_range i ((extChartAt I i).map_source hy)))

/-- **Transformation law for local representatives.** Near the image of a point `y` of the
first-jet chart domains at `i` and `j`, the local representative at `j` is the coordinate change
of `V` from `i` to `j` applied to the local representative at `i` after the change of charts. -/
theorem localRep_eventuallyEq_fiberCoordChange (s : ∀ x, V x) {i j y : M}
    (hi : y ∈ baseSet (H := H) F V i) (hj : y ∈ baseSet (H := H) F V j) :
    localRep I F s j =ᶠ[𝓝[range I] (extChartAt I j y)] fun z ↦ fiberCoordChange I F V i j z
      (localRep I F s i ((extChartAt I i ∘ (extChartAt I j).symm) z)) := by
  filter_upwards [eventually_extChartAt_symm_mem_baseSet I hi hj.2,
    eventually_extChartAt_symm_mem_baseSet I hj hj.2] with z hzi hzj
  rw [Function.comp_apply, localRep_extChartAt I F s hzi.2, fiberCoordChange_apply,
    ContinuousLinearEquiv.coe_coe,
    Trivialization.coordChangeL_apply_snd 𝕜 _ _ (p := ⟨_, s _⟩) hzi.1 hzj.1, localRep_apply]

section

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]

/-- The local representative in the chart and trivialization at `i` of a section that is
differentiable at a point `y` of the first-jet chart domain at `i` is differentiable within
`range I` at the image of `y`. -/
theorem differentiableWithinAt_localRep {s : ∀ x, V x} {i y : M}
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) y)
    (hi : y ∈ baseSet (H := H) F V i) :
    DifferentiableWithinAt 𝕜 (localRep I F s i) (range I) (extChartAt I i y) := by
  have hy := mem_extChartAt_source_of_mem_baseSet I hi
  have h₁ : MDifferentiableAt I 𝓘(𝕜, F) (fun x ↦ (trivializationAt F V i ⟨x, s x⟩).2)
      ((extChartAt I i).symm (extChartAt I i y)) := by
    rw [(extChartAt I i).left_inv hy]
    exact ((trivializationAt F V i).mdifferentiableAt_section_iff I s hi.1).1 hs
  exact mdifferentiableWithinAt_iff_differentiableWithinAt.1 (h₁.comp_mdifferentiableWithinAt _
    (mdifferentiableWithinAt_extChartAt_symm ((extChartAt I i).map_source hy)))

/-- The first jet `j¹s(x)` of a section `s` of `V` at `x`: the value at `x` and the chart
derivative at `x` of the local representative of `s` in the chart and trivialization at `x`. -/
def jet (s : ∀ x, V x) (x : M) : FirstJetBundle I F V x :=
  ((trivializationAt F V x ⟨x, s x⟩).2,
    fderivWithin 𝕜 (localRep I F s x) (range I) (extChartAt I x x))

/-- The value coordinate of `j¹s(x)` is the value of `s` in the trivialization at `x`. -/
@[simp]
theorem jet_fst (s : ∀ x, V x) (x : M) :
    (jet I F s x).1 = (trivializationAt F V x ⟨x, s x⟩).2 := (rfl)

/-- The derivative coordinate of `j¹s(x)` is the chart derivative of the local representative
at `x`. -/
@[simp]
theorem jet_snd (s : ∀ x, V x) (x : M) :
    (jet I F s x).2 = fderivWithin 𝕜 (localRep I F s x) (range I) (extChartAt I x x) := (rfl)

/-- **The first jet in an arbitrary chart.** In the chart and trivialization at `i`, the first jet
of a section differentiable at `y` consists of the value and the chart derivative of the local
representative of the section. -/
theorem coordChange_jet {s : ∀ x, V x} {y : M}
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) y) {i : M}
    (hi : y ∈ baseSet (H := H) F V i) :
    coordChange I F V y i y (jet I F s y) =
      ((trivializationAt F V i ⟨y, s y⟩).2,
        fderivWithin 𝕜 (localRep I F s i) (range I) (extChartAt I i y)) := by
  have hy := mem_baseSet_self (H := H) F V y
  have hyi := mem_extChartAt_source_of_mem_baseSet I hi
  have hyy := mem_extChartAt_source_of_mem_baseSet I hy
  have hval : ((trivializationAt F V y).coordChangeL 𝕜 (trivializationAt F V i) y : F →L[𝕜] F)
      (trivializationAt F V y ⟨y, s y⟩).2 = (trivializationAt F V i ⟨y, s y⟩).2 :=
    Trivialization.coordChangeL_apply_snd 𝕜 _ _ (p := ⟨y, s y⟩) hy.1 hi.1
  -- The local representative at `y` is differentiable, and so is the one at `i`.
  have hrep : HasFDerivWithinAt (localRep I F s y)
      (fderivWithin 𝕜 (localRep I F s y) (range I) (extChartAt I y y)) (range I)
      ((extChartAt I y ∘ (extChartAt I i).symm) (extChartAt I i y)) := by
    rw [Function.comp_apply, (extChartAt I i).left_inv hyi]
    exact (differentiableWithinAt_localRep I F hs hy).hasFDerivWithinAt
  have hcomp := (hasFDerivWithinAt_fiberCoordChange hy.1 hi).clm_apply (hrep.comp _
    (hasFDerivWithinAt_tangentCoordChange ⟨hyi, hyy⟩)
    (mapsTo_extChartAt_comp_extChartAt_symm I y i _))
  -- Differentiating the transformation law for local representatives by the product and chain
  -- rules gives the jet transformation.
  have hD := (hcomp.congr_of_eventuallyEq
    (localRep_eventuallyEq_fiberCoordChange I F s hy hi) ?_).fderivWithin
    (I.uniqueDiffOn _ (extChartAt_target_subset_range i ((extChartAt I i).map_source hyi)))
  · refine (coordChange_apply I F V y i y _).trans ?_
    rw [hD]
    simp only [Function.comp_apply, (extChartAt I i).left_inv hyi, localRep_extChartAt I F s hy.2,
      fiberCoordChange_extChartAt hi.2]
    refine Prod.ext ?_ ?_
    · simpa using hval
    · rw [jet_fst, jet_snd, add_comm]
  · simp only [Function.comp_apply, (extChartAt I i).left_inv hyi, localRep_extChartAt I F s hy.2,
      fiberCoordChange_extChartAt hi.2, hval, localRep_extChartAt I F s hi.2]

/-- The preferred trivialization of `J¹V` at `i` reads a first jet in the chart and
trivialization of `V` at `i`. -/
theorem trivializationAt_apply_snd (i : M)
    (p : TotalSpace (F × (E →L[𝕜] F)) (FirstJetBundle I F V)) :
    (trivializationAt (F × (E →L[𝕜] F)) (FirstJetBundle I F V) i p).2 =
      coordChange I F V p.1 i p.1 p.2 := (rfl)

/-- In the preferred trivialization of `J¹V` at `i`, the first jet of a section differentiable
at `y` consists of the value and the chart derivative of its local representative at `i`. -/
theorem trivializationAt_jet {s : ∀ x, V x} {y : M}
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) y) {i : M}
    (hi : y ∈ baseSet (H := H) F V i) :
    (trivializationAt (F × (E →L[𝕜] F)) (FirstJetBundle I F V) i ⟨y, jet I F s y⟩).2 =
      ((trivializationAt F V i ⟨y, s y⟩).2,
        fderivWithin 𝕜 (localRep I F s i) (range I) (extChartAt I i y)) := by
  rw [trivializationAt_apply_snd]
  exact coordChange_jet I F hs hi

/-- The value of a first jet, the fibre of the projection `J¹V → V`. -/
def value (x : M) : FirstJetBundle I F V x →L[𝕜] V x :=
  (trivializationAt F V x).symmL 𝕜 x ∘L ContinuousLinearMap.fst 𝕜 F (E →L[𝕜] F)

/-- The value of a first jet is its value coordinate read back through the trivialization. -/
theorem value_apply (x : M) (j : FirstJetBundle I F V x) :
    value I F x j = (trivializationAt F V x).symm x j.1 := by
  have h : value I F x j = (trivializationAt F V x).symmL 𝕜 x j.1 := (rfl)
  rw [h, Trivialization.symmL_apply _ (mem_baseSet_trivializationAt F V x)]

/-- The value of the first jet of a section is the value of the section. -/
@[simp]
theorem value_jet (s : ∀ x, V x) (x : M) : value I F x (jet I F s x) = s x := by
  rw [value_apply, jet_fst,
    Trivialization.symm_apply_apply_mk _ (mem_baseSet_trivializationAt F V x)]

/-- Every vector is the value of a first jet. -/
theorem value_surjective (x : M) : Function.Surjective (value I F (V := V) x) := fun v ↦
  ⟨((trivializationAt F V x ⟨x, v⟩).2, 0), (value_apply I F x _).trans
    (Trivialization.symm_apply_apply_mk _ (mem_baseSet_trivializationAt F V x) v)⟩

end

/-- **The first jet of a `C^(n+1)` section is a `C^n` section of `J¹V`.** -/
theorem contMDiffOn_jet {n : ℕ∞ω} [IsManifold I (n + 1) M] [ContMDiffVectorBundle (n + 1) F V I]
    {s : ∀ x, V x} {U : Set M} (hU : IsOpen U)
    (hs : ContMDiffOn I (I.prod 𝓘(𝕜, F)) (n + 1) (fun x ↦ TotalSpace.mk' F x (s x)) U) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffVectorBundle 1 F V I := .of_le (n := n + 1) le_add_self
    ContMDiffOn I (I.prod 𝓘(𝕜, F × (E →L[𝕜] F))) n
      (fun x ↦ TotalSpace.mk' (F × (E →L[𝕜] F)) x (jet I F s x)) U := by
  have : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
  have : IsManifold I n M := .of_le (n := n + 1) le_self_add
  have : ContMDiffVectorBundle 1 F V I := .of_le (n := n + 1) le_add_self
  intro x₀ hx₀
  have hsx₀ := hs.contMDiffAt (hU.mem_nhds hx₀)
  have hx₀' : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  refine ContMDiffAt.contMDiffWithinAt ((contMDiffAt_section_iff x₀).2 ?_)
  -- The value coordinate.
  have hval := (contMDiffAt_section_iff x₀).1 hsx₀
  -- The derivative coordinate: the chart derivative of the local representative.
  have hrep := contDiffWithinAt_localRep I F hsx₀ (mem_baseSet_self (H := H) F V x₀)
  have hderiv : ContMDiffAt I 𝓘(𝕜, E →L[𝕜] F) n
      (fun x ↦ fderivWithin 𝕜 (localRep I F s x₀) (range I) (extChartAt I x₀ x)) x₀ := by
    have h₂ := contMDiffWithinAt_iff_contDiffWithinAt.2 (hrep.fderivWithin_right I.uniqueDiffOn
      le_rfl (extChartAt_target_subset_range x₀ ((extChartAt I x₀).map_source hx₀')))
    rw [← contMDiffWithinAt_univ]
    exact h₂.comp x₀ contMDiffAt_extChartAt.contMDiffWithinAt fun x _ ↦ by
      rw [extChartAt_coe]; exact mem_range_self _
  refine ((hval.of_le le_self_add).prodMk_space hderiv).congr_of_eventuallyEq ?_
  filter_upwards [hU.mem_nhds hx₀, (isOpen_baseSet (H := H) F V x₀).mem_nhds
    (mem_baseSet_self (H := H) F V x₀)] with x hxU hxb
  exact trivializationAt_jet I F ((hs x hxU).contMDiffAt (hU.mem_nhds hxU)
    |>.mdifferentiableAt (by simp)) hxb

/-- The first jet of a `C^(n+1)` section is a `C^n` section of `J¹V`. -/
theorem contMDiff_jet {n : ℕ∞ω} [IsManifold I (n + 1) M] [ContMDiffVectorBundle (n + 1) F V I]
    {s : ∀ x, V x} (hs : ContMDiff I (I.prod 𝓘(𝕜, F)) (n + 1) fun x ↦ TotalSpace.mk' F x (s x)) :
    haveI : IsManifold I 1 M := .of_le (n := n + 1) le_add_self
    haveI : ContMDiffVectorBundle 1 F V I := .of_le (n := n + 1) le_add_self
    ContMDiff I (I.prod 𝓘(𝕜, F × (E →L[𝕜] F))) n
      fun x ↦ TotalSpace.mk' (F × (E →L[𝕜] F)) x (jet I F s x) := by
  rw [← contMDiffOn_univ] at hs ⊢
  exact contMDiffOn_jet I F isOpen_univ hs

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]

/-- A first jet has value zero exactly when its value coordinate vanishes. -/
theorem value_eq_zero_iff (x : M) (j : FirstJetBundle I F V x) : value I F x j = 0 ↔ j.1 = 0 := by
  have hx := mem_baseSet_trivializationAt F V x
  have h : value I F x j = (trivializationAt F V x).symmL 𝕜 x j.1 := (rfl)
  rw [h]
  refine ⟨fun h0 ↦ ?_, fun h0 ↦ by rw [h0, map_zero]⟩
  rw [← (trivializationAt F V x).continuousLinearMapAt_symmL (R := 𝕜) hx j.1, h0, map_zero]

/-- A first jet with value coordinate zero has value zero. -/
@[simp]
theorem value_mk_zero (x : M) (A : E →L[𝕜] F) :
    value I F x (((0 : F), A) : FirstJetBundle I F V x) = (0 : V x) :=
  (value_eq_zero_iff I F x _).2 rfl

end

section Kernel

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul 𝕜 (V x)]

/-- The inclusion of the continuous linear maps `Hom(TₓM, Vₓ)` into the first jets at `x`: a
homomorphism `L` gives the jet with value `0` whose chart derivative is `L` read in the
trivialization at `x`. -/
def ofDeriv (x : M) : (TangentSpace I x →L[𝕜] V x) →L[𝕜] FirstJetBundle I F V x :=
  ContinuousLinearMap.inr 𝕜 F (E →L[𝕜] F) ∘L
    ContinuousLinearMap.postcomp (TangentSpace I x)
      ((trivializationAt F V x).continuousLinearMapAt 𝕜 x)

/-- The jet of `L` has value coordinate `0` and derivative coordinate `L` read in the
trivialization at `x`. -/
@[simp]
theorem ofDeriv_apply (x : M) (L : TangentSpace I x →L[𝕜] V x) :
    ofDeriv I F x L =
      (((0 : F), ((trivializationAt F V x).continuousLinearMapAt 𝕜 x).comp L) :
        FirstJetBundle I F V x) :=
  (rfl)

/-- The inclusion of `Hom(TₓM, Vₓ)` into the first jets is injective. -/
theorem ofDeriv_injective (x : M) : Function.Injective (ofDeriv I F (V := V) x) := by
  intro L L' h
  ext v
  have h2 : (trivializationAt F V x).continuousLinearMapAt 𝕜 x (L v) =
      (trivializationAt F V x).continuousLinearMapAt 𝕜 x (L' v) :=
    congrArg (fun j : FirstJetBundle I F V x ↦ j.2 v) h
  have hx := mem_baseSet_trivializationAt F V x
  rw [← (trivializationAt F V x).symmL_continuousLinearMapAt (R := 𝕜) hx (L v), h2,
    (trivializationAt F V x).symmL_continuousLinearMapAt hx]

/-- The value of the jet of a homomorphism `L` is zero. -/
theorem value_ofDeriv (x : M) (L : TangentSpace I x →L[𝕜] V x) :
    value I F x (ofDeriv I F x L) = 0 :=
  (value_eq_zero_iff I F x _).2 rfl

/-- The composite `Hom(TₓM, Vₓ) → J¹Vₓ → Vₓ` of the first-jet sequence is zero. -/
@[simp]
theorem value_comp_ofDeriv (x : M) : value I F x ∘L ofDeriv I F (V := V) x = 0 :=
  ContinuousLinearMap.ext (value_ofDeriv I F x)

/-- **The first-jet sequence `0 → Hom(TₓM, Vₓ) → J¹Vₓ → Vₓ → 0` is exact in the middle**: the
first jets with value zero are exactly the images of `Hom(TₓM, Vₓ)`. -/
theorem range_ofDeriv (x : M) :
    LinearMap.range (ofDeriv I F (V := V) x).toLinearMap =
      LinearMap.ker (value I F x).toLinearMap := by
  have hx := mem_baseSet_trivializationAt F V x
  ext j
  simp only [LinearMap.mem_range, LinearMap.mem_ker, ContinuousLinearMap.coe_coe]
  rw [value_eq_zero_iff]
  refine ⟨?_, fun hj ↦ ⟨((trivializationAt F V x).symmL 𝕜 x).comp j.2, Prod.ext hj.symm ?_⟩⟩
  · rintro ⟨L, rfl⟩
    rfl
  · ext v
    exact Trivialization.continuousLinearMapAt_symmL _ hx (j.2 v)

/-- The inclusion of `Hom(TM, V)` is intrinsic: in the chart and trivialization at `i`, the jet
of `L` has value zero and its chart derivative is `L` read in that chart and trivialization. -/
theorem coordChange_ofDeriv {y i : M} (hi : y ∈ baseSet (H := H) F V i)
    (L : TangentSpace I y →L[𝕜] V y) :
    coordChange I F V y i y (ofDeriv I F y L) =
      ((0 : F), ((trivializationAt F V i).continuousLinearMapAt 𝕜 y).comp
        (L.comp (tangentCoordChange I i y y : E →L[𝕜] TangentSpace I y))) := by
  have hy := mem_baseSet_trivializationAt F V y
  refine (coordChange_apply I F V y i y _).trans (Prod.ext (map_zero _) ?_)
  ext v
  have hL : (trivializationAt F V y).symm y ((trivializationAt F V y).continuousLinearMapAt 𝕜 y
      (L (tangentCoordChange I i y y v))) = L (tangentCoordChange I i y y v) := by
    rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hy,
      Trivialization.symm_apply_apply_mk _ hy]
  simp only [ofDeriv_apply, map_zero, zero_add, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe]
  rw [Trivialization.coordChangeL_apply _ _ ⟨hy, hi.1⟩,
    Trivialization.continuousLinearMapAt_apply_of_mem (R := 𝕜) _ hi.1]
  exact congrArg (fun w ↦ (trivializationAt F V i ⟨y, w⟩).2) hL

end Kernel

section Vanishing

variable {I F}

section

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, AddCommMonoid (V x)]
  [∀ x, Module 𝕜 (V x)] [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]

/-- At a zero of a section `s`, the local representative vanishes at the image of `y` in any chart
and trivialization domain containing `y`. -/
theorem localRep_extChartAt_eq_zero {s : ∀ x, V x} {i y : M}
    (hy : y ∈ baseSet (H := H) F V i) (hs0 : s y = 0) :
    localRep I F s i (extChartAt I i y) = 0 := by
  rw [localRep_extChartAt I F s hy.2, hs0,
    (trivializationAt F V i).apply_eq_prod_continuousLinearEquivAt 𝕜 y hy.1, map_zero]

/-- **Chart change of a derivative at a zero of a section.** If a section `s` of a topological
vector bundle vanishes at `y`, then changing charts and trivializations transforms
`HasFDerivWithinAt` of its local representative tensorially, by the value coordinate change
composed with the chart Jacobian. Unlike the general jet transformation `coordChange_jet`, this
requires no `ContMDiffVectorBundle` hypothesis on `V`. -/
theorem hasFDerivWithinAt_localRep_congr_chart_of_eq_zero [IsManifold I 1 M]
    {s : ∀ x, V x} {i j y : M}
    (hi : y ∈ baseSet (H := H) F V i) (hj : y ∈ baseSet (H := H) F V j)
    (hs0 : s y = 0) {L : E →L[𝕜] F}
    (hs : HasFDerivWithinAt (localRep I F s i) L (range I) (extChartAt I i y)) :
    HasFDerivWithinAt (localRep I F s j)
      (((trivializationAt F V i).coordChangeL 𝕜 (trivializationAt F V j) y : F →L[𝕜] F).comp
        (L.comp (tangentCoordChange I j i y))) (range I) (extChartAt I j y) := by
  have hyi := mem_extChartAt_source_of_mem_baseSet I hi
  have hyj := mem_extChartAt_source_of_mem_baseSet I hj
  have hcc : ContinuousAt (fun b ↦ ((trivializationAt F V i).coordChangeL 𝕜
      (trivializationAt F V j) b : F →L[𝕜] F)) y :=
    (continuousOn_coordChange 𝕜 (trivializationAt F V i) (trivializationAt F V j)).continuousAt
      (((trivializationAt F V i).open_baseSet.inter
        (trivializationAt F V j).open_baseSet).mem_nhds ⟨hi.1, hj.1⟩)
  have hsymm : ContinuousWithinAt (extChartAt I j).symm (range I) (extChartAt I j y) :=
    (continuousOn_extChartAt_symm j _ ((extChartAt I j).map_source hyj)).mono_of_mem_nhdsWithin
      (extChartAt_target_mem_nhdsWithin_of_mem ((extChartAt I j).map_source hyj))
  have hc : ContinuousWithinAt (fiberCoordChange I F V i j) (range I) (extChartAt I j y) := by
    have h := hcc.continuousWithinAt (s := univ)
    rw [← (extChartAt I j).left_inv hyj] at h
    exact h.comp hsymm (mapsTo_univ _ _)
  have hrep : HasFDerivWithinAt (localRep I F s i) L (range I)
      ((extChartAt I i ∘ (extChartAt I j).symm) (extChartAt I j y)) := by
    rwa [Function.comp_apply, (extChartAt I j).left_inv hyj]
  have hcomp : HasFDerivWithinAt
      (fun z ↦ localRep I F s i ((extChartAt I i ∘ (extChartAt I j).symm) z))
      (L.comp (tangentCoordChange I j i y)) (range I) (extChartAt I j y) :=
    hrep.comp _ (hasFDerivWithinAt_tangentCoordChange ⟨hyj, hyi⟩)
      (mapsTo_extChartAt_comp_extChartAt_symm I i j _)
  have hu0 :
      localRep I F s i ((extChartAt I i ∘ (extChartAt I j).symm) (extChartAt I j y)) = 0 := by
    rw [Function.comp_apply, (extChartAt I j).left_inv hyj]
    exact localRep_extChartAt_eq_zero hi hs0
  have hd := HasFDerivWithinAt.clm_apply_of_eq_zero hc hcomp hu0
  rw [fiberCoordChange_extChartAt hj.2] at hd
  exact hd.congr_of_eventuallyEq (localRep_eventuallyEq_fiberCoordChange I F s hi hj)
    (by rw [localRep_extChartAt_eq_zero hj hs0, hu0, map_zero])

/-- At a zero of a section `s` of a topological vector bundle over a `C¹` manifold, having zero
chart derivative within `range I` is independent of the choice of chart and trivialization
containing the point. -/
theorem hasFDerivWithinAt_localRep_zero_iff_of_mem_baseSet [IsManifold I 1 M]
    {s : ∀ x, V x} {i j y : M}
    (hi : y ∈ baseSet (H := H) F V i) (hj : y ∈ baseSet (H := H) F V j)
    (hs0 : s y = 0) :
    HasFDerivWithinAt (localRep I F s i) (0 : E →L[𝕜] F) (range I) (extChartAt I i y) ↔
      HasFDerivWithinAt (localRep I F s j) (0 : E →L[𝕜] F) (range I) (extChartAt I j y) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero] using
      hasFDerivWithinAt_localRep_congr_chart_of_eq_zero hi hj hs0 h
  · simpa only [ContinuousLinearMap.zero_comp, ContinuousLinearMap.comp_zero] using
      hasFDerivWithinAt_localRep_congr_chart_of_eq_zero hj hi hs0 h

section

variable [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]

/-- A first-jet coordinate change at a point in the overlap of both chart domains vanishes only on
the zero jet. -/
theorem coordChange_eq_zero_iff {i j y : M}
    (hi : y ∈ baseSet (H := H) F V i) (hj : y ∈ baseSet (H := H) F V j)
    {v : F × (E →L[𝕜] F)} :
    coordChange I F V i j y v = 0 ↔ v = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, map_zero]⟩
  have := coordChange_comp_apply (I := I) (F := F) (V := V) hi hj hi v
  rw [h, map_zero, coordChange_self_apply hi] at this
  exact this.symm

/-- The first jet of a section at `x` vanishes exactly when the section vanishes at `x` and its
preferred local representative has zero chart derivative within `range I` at `x`. -/
theorem jet_eq_zero_iff {s : ∀ x, V x} {x : M} :
    jet I F s x = 0 ↔
      s x = 0 ∧ fderivWithin 𝕜 (localRep I F s x) (range I) (extChartAt I x x) = 0 := by
  refine (Prod.ext_iff (x := (jet I F s x : F × (E →L[𝕜] F))) (y := (0, 0))).trans ?_
  rw [← value_eq_zero_iff I F x (jet I F s x), value_jet, jet_snd]

/-- A section vanishing at `x` whose local representative has derivative `0` within `range I` at
`x` has zero first jet at `x`. -/
theorem jet_eq_zero_of_hasFDerivWithinAt_zero {s : ∀ x, V x} {x : M} (hs0 : s x = 0)
    (hd : HasFDerivWithinAt (localRep I F s x) (0 : E →L[𝕜] F) (range I) (extChartAt I x x)) :
    jet I F s x = 0 :=
  jet_eq_zero_iff.2 ⟨hs0, hd.fderivWithin
    (I.uniqueDiffOn _ (extChartAt_target_subset_range x (mem_extChartAt_target x)))⟩

/-- For a section differentiable at `x`, its first jet vanishes at `x` exactly when its value is `0`
and its local representative has derivative `0` within `range I` at `x`. -/
theorem jet_eq_zero_iff_hasFDerivWithinAt {s : ∀ x, V x} {x : M}
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun y ↦ TotalSpace.mk' F y (s y)) x) :
    jet I F s x = 0 ↔
      s x = 0 ∧
        HasFDerivWithinAt (localRep I F s x) (0 : E →L[𝕜] F) (range I) (extChartAt I x x) := by
  refine ⟨fun h ↦ ?_, fun ⟨hs0, hd⟩ ↦ jet_eq_zero_of_hasFDerivWithinAt_zero hs0 hd⟩
  obtain ⟨hs0, hfd⟩ := jet_eq_zero_iff.1 h
  refine ⟨hs0, ?_⟩
  rw [← hfd]
  exact (differentiableWithinAt_localRep I F hs (mem_baseSet_self (H := H) F V x)).hasFDerivWithinAt

/-- On a boundaryless manifold, a section differentiable at `x` has zero first jet at `x` exactly
when its value is `0` and its local representative has Fréchet derivative `0` at `x`. -/
theorem jet_eq_zero_iff_hasFDerivAt [I.Boundaryless] {s : ∀ x, V x} {x : M}
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun y ↦ TotalSpace.mk' F y (s y)) x) :
    jet I F s x = 0 ↔
      s x = 0 ∧ HasFDerivAt (localRep I F s x) (0 : E →L[𝕜] F) (extChartAt I x x) := by
  rw [jet_eq_zero_iff_hasFDerivWithinAt hs, ModelWithCorners.range_eq_univ, hasFDerivWithinAt_univ]

/-- **Chart independence of vanishing first jets.** For a section differentiable at `y`, its first
jet vanishes at `y` exactly when `s y = 0` and the chart derivative of its local representative at
any chart and trivialization domain `i` containing `y` vanishes at `y`. -/
theorem jet_eq_zero_iff_of_mem_baseSet {s : ∀ x, V x} {i y : M}
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun x ↦ TotalSpace.mk' F x (s x)) y)
    (hi : y ∈ baseSet (H := H) F V i) :
    jet I F s y = 0 ↔
      s y = 0 ∧ fderivWithin 𝕜 (localRep I F s i) (range I) (extChartAt I i y) = 0 := by
  have hc : coordChange I F V y i y (jet I F s y) = 0 ↔ jet I F s y = 0 :=
    coordChange_eq_zero_iff (mem_baseSet_self (H := H) F V y) hi
  rw [← hc, coordChange_jet I F hs hi, Prod.mk_eq_zero]
  refine and_congr ?_ Iff.rfl
  rw [(trivializationAt F V i).apply_eq_prod_continuousLinearEquivAt 𝕜 y hi.1]
  exact ((trivializationAt F V i).continuousLinearEquivAt 𝕜 y hi.1).map_eq_zero_iff

end

/-- **Multiplying a section by a continuous scalar function at a zero.** If `f : M → 𝕜` is
continuous at `y`, `s y = 0`, and `localRep I F s i` has derivative `L` within `range I` at
`extChartAt I i y`, then `localRep I F (fun m ↦ f m • s m) i` has derivative `f y • L` there.
No differentiability of `f` is needed. -/
theorem hasFDerivWithinAt_localRep_smul_of_eq_zero
    {f : M → 𝕜} {s : ∀ m, V m} {i y : M}
    (hy : y ∈ baseSet (H := H) F V i) (hf : ContinuousAt f y) (hs0 : s y = 0)
    {L : E →L[𝕜] F}
    (hs : HasFDerivWithinAt (localRep I F s i) L (range I) (extChartAt I i y)) :
    HasFDerivWithinAt (localRep I F (fun m ↦ f m • s m) i)
      (f y • L) (range I) (extChartAt I i y) := by
  have hyS : y ∈ (extChartAt I i).source := mem_extChartAt_source_of_mem_baseSet I hy
  have hsymm : ContinuousWithinAt (extChartAt I i).symm (range I) (extChartAt I i y) :=
    (continuousOn_extChartAt_symm i _ ((extChartAt I i).map_source hyS)).mono_of_mem_nhdsWithin
      (extChartAt_target_mem_nhdsWithin_of_mem ((extChartAt I i).map_source hyS))
  let lsm : 𝕜 →L[𝕜] F →L[𝕜] F := ContinuousLinearMap.lsmul 𝕜 𝕜
  have hfc : ContinuousWithinAt (fun z ↦ lsm (f ((extChartAt I i).symm z)))
      (range I) (extChartAt I i y) := by
    have hf' : ContinuousWithinAt (f ∘ (extChartAt I i).symm) (range I) (extChartAt I i y) := by
      have h := hf.continuousWithinAt (s := univ)
      rw [← (extChartAt I i).left_inv hyS] at h
      exact h.comp hsymm (mapsTo_univ _ _)
    exact lsm.continuous.continuousWithinAt.comp hf' (mapsTo_univ _ _)
  have hu0 : localRep I F s i (extChartAt I i y) = 0 := localRep_extChartAt_eq_zero hy hs0
  have hd := HasFDerivWithinAt.clm_apply_of_eq_zero hfc hs hu0
  rw [(extChartAt I i).left_inv hyS] at hd
  have hder : (lsm (f y)).comp L = f y • L := by
    ext v; simp [lsm]
  rw [hder] at hd
  refine hd.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [eventually_extChartAt_symm_mem_baseSet I hy hy.2] with z hz
    rw [localRep_apply, localRep_apply,
      (trivializationAt F V i).apply_eq_prod_continuousLinearEquivAt 𝕜 _ hz.1,
      (trivializationAt F V i).apply_eq_prod_continuousLinearEquivAt 𝕜 _ hz.1, map_smul]
    rfl
  · rw [localRep_extChartAt_eq_zero hy (by rw [hs0, smul_zero]), hu0, map_zero]

/-- Multiplying a section with zero first jet at `x` by a scalar function continuous at `x`
produces a section with zero first jet at `x`. No differentiability of the scalar function is
needed. -/
theorem jet_smul_eq_zero [IsManifold I 1 M] [ContMDiffVectorBundle 1 F V I]
    {f : M → 𝕜} {s : ∀ m, V m} {x : M} (hf : ContinuousAt f x)
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun m ↦ TotalSpace.mk' F m (s m)) x)
    (hjet : jet I F s x = 0) :
    jet I F (fun m ↦ f m • s m) x = 0 := by
  obtain ⟨hs0, hd⟩ := (jet_eq_zero_iff_hasFDerivWithinAt hs).1 hjet
  refine jet_eq_zero_of_hasFDerivWithinAt_zero (by rw [hs0, smul_zero]) ?_
  simpa only [smul_zero] using hasFDerivWithinAt_localRep_smul_of_eq_zero
    (mem_baseSet_self (H := H) F V x) hf hs0 hd

end

section ClmApply

variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂]
  {V₁ : M → Type*} [TopologicalSpace (TotalSpace F₁ V₁)] [∀ x, AddCommGroup (V₁ x)]
  [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)] [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁]
  {V₂ : M → Type*} [TopologicalSpace (TotalSpace F₂ V₂)] [∀ x, AddCommGroup (V₂ x)]
  [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]

/-- **Applying a continuous bundle homomorphism to a section at a zero.** Let `A : Hom(V₁, V₂)` be
continuous at `y` as a section of the Hom bundle, and let `s` be a section of `V₁` with `s y = 0`
whose local representative at `i` has derivative `L` within `range I` at `extChartAt I i y`. Then
the local representative of `m ↦ A m (s m)` has derivative
`(inCoordinates i y i y (A y)).comp L` there. No differentiability of `A` is needed. -/
theorem hasFDerivWithinAt_localRep_clm_apply_of_eq_zero
    {A : ∀ m, V₁ m →L[𝕜] V₂ m} {s : ∀ m, V₁ m} {i y : M}
    (hy₁ : y ∈ baseSet (H := H) F₁ V₁ i) (hy₂ : y ∈ (trivializationAt F₂ V₂ i).baseSet)
    (hA : ContinuousAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) m (A m)) y)
    (hs0 : s y = 0) {L : E →L[𝕜] F₁}
    (hs : HasFDerivWithinAt (localRep I F₁ s i) L (range I) (extChartAt I i y)) :
    HasFDerivWithinAt (localRep I F₂ (fun m ↦ A m (s m)) i)
      ((ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ i y i y (A y)).comp L)
      (range I) (extChartAt I i y) := by
  let eH := trivializationAt (F₁ →L[𝕜] F₂) (fun m ↦ V₁ m →L[𝕜] V₂ m) i
  have hyH : y ∈ eH.baseSet := by
    rw [hom_trivializationAt_baseSet (RingHom.id 𝕜) i]
    exact ⟨hy₁.1, hy₂⟩
  have hyS : y ∈ (extChartAt I i).source := mem_extChartAt_source_of_mem_baseSet I hy₁
  have hAe : ContinuousAt (fun m ↦ (eH ⟨m, A m⟩).2) y :=
    ((eH.continuousOn.continuousAt (eH.open_source.mem_nhds (eH.mem_source.2 hyH))).comp hA).snd
  have hcoord : ContinuousAt
      (fun m ↦ ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ i m i m (A m)) y := by
    refine hAe.congr (Eventually.of_forall fun m ↦ ?_)
    exact congrArg Prod.snd
      (hom_trivializationAt_apply (F₁ := F₁) (E₁ := V₁) (F₂ := F₂) (E₂ := V₂) (σ := RingHom.id 𝕜)
        i ⟨m, A m⟩)
  have hsymm : ContinuousWithinAt (extChartAt I i).symm (range I) (extChartAt I i y) :=
    (continuousOn_extChartAt_symm i _ ((extChartAt I i).map_source hyS)).mono_of_mem_nhdsWithin
      (extChartAt_target_mem_nhdsWithin_of_mem ((extChartAt I i).map_source hyS))
  have hc : ContinuousWithinAt
      (fun z ↦ ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ i
        ((extChartAt I i).symm z) i ((extChartAt I i).symm z) (A ((extChartAt I i).symm z)))
      (range I) (extChartAt I i y) := by
    have h := hcoord.continuousWithinAt (s := univ)
    rw [← (extChartAt I i).left_inv hyS] at h
    exact h.comp hsymm (mapsTo_univ _ _)
  have hu0 : localRep I F₁ s i (extChartAt I i y) = 0 := localRep_extChartAt_eq_zero hy₁ hs0
  have hd := HasFDerivWithinAt.clm_apply_of_eq_zero hc hs hu0
  rw [(extChartAt I i).left_inv hyS] at hd
  refine hd.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [eventually_extChartAt_symm_mem_baseSet I hy₁ hy₁.2,
      mem_nhdsWithin_of_mem_nhds (extChartAt_preimage_mem_nhds' hyS
        ((trivializationAt F₂ V₂ i).open_baseSet.mem_nhds hy₂))] with z hz₁ hz₂
    rw [localRep_apply, localRep_apply,
      ContinuousLinearMap.inCoordinates_eq hz₁.1 hz₂, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.comp_apply,
      (trivializationAt F₁ V₁ i).apply_eq_prod_continuousLinearEquivAt 𝕜 _ hz₁.1,
      (trivializationAt F₂ V₂ i).apply_eq_prod_continuousLinearEquivAt 𝕜 _ hz₂]
    simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]
  · rw [localRep_extChartAt_eq_zero ⟨hy₂, hy₁.2⟩ (by rw [hs0, map_zero]), hu0, map_zero]

/-- Applying a continuous bundle homomorphism `A : Hom(V₁, V₂)` to a section with zero first jet
at `x` produces a section with zero first jet at `x`. No differentiability of `A` is needed. -/
theorem jet_clm_apply_eq_zero [IsManifold I 1 M]
    [ContMDiffVectorBundle 1 F₁ V₁ I] [ContMDiffVectorBundle 1 F₂ V₂ I]
    {A : ∀ m, V₁ m →L[𝕜] V₂ m} {s : ∀ m, V₁ m} {x : M}
    (hA : ContinuousAt (fun m ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) m (A m)) x)
    (hs : MDifferentiableAt I (I.prod 𝓘(𝕜, F₁)) (fun m ↦ TotalSpace.mk' F₁ m (s m)) x)
    (hjet : jet I F₁ s x = 0) :
    jet I F₂ (fun m ↦ A m (s m)) x = 0 := by
  obtain ⟨hs0, hd⟩ := (jet_eq_zero_iff_hasFDerivWithinAt hs).1 hjet
  refine jet_eq_zero_of_hasFDerivWithinAt_zero (by rw [hs0, map_zero]) ?_
  simpa only [ContinuousLinearMap.comp_zero] using hasFDerivWithinAt_localRep_clm_apply_of_eq_zero
    (mem_baseSet_self (H := H) F₁ V₁ x) (mem_baseSet_trivializationAt F₂ V₂ x) hA hs0 hd

end ClmApply

end Vanishing

section Trivial

section

variable [TopologicalSpace F]

/-- For the trivial bundle over a model space, the local representative of a section is the
section itself. -/
@[simp]
theorem localRep_trivial (s : ∀ x : E, Bundle.Trivial E F x) (x : E) :
    localRep 𝓘(𝕜, E) F s x = s := by
  funext z
  simp [localRep_apply]

end

variable [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- For the trivial bundle over a model space, the value coordinate of a first jet is the value
of the section. -/
theorem jet_trivial_fst (s : ∀ x : E, Bundle.Trivial E F x) (x : E) :
    (jet 𝓘(𝕜, E) F s x).1 = s x := by
  simp

/-- For the trivial bundle over a model space, the derivative coordinate of a first jet is the
Fréchet derivative of the section. -/
theorem jet_trivial_snd (s : ∀ x : E, Bundle.Trivial E F x) (x : E) :
    (jet 𝓘(𝕜, E) F s x).2 = fderiv 𝕜 s x := by
  simp [fderivWithin_univ]

end Trivial

end FirstJetBundle

end TauCeti
