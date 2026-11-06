/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import TauCeti.Geometry.Manifold.IsManifold.InteriorChart

/-!
# Vector-space charts on a boundaryless manifold

`BoundarylessModel I M` carries the topology of `M`, but its charts take values in the
model vector space `E` rather than in `H`. A chart `c` is replaced by `I ∘ c`, restricted to the
points whose coordinates lie in the interior of `range I`. For a boundaryless manifold these
charts cover the carrier, even when the model itself has unused boundary points.
The extended coordinate functions and their
inverses do not change, and the identity is a diffeomorphism.

This lets constructions stated for self-modelled manifolds apply to boundaryless manifolds with
arbitrary models without installing a second atlas on the original manifold. In particular, local
normal forms and implicit-function constructions can retain their actual coordinates.

## Main definitions and results

* `BoundarylessModel.chart`, `atlas_eq`, `chartAt_eq`: the transported atlas.
* `BoundarylessModel.extChartAt_apply`, `extChartAt_symm_apply`: preferred coordinate comparisons.
* `BoundarylessModel.diffeomorph`: the identity diffeomorphism for a boundaryless carrier.
* `BoundarylessModel.mdifferentiableAt_source_iff`, `mdifferentiableAt_target_iff`,
  `mfderiv_source`, `mfderiv_target`, `mfderiv_source_eq_zero_iff`: differentiability and derivative
  comparisons.
* `BoundarylessModel.originalChart`, `chart_toPartialEquiv`, `chart_originalChart`,
  `originalChart_chart`, `originalChart_extend`, `originalChart_source`,
  `originalChart_extend_apply`, `originalChart_extend_symm_apply`, `originalChart_extend_target`,
  `chart_source_of_boundaryless`, `chart_target_of_boundaryless`,
  `extChartAt_eq`, `chart_mem_maximalAtlas_iff`, `originalChart_mem_maximalAtlas_iff`: full-chart
  roundtrips when the model itself is boundaryless.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013),
  Chapter 1 (Smooth Manifolds), Proposition 1.17, Lemma 1.35 and Proposition 1.38(a,c),
  pp. 13–14, 21–22, 27.
-/

public section

open Function Set
open scoped Topology ContDiff Manifold

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]

/-- A copy of a manifold whose charts take values in the vector space of its model `I`.
The transported atlas requires `BoundarylessManifold I M`. The topology is unchanged; the
original manifold retains its original atlas. -/
-- The exported carrier and chart equalities require this body under Lean's module system.
@[expose] def BoundarylessModel (_I : ModelWithCorners 𝕜 E H) (M : Type*) := M

namespace BoundarylessModel

variable (I : ModelWithCorners 𝕜 E H) (M : Type*) [TopologicalSpace M]

/-- The model copy inherits the topology of the original manifold. -/
instance : TopologicalSpace (BoundarylessModel I M) := inferInstanceAs (TopologicalSpace M)

/-- The identity homeomorphism to the copy with vector-space-valued charts. -/
def homeomorph : M ≃ₜ BoundarylessModel I M where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/-- The carrier map of the homeomorphism is the identity. -/
theorem coe_homeomorph : ⇑(homeomorph I M) = id :=
  (rfl)

/-- The inverse carrier map is also the identity. -/
theorem coe_homeomorph_symm : ⇑(homeomorph I M).symm = id :=
  (rfl)

/-- The homeomorphism sends each point to the same point of the model copy. -/
@[simp]
theorem homeomorph_apply (x : M) : homeomorph I M x = x :=
  (rfl)

/-- The inverse homeomorphism sends each point back to the same original point. -/
@[simp]
theorem homeomorph_symm_apply (x : BoundarylessModel I M) :
    (homeomorph I M).symm x = x :=
  (rfl)

variable {M}

/-- Replace a chart by its vector-space coordinates over the interior of the model range. -/
noncomputable def chart (c : OpenPartialHomeomorph M H) :
    OpenPartialHomeomorph (BoundarylessModel I M) E := c.trans I.interiorChart

/-- The transported chart has the original extended coordinates. -/
@[simp]
theorem chart_apply (c : OpenPartialHomeomorph M H) (x : BoundarylessModel I M) :
    chart I c x = I (c ((homeomorph I M).symm x)) := by
  rw [homeomorph_symm_apply]
  calc
    chart I c x = I.interiorChart (c x) :=
      congrFun (OpenPartialHomeomorph.coe_trans c I.interiorChart) x
    _ = I (c x) := congrFun (ModelWithCorners.interiorChart_coe (I := I)) (c x)

/-- The inverse transported chart has the original inverse extended coordinates. -/
@[simp]
theorem chart_symm_apply (c : OpenPartialHomeomorph M H) (v : E) :
    (chart I c).symm v = homeomorph I M (c.symm (I.symm v)) := by
  rw [homeomorph_apply]
  exact (congrFun (OpenPartialHomeomorph.coe_trans_symm c I.interiorChart) v).trans
    (congrArg c.symm (congrFun (ModelWithCorners.interiorChart_coe_symm (I := I)) v))

/-- The transported source consists of the original chart points with interior coordinates. -/
theorem chart_source (c : OpenPartialHomeomorph M H) :
    (chart I c).source = (homeomorph I M).symm ⁻¹' c.source ∩
      (fun x => I (c ((homeomorph I M).symm x))) ⁻¹' interior (range I) := by
  rw [coe_homeomorph_symm]
  -- Both carriers have the original topology; normalize them before the composition law.
  change (c.trans I.interiorChart).source =
    c.source ∩ (fun x : M => I (c x)) ⁻¹' interior (range I)
  simpa only [ModelWithCorners.interiorChart_source, ← preimage_comp,
    Function.comp_def] using
    (OpenPartialHomeomorph.trans_source c I.interiorChart)

/-- The transported target is the interior part of the original extended chart target. -/
theorem chart_target (c : OpenPartialHomeomorph M H) :
    (chart I c).target = interior (range I) ∩ I.symm ⁻¹' c.target := by
  simp only [chart, OpenPartialHomeomorph.trans_target, ModelWithCorners.interiorChart_target,
    ModelWithCorners.interiorChart_coe_symm]

private theorem chart_trans_source_subset (c d : OpenPartialHomeomorph M H) :
    ((chart I c).symm.trans (chart I d)).source ⊆
      I.symm ⁻¹' (c.symm.trans d).source ∩ range I := by
  intro v hv
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    chart_target, chart_source, mem_inter_iff, mem_preimage, chart_symm_apply,
    homeomorph_apply, homeomorph_symm_apply] at hv ⊢
  exact ⟨⟨hv.1.2, hv.2.1⟩, interior_subset hv.1.1⟩

private theorem chart_trans_coe (c d : OpenPartialHomeomorph M H) :
    (((chart I c).symm.trans (chart I d)) : E → E) =
      I ∘ (c.symm.trans d) ∘ I.symm := by
  funext v
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply, chart_apply,
    chart_symm_apply, Homeomorph.symm_apply_apply]

private theorem original_chart_trans_mem_contDiffGroupoid_iff_contDiffOn
    (c d : OpenPartialHomeomorph M H) (n : ℕ∞ω) :
    c.symm.trans d ∈ contDiffGroupoid n I ↔
      ContDiffOn 𝕜 n (I ∘ (c.symm.trans d) ∘ I.symm)
          (I.symm ⁻¹' (c.symm.trans d).source ∩ range I) ∧
        ContDiffOn 𝕜 n (I ∘ (d.symm.trans c) ∘ I.symm)
          (I.symm ⁻¹' (d.symm.trans c).source ∩ range I) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  -- The pregroupoid property is smoothness in the model coordinates, in both directions.
  rfl

private theorem chart_trans_mem_contDiffGroupoid_iff_contDiffOn
    (c d : OpenPartialHomeomorph M H) (n : ℕ∞ω) :
    (chart I c).symm.trans (chart I d) ∈ contDiffGroupoid n 𝓘(𝕜, E) ↔
      ContDiffOn 𝕜 n ((chart I c).symm.trans (chart I d)).toPartialEquiv
          ((chart I c).symm.trans (chart I d)).source ∧
        ContDiffOn 𝕜 n ((chart I d).symm.trans (chart I c)).toPartialEquiv
          ((chart I d).symm.trans (chart I c)).source := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
  -- The self-model has identity coordinate maps and full range.
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id,
    preimage_id_eq, range_id, inter_univ]
  rfl

private theorem chart_trans_mem_contDiffGroupoid {n : ℕ∞ω}
    (c d : OpenPartialHomeomorph M H) (h : c.symm.trans d ∈ contDiffGroupoid n I) :
    (chart I c).symm.trans (chart I d) ∈ contDiffGroupoid n 𝓘(𝕜, E) := by
  obtain ⟨hforward, hbackward⟩ :=
    (original_chart_trans_mem_contDiffGroupoid_iff_contDiffOn I c d n).1 h
  rw [chart_trans_mem_contDiffGroupoid_iff_contDiffOn]
  constructor
  · simpa only [OpenPartialHomeomorph.coe_toPartialEquiv, chart_trans_coe] using
      hforward.mono (chart_trans_source_subset I c d)
  · simpa only [OpenPartialHomeomorph.coe_toPartialEquiv, chart_trans_coe] using
      hbackward.mono (chart_trans_source_subset I d c)

section BoundarylessModelCharts

variable [I.Boundaryless]

/-- For a boundaryless model, the transported chart has the whole original source. -/
@[simp]
theorem chart_source_of_boundaryless (c : OpenPartialHomeomorph M H) :
    (chart I c).source = (homeomorph I M).symm ⁻¹' c.source := by
  simp only [chart_source, I.range_eq_univ, interior_univ, preimage_univ, inter_univ]

/-- For a boundaryless model, the transported chart has the whole extended target. -/
@[simp]
theorem chart_target_of_boundaryless (c : OpenPartialHomeomorph M H) :
    (chart I c).target = I.symm ⁻¹' c.target := by
  simp only [chart_target, I.range_eq_univ, interior_univ, univ_inter]

private theorem chart_eq_trans_toHomeomorph (c : OpenPartialHomeomorph M H) :
    chart I c = c.trans I.toHomeomorph.toOpenPartialHomeomorph := by
  have h : I.interiorChart = I.toHomeomorph.toOpenPartialHomeomorph := by
    apply OpenPartialHomeomorph.ext
    · intro x
      exact congrFun ModelWithCorners.interiorChart_coe x
    · intro x
      exact congrFun ModelWithCorners.interiorChart_coe_symm x
    · simp only [ModelWithCorners.interiorChart_source, I.range_eq_univ, interior_univ,
        preimage_univ, Homeomorph.toOpenPartialHomeomorph_source]
  exact congrArg c.trans h

/-- The new chart has exactly the old extended partial equivalence. The carrier and topology
of the copy are definitionally those of `M`, so the two partial equivalences have the same type. -/
theorem chart_toPartialEquiv (c : OpenPartialHomeomorph M H) :
    (chart I c).toPartialEquiv = c.extend I := by
  rw [chart_eq_trans_toHomeomorph]
  apply PartialEquiv.ext
  · intro x; rfl
  · intro x; rfl
  · simp only [OpenPartialHomeomorph.trans_source,
      Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ,
      OpenPartialHomeomorph.extend_source]
    rfl

/-- Return a vector-space-valued chart on the copy to the original model. -/
def originalChart (φ : OpenPartialHomeomorph (BoundarylessModel I M) E) :
    OpenPartialHomeomorph M H :=
  φ.trans I.toHomeomorph.symm.toOpenPartialHomeomorph

/-- Returning a chart to the original model and extending it again recovers the same chart. -/
@[simp]
theorem chart_originalChart (φ : OpenPartialHomeomorph (BoundarylessModel I M) E) :
    chart I (originalChart I φ) = φ := by
  -- Both sides use the copied topology; expose that carrier for the composition laws.
  rw [chart_eq_trans_toHomeomorph]
  change (φ.trans I.toHomeomorph.symm.toOpenPartialHomeomorph).trans
    I.toHomeomorph.toOpenPartialHomeomorph = φ
  simp [OpenPartialHomeomorph.trans_assoc]

/-- Extending an original chart and returning it to its model recovers the original chart. -/
@[simp]
theorem originalChart_chart (c : OpenPartialHomeomorph M H) :
    originalChart I (chart I c) = c := by
  -- Use the original topology instance throughout the composition.
  rw [chart_eq_trans_toHomeomorph]
  change (c.trans I.toHomeomorph.toOpenPartialHomeomorph).trans
    I.toHomeomorph.symm.toOpenPartialHomeomorph = c
  simp [OpenPartialHomeomorph.trans_assoc]

/-- An arbitrary chart on the copy and its corresponding original chart have identical
extended coordinates, source and target. -/
theorem originalChart_extend (φ : OpenPartialHomeomorph (BoundarylessModel I M) E) :
    (originalChart I φ).extend I = φ.toPartialEquiv := by
  rw [← chart_toPartialEquiv, chart_originalChart]

/-- A chart of the copy and the corresponding original chart have the same source. -/
@[simp]
theorem originalChart_source (φ : OpenPartialHomeomorph (BoundarylessModel I M) E) :
    (originalChart I φ).source = homeomorph I M ⁻¹' φ.source := by
  ext y
  rw [mem_preimage, homeomorph_apply, ← OpenPartialHomeomorph.extend_source (I := I),
    originalChart_extend]
  -- The extended chart's source is the chart's source, over the copy's carrier `M`.
  rfl

/-- The extended original chart of a chart of the copy has the same coordinates. -/
theorem originalChart_extend_apply (φ : OpenPartialHomeomorph (BoundarylessModel I M) E)
    (y : M) : (originalChart I φ).extend I y = φ (homeomorph I M y) := by
  rw [originalChart_extend, homeomorph_apply]
  -- Coercing the partial equivalence is coercing the chart; the carriers agree definitionally.
  rfl

/-- The extended original chart of a chart of the copy has the same inverse. -/
theorem originalChart_extend_symm_apply (φ : OpenPartialHomeomorph (BoundarylessModel I M) E)
    (v : E) : ((originalChart I φ).extend I).symm v = (homeomorph I M).symm (φ.symm v) := by
  rw [originalChart_extend, homeomorph_symm_apply]
  -- As above, now for the inverse chart.
  rfl

/-- The extended original chart of a chart of the copy has the same target. -/
theorem originalChart_extend_target (φ : OpenPartialHomeomorph (BoundarylessModel I M) E) :
    ((originalChart I φ).extend I).target = φ.target := by
  rw [originalChart_extend]

private theorem chart_trans_toPartialEquiv (c d : OpenPartialHomeomorph M H) :
    ((chart I c).symm.trans (chart I d)).toPartialEquiv = I.extendCoordChange c d := by
  rw [ModelWithCorners.extendCoordChange, OpenPartialHomeomorph.trans_toPartialEquiv,
    OpenPartialHomeomorph.symm_toPartialEquiv, chart_toPartialEquiv, chart_toPartialEquiv]
  rfl

private theorem chart_trans_mem_contDiffGroupoid_iff (c d : OpenPartialHomeomorph M H)
    (n : ℕ∞ω) :
    (chart I c).symm.trans (chart I d) ∈ contDiffGroupoid n 𝓘(𝕜, E) ↔
      c.symm.trans d ∈ contDiffGroupoid n I := by
  rw [chart_trans_mem_contDiffGroupoid_iff_contDiffOn,
    original_chart_trans_mem_contDiffGroupoid_iff_contDiffOn]
  rw [chart_trans_toPartialEquiv, chart_trans_toPartialEquiv]
  simp only [I.extendCoordChange_source, I.image_eq]
  -- An extended transition is I ∘ (d ∘ c.symm) ∘ I.symm, in both directions.
  rfl

end BoundarylessModelCharts

variable [ChartedSpace H M] [BoundarylessManifold I M]

/-- The model copy receives the atlas obtained by extending the original charts to `E`. -/
noncomputable instance : ChartedSpace E (BoundarylessModel I M) where
  atlas := chart I '' atlas H M
  chartAt x := chart I (chartAt H ((homeomorph I M).symm x))
  mem_chart_source x := by
    rw [chart_source]
    exact ⟨mem_chart_source H ((homeomorph I M).symm x),
      BoundarylessManifold.isInteriorPoint (I := I) (x := (homeomorph I M).symm x)⟩
  chart_mem_atlas x := mem_image_of_mem _ (chart_mem_atlas H _)

/-- The atlas consists of the extended original charts. -/
theorem atlas_eq : atlas E (BoundarylessModel I M) = chart I '' atlas H M :=
  (rfl)

/-- Preferred charts are transported without making any new choices. -/
theorem chartAt_eq (x : BoundarylessModel I M) :
    chartAt E x = chart I (chartAt H ((homeomorph I M).symm x)) :=
  (rfl)

/-- The preferred chart of the copy has the coordinates of the preferred extended chart. -/
theorem chartAt_apply (z y : BoundarylessModel I M) :
    chartAt E z y = extChartAt I ((homeomorph I M).symm z) ((homeomorph I M).symm y) := by
  rw [chartAt_eq, chart_apply, extChartAt_coe, comp_apply]

/-- The inverse preferred chart of the copy is the inverse preferred extended chart. -/
theorem chartAt_symm_apply (z : BoundarylessModel I M) (v : E) :
    (homeomorph I M).symm ((chartAt E z).symm v) =
      (extChartAt I ((homeomorph I M).symm z)).symm v := by
  rw [chartAt_eq, chart_symm_apply, Homeomorph.symm_apply_apply, extChartAt_coe_symm, comp_apply]

/-- Transport to the vector-space model preserves every degree of manifold regularity. -/
noncomputable instance {n : ℕ∞ω} [IsManifold I n M] :
    IsManifold 𝓘(𝕜, E) n (BoundarylessModel I M) where
  compatible := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact chart_trans_mem_contDiffGroupoid I c d ((contDiffGroupoid n I).compatible hc hd)

/-- The preferred extended chart has the same coordinate function after transport. -/
theorem extChartAt_apply (x y : BoundarylessModel I M) :
    extChartAt 𝓘(𝕜, E) x y = extChartAt I ((homeomorph I M).symm x)
      ((homeomorph I M).symm y) := by
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply, id_eq,
    chartAt_eq, chart_apply]

/-- The preferred extended chart has the same inverse function after transport. -/
theorem extChartAt_symm_apply (x : BoundarylessModel I M) (v : E) :
    (homeomorph I M).symm ((extChartAt 𝓘(𝕜, E) x).symm v) =
      (extChartAt I ((homeomorph I M).symm x)).symm v := by
  simp only [extChartAt_coe_symm, modelWithCornersSelf_coe_symm, Function.comp_apply, id_eq,
    chartAt_eq, chart_symm_apply, Homeomorph.symm_apply_apply]

section BoundarylessModelAtlas

variable [I.Boundaryless]

/-- The extended preferred chart is unchanged by the model transport. -/
theorem extChartAt_eq (x : BoundarylessModel I M) :
    extChartAt 𝓘(𝕜, E) x = extChartAt I ((homeomorph I M).symm x) := by
  rw [extChartAt, chartAt_eq]
  rw [OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv, PartialEquiv.trans_refl,
    chart_toPartialEquiv]
  rfl

/-- Membership in the maximal atlas is preserved by extending a chart to the vector space. -/
@[simp]
theorem chart_mem_maximalAtlas_iff (c : OpenPartialHomeomorph M H) (n : ℕ∞ω) :
    chart I c ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n (BoundarylessModel I M) ↔
      c ∈ IsManifold.maximalAtlas I n M := by
  simp only [IsManifold.maximalAtlas, mem_maximalAtlas_iff, atlas_eq,
    forall_mem_image, chart_trans_mem_contDiffGroupoid_iff]

/-- Every maximal chart on the copy corresponds to a maximal chart on the original manifold. -/
@[simp]
theorem originalChart_mem_maximalAtlas_iff
    (φ : OpenPartialHomeomorph (BoundarylessModel I M) E) (n : ℕ∞ω) :
    originalChart I φ ∈ IsManifold.maximalAtlas I n M ↔
      φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n (BoundarylessModel I M) := by
  rw [← chart_mem_maximalAtlas_iff, chart_originalChart]

end BoundarylessModelAtlas

private theorem range_mem_nhds_extChartAt (x : BoundarylessModel I M) :
    range I ∈ 𝓝 (extChartAt I ((homeomorph I M).symm x) ((homeomorph I M).symm x)) :=
  range_mem_nhds_isInteriorPoint
    (BoundarylessManifold.isInteriorPoint (I := I) (x := (homeomorph I M).symm x))

/-- The identity is a diffeomorphism from a boundaryless manifold to its vector-model copy. -/
noncomputable def diffeomorph (n : ℕ∞ω) :
    Diffeomorph I 𝓘(𝕜, E) M (BoundarylessModel I M) n where
  toEquiv := (homeomorph I M).toEquiv
  contMDiff_toFun := by
    -- The coercion lemma coe_diffeomorph is not available inside its own definition.
    -- Present the equivalence field using the already defined identity homeomorphism.
    change ContMDiff I 𝓘(𝕜, E) n (homeomorph I M)
    intro x
    have hcoord : writtenInExtChartAt I 𝓘(𝕜, E) x (homeomorph I M) =
        writtenInExtChartAt I I x id := by
      funext v
      simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_apply,
        Homeomorph.symm_apply_apply, id_eq]
    have h := (contMDiff_id : ContMDiff I I n (id : M → M)) x
    rw [contMDiffAt_iff] at h ⊢
    refine ⟨(homeomorph I M).continuous.continuousAt, ?_⟩
    -- simp unfolds writtenInExtChartAt; change folds the anonymous coordinate composition.
    change ContDiffWithinAt 𝕜 n (writtenInExtChartAt I 𝓘(𝕜, E) x (homeomorph I M)) _ _
    rw [hcoord]
    exact h.2
  contMDiff_invFun := by
    -- The coercion lemma coe_diffeomorph is not available inside its own definition.
    -- Present the equivalence field using the already defined identity homeomorphism.
    change ContMDiff 𝓘(𝕜, E) I n (homeomorph I M).symm
    intro x
    have hcoord : writtenInExtChartAt 𝓘(𝕜, E) I x (homeomorph I M).symm =
        writtenInExtChartAt I I ((homeomorph I M).symm x) id := by
      funext v
      simp only [writtenInExtChartAt, Function.comp_apply, extChartAt_symm_apply, id_eq]
    have h := (contMDiff_id : ContMDiff I I n (id : M → M)) ((homeomorph I M).symm x)
    rw [contMDiffAt_iff] at h ⊢
    refine ⟨(homeomorph I M).symm.continuous.continuousAt, ?_⟩
    -- simp unfolds writtenInExtChartAt; change folds the anonymous coordinate composition.
    change ContDiffWithinAt 𝕜 n (writtenInExtChartAt 𝓘(𝕜, E) I x (homeomorph I M).symm) _ _
    rw [hcoord, extChartAt_apply]
    -- The inverse has native source range univ, whereas h.2 is smooth within range I.
    -- This range is a neighborhood at an interior point, so upgrade to ContDiffAt.
    -- The forward map already has range I as its source set and needs no upgrade.
    have hh := h.2.contDiffAt (range_mem_nhds_extChartAt I x)
    exact hh.contDiffWithinAt

/-- The diffeomorphism has the underlying identity homeomorphism. -/
@[simp]
theorem coe_diffeomorph (n : ℕ∞ω) :
    ⇑(diffeomorph I (M := M) n) = homeomorph I M :=
  (rfl)

/-- The inverse diffeomorphism has the inverse identity homeomorphism. -/
@[simp]
theorem coe_diffeomorph_symm (n : ℕ∞ω) :
    ⇑(diffeomorph I (M := M) n).symm = (homeomorph I M).symm :=
  (rfl)

section Derivatives

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] (J : ModelWithCorners 𝕜 E' H')
  [TopologicalSpace N] [ChartedSpace H' N]

private theorem writtenInExtChartAt_source (f : M → N) (x : BoundarylessModel I M) :
    writtenInExtChartAt 𝓘(𝕜, E) J x (f ∘ (homeomorph I M).symm) =
      writtenInExtChartAt I J ((homeomorph I M).symm x) f := by
  funext v
  simp only [writtenInExtChartAt, comp_apply, extChartAt_symm_apply]

private theorem writtenInExtChartAt_target (f : N → M) (x : N) :
    writtenInExtChartAt J 𝓘(𝕜, E) x (homeomorph I M ∘ f) =
      writtenInExtChartAt J I x f := by
  funext v
  simp only [writtenInExtChartAt, comp_apply, extChartAt_apply, Homeomorph.symm_apply_apply]

/-- Changing the source model preserves differentiability, even when no manifold regularity
assumption is imposed on either atlas. -/
@[simp]
theorem mdifferentiableAt_source_iff (f : M → N) (x : BoundarylessModel I M) :
    MDifferentiableAt 𝓘(𝕜, E) J (f ∘ (homeomorph I M).symm) x ↔
      MDifferentiableAt I J f ((homeomorph I M).symm x) := by
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff, writtenInExtChartAt_source,
    extChartAt_apply, ModelWithCorners.range_eq_univ]
  rw [differentiableWithinAt_univ]
  refine and_congr ((homeomorph I M).symm.comp_continuousAt_iff' f x) ⟨
    DifferentiableAt.differentiableWithinAt, fun h ↦ ?_⟩
  exact h.differentiableAt (range_mem_nhds_extChartAt I x)

-- The coordinate derivative is unchanged: both the written map and evaluation point agree
-- by the preferred-coordinate comparison, and the model range is a neighborhood of the point.
-- Keep this separate from tangent casts.
private theorem fderivWithin_writtenInExtChartAt_source (f : M → N)
    (x : BoundarylessModel I M) :
    fderivWithin 𝕜 (writtenInExtChartAt 𝓘(𝕜, E) J x (f ∘ (homeomorph I M).symm))
        (range 𝓘(𝕜, E)) (extChartAt 𝓘(𝕜, E) x x) =
      fderivWithin 𝕜 (writtenInExtChartAt I J ((homeomorph I M).symm x) f)
        (range I) (extChartAt I ((homeomorph I M).symm x) ((homeomorph I M).symm x)) := by
  rw [writtenInExtChartAt_source, extChartAt_apply, ModelWithCorners.range_eq_univ,
    fderivWithin_univ, fderivWithin_of_mem_nhds (range_mem_nhds_extChartAt I x)]

/-- The source-side derivative comparison, with the tangent spaces identified explicitly
through their common model vector space. No differentiability hypothesis is needed. -/
theorem mfderiv_source (f : M → N) (x : BoundarylessModel I M) :
    mfderiv 𝓘(𝕜, E) J (f ∘ (homeomorph I M).symm) x =
      mfderiv I J f ((homeomorph I M).symm x) ∘L
        (tangentSpaceCastModel I ((homeomorph I M).symm x)).symm.toContinuousLinearMap ∘L
        (tangentSpaceCastModel 𝓘(𝕜, E) x).toContinuousLinearMap := by
  by_cases h : MDifferentiableAt I J f ((homeomorph I M).symm x)
  · have h' := (mdifferentiableAt_source_iff I J f x).2 h
    rw [h'.mfderiv, h.mfderiv, fderivWithin_writtenInExtChartAt_source]
    -- Only the inverse tangent identifications cancel; no tangent-space definitions unfold.
    ext v
    simp only [comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
  · rw [mfderiv_zero_of_not_mdifferentiableAt
        (fun h' ↦ h ((mdifferentiableAt_source_iff I J f x).1 h')),
      mfderiv_zero_of_not_mdifferentiableAt h]
    simp only [ContinuousLinearMap.zero_comp]

/-- Changing the source model does not change whether the derivative vanishes. -/
@[simp]
theorem mfderiv_source_eq_zero_iff (f : M → N) (x : BoundarylessModel I M) :
    mfderiv 𝓘(𝕜, E) J (f ∘ (homeomorph I M).symm) x = 0 ↔
      mfderiv I J f ((homeomorph I M).symm x) = 0 := by
  rw [mfderiv_source]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, ContinuousLinearMap.zero_comp]⟩
  ext v
  -- Evaluate at a vector transported by the inverse tangent identification to cancel the casts.
  simpa using congrArg (fun L ↦ L ((tangentSpaceCastModel 𝓘(𝕜, E) x).symm
    (tangentSpaceCastModel I ((homeomorph I M).symm x) v))) h

/-- Changing the target model preserves differentiability. -/
@[simp]
theorem mdifferentiableAt_target_iff (f : N → M) (x : N) :
    MDifferentiableAt J 𝓘(𝕜, E) ((homeomorph I M) ∘ f) x ↔
      MDifferentiableAt J I f x := by
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff]
  rw [writtenInExtChartAt_target]
  exact and_congr ((homeomorph I M).comp_continuousAt_iff f x) Iff.rfl

-- Target transport leaves the coordinate derivative unchanged, before identifying tangent spaces.
private theorem fderivWithin_writtenInExtChartAt_target (f : N → M) (x : N) :
    fderivWithin 𝕜 (writtenInExtChartAt J 𝓘(𝕜, E) x ((homeomorph I M) ∘ f))
        (range J) (extChartAt J x x) =
      fderivWithin 𝕜 (writtenInExtChartAt J I x f) (range J) (extChartAt J x x) := by
  rw [writtenInExtChartAt_target]

/-- The target-side derivative comparison through the common model vector space. -/
theorem mfderiv_target (f : N → M) (x : N) :
    mfderiv J 𝓘(𝕜, E) ((homeomorph I M) ∘ f) x =
      (tangentSpaceCastModel 𝓘(𝕜, E) (homeomorph I M (f x))).symm.toContinuousLinearMap ∘L
        (tangentSpaceCastModel I (f x)).toContinuousLinearMap ∘L mfderiv J I f x := by
  by_cases h : MDifferentiableAt J I f x
  · have h' := (mdifferentiableAt_target_iff I J f x).2 h
    rw [h'.mfderiv, h.mfderiv, fderivWithin_writtenInExtChartAt_target]
    -- Only the inverse tangent identifications cancel; no tangent-space definitions unfold.
    ext v
    simp only [comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
  · rw [mfderiv_zero_of_not_mdifferentiableAt
        (fun h' ↦ h ((mdifferentiableAt_target_iff I J f x).1 h')),
      mfderiv_zero_of_not_mdifferentiableAt h]
    simp only [ContinuousLinearMap.comp_zero]

end Derivatives

end BoundarylessModel

end TauCeti
