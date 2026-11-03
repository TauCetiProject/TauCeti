/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Replacing a boundaryless model by its vector space

`BoundarylessModel I M` carries the topology of `M`, but its charts take values in the
model vector space `E` rather than in `H`. A chart `c` is replaced by `I ∘ c`.
The extended charts do not change, and the identity is a diffeomorphism.

This lets constructions stated for self-modelled manifolds apply to arbitrary boundaryless
models without installing a second atlas on the original manifold. In particular, local
normal forms and implicit-function constructions can retain their actual coordinates.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]

/-- A copy of a manifold on which the charts of a boundaryless model `I` take values in its
vector space. The topology is unchanged; the original manifold retains its original atlas. -/
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

variable {M} [I.Boundaryless]

/-- Replace an `H`-valued chart by its `E`-valued extended coordinates. -/
def chart (c : OpenPartialHomeomorph M H) : OpenPartialHomeomorph (BoundarylessModel I M) E :=
  c.trans I.toHomeomorph.toOpenPartialHomeomorph

@[simp]
theorem chart_apply (c : OpenPartialHomeomorph M H) (y : BoundarylessModel I M) :
    chart I c y = I (c ((homeomorph I M).symm y)) :=
  (rfl)

@[simp]
theorem chart_symm_apply (c : OpenPartialHomeomorph M H) (v : E) :
    (chart I c).symm v = homeomorph I M (c.symm (I.symm v)) :=
  (rfl)

@[simp]
theorem chart_source (c : OpenPartialHomeomorph M H) :
    (chart I c).source = (homeomorph I M).symm ⁻¹' c.source := by
  simp only [chart, OpenPartialHomeomorph.trans_source,
    Homeomorph.toOpenPartialHomeomorph_source, preimage_univ, inter_univ]
  rfl

@[simp]
theorem chart_target (c : OpenPartialHomeomorph M H) :
    (chart I c).target = I.symm ⁻¹' c.target := by
  simp only [chart, OpenPartialHomeomorph.trans_target,
    Homeomorph.toOpenPartialHomeomorph_target, univ_inter]
  rfl

/-- The new chart has exactly the old extended partial equivalence. The carrier and topology
of the copy are definitionally those of `M`, so the two partial equivalences have the same type. -/
theorem chart_toPartialEquiv (c : OpenPartialHomeomorph M H) :
    (chart I c).toPartialEquiv = c.extend I := by
  apply PartialEquiv.ext
  · intro x; rfl
  · intro x; rfl
  · rw [chart_source, OpenPartialHomeomorph.extend_source, coe_homeomorph_symm]
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
  change (φ.trans I.toHomeomorph.symm.toOpenPartialHomeomorph).trans
    I.toHomeomorph.toOpenPartialHomeomorph = φ
  simp [OpenPartialHomeomorph.trans_assoc]

/-- Extending an original chart and returning it to its model recovers the original chart. -/
@[simp]
theorem originalChart_chart (c : OpenPartialHomeomorph M H) :
    originalChart I (chart I c) = c := by
  -- Use the original topology instance throughout the composition.
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
  -- Mathlib defines membership by smoothness of the forward and inverse model-coordinate
  -- maps. Isolate that representation in local lemmas for the two chart transitions.
  have transported_mem_iff :
      (chart I c).symm.trans (chart I d) ∈ contDiffGroupoid n 𝓘(𝕜, E) ↔
        ContDiffOn 𝕜 n ((chart I c).symm.trans (chart I d)).toPartialEquiv
            ((chart I c).symm.trans (chart I d)).source ∧
          ContDiffOn 𝕜 n ((chart I d).symm.trans (chart I c)).toPartialEquiv
            ((chart I d).symm.trans (chart I c)).source := by
    -- In the self model the coordinate maps are identities and the range is univ.
    change (ContDiffOn 𝕜 n _ _ ∧ ContDiffOn 𝕜 n _ _) ↔ _
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id,
      preimage_id_eq, range_id, inter_univ]
    rfl
  have original_mem_iff : c.symm.trans d ∈ contDiffGroupoid n I ↔
      ContDiffOn 𝕜 n (I ∘ (c.symm.trans d) ∘ I.symm)
          (I.symm ⁻¹' (c.symm.trans d).source ∩ range I) ∧
        ContDiffOn 𝕜 n (I ∘ (d.symm.trans c) ∘ I.symm)
          (I.symm ⁻¹' (d.symm.trans c).source ∩ range I) := Iff.rfl
  rw [transported_mem_iff, original_mem_iff]
  rw [chart_trans_toPartialEquiv, chart_trans_toPartialEquiv]
  simp only [I.extendCoordChange_source, I.image_eq]
  -- An extended transition is I ∘ (d ∘ c.symm) ∘ I.symm, in both directions.
  rfl

variable [ChartedSpace H M]

/-- The model copy receives the atlas obtained by extending the original charts to `E`. -/
instance : ChartedSpace E (BoundarylessModel I M) where
  atlas := chart I '' atlas H M
  chartAt x := chart I (chartAt H ((homeomorph I M).symm x))
  mem_chart_source x := by
    rw [chart_source]
    exact mem_chart_source H ((homeomorph I M).symm x)
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

/-- Replacing a boundaryless model by its vector space preserves manifold regularity. -/
instance {n : ℕ∞ω} [IsManifold I n M] : IsManifold 𝓘(𝕜, E) n (BoundarylessModel I M) where
  compatible := by
    rintro _ _ ⟨c, hc, rfl⟩ ⟨d, hd, rfl⟩
    exact (chart_trans_mem_contDiffGroupoid_iff I c d n).2
      ((contDiffGroupoid n I).compatible hc hd)

/-- The identity, as a diffeomorphism from the original model to the self-modelled copy. -/
def diffeomorph (n : ℕ∞ω) : Diffeomorph I 𝓘(𝕜, E) M (BoundarylessModel I M) n where
  toEquiv := (homeomorph I M).toEquiv
  contMDiff_toFun := by
    -- The equivalence field and the homeomorphism have the same carrier map; use the latter
    -- so the explicit extended-chart comparison applies.
    change ContMDiff I 𝓘(𝕜, E) n (homeomorph I M)
    intro x
    have hcoord : writtenInExtChartAt I 𝓘(𝕜, E) x (homeomorph I M) =
        writtenInExtChartAt I I x id := by
      simp only [writtenInExtChartAt, extChartAt_eq, Homeomorph.symm_apply_apply]
      rfl
    have h := (contMDiff_id : ContMDiff I I n (id : M → M)) x
    rw [contMDiffAt_iff] at h ⊢
    refine ⟨(homeomorph I M).continuous.continuousAt, ?_⟩
    -- contMDiffAt_iff writes out this coordinate composition; fold its named expression.
    change ContDiffWithinAt 𝕜 n (writtenInExtChartAt I 𝓘(𝕜, E) x (homeomorph I M)) _ _
    rw [hcoord]
    exact h.2
  contMDiff_invFun := by
    -- Likewise, the inverse equivalence field is the inverse homeomorphism on the carrier.
    change ContMDiff 𝓘(𝕜, E) I n (homeomorph I M).symm
    intro x
    have hcoord : writtenInExtChartAt 𝓘(𝕜, E) I x (homeomorph I M).symm =
        writtenInExtChartAt I I ((homeomorph I M).symm x) id := by
      simp only [writtenInExtChartAt, extChartAt_eq]
      rfl
    have h := (contMDiff_id : ContMDiff I I n (id : M → M)) ((homeomorph I M).symm x)
    rw [contMDiffAt_iff, I.range_eq_univ] at h
    rw [contMDiffAt_iff]
    refine ⟨(homeomorph I M).symm.continuous.continuousAt, ?_⟩
    -- Fold the coordinate composition from contMDiffAt_iff before applying hcoord.
    change ContDiffWithinAt 𝕜 n (writtenInExtChartAt 𝓘(𝕜, E) I x (homeomorph I M).symm) _ _
    rw [hcoord, ModelWithCorners.range_eq_univ, extChartAt_eq]
    exact h.2

/-- The diffeomorphism has the same underlying map as the identity homeomorphism. -/
@[simp]
theorem coe_diffeomorph (n : ℕ∞ω) : ⇑(diffeomorph I (M := M) n) = homeomorph I M :=
  (rfl)

/-- The inverse diffeomorphism has the inverse identity map as its underlying function. -/
@[simp]
theorem coe_diffeomorph_symm (n : ℕ∞ω) :
    ⇑(diffeomorph I (M := M) n).symm = (homeomorph I M).symm :=
  (rfl)

section Derivatives

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [TopologicalSpace H'] (J : ModelWithCorners 𝕜 E' H')
  [TopologicalSpace N] [ChartedSpace H' N]

/-- Changing the source model preserves differentiability, even when no manifold regularity
assumption is imposed on either atlas. -/
@[simp]
theorem mdifferentiableAt_source_iff (f : M → N) (x : BoundarylessModel I M) :
    MDifferentiableAt 𝓘(𝕜, E) J (f ∘ (homeomorph I M).symm) x ↔
      MDifferentiableAt I J f ((homeomorph I M).symm x) := by
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff]
  simp only [writtenInExtChartAt, extChartAt_eq, I.range_eq_univ,
    ModelWithCorners.range_eq_univ]
  exact and_congr ((homeomorph I M).symm.comp_continuousAt_iff' f x) Iff.rfl

-- The coordinate derivative is unchanged: both the written map and evaluation point agree
-- by extChartAt_eq, and both model ranges are univ. Keep this separate from tangent casts.
private theorem fderivWithin_writtenInExtChartAt_source (f : M → N)
    (x : BoundarylessModel I M) :
    fderivWithin 𝕜 (writtenInExtChartAt 𝓘(𝕜, E) J x (f ∘ (homeomorph I M).symm))
        (range 𝓘(𝕜, E)) (extChartAt 𝓘(𝕜, E) x x) =
      fderivWithin 𝕜 (writtenInExtChartAt I J ((homeomorph I M).symm x) f)
        (range I) (extChartAt I ((homeomorph I M).symm x) ((homeomorph I M).symm x)) := by
  simp only [writtenInExtChartAt, extChartAt_eq, I.range_eq_univ,
    ModelWithCorners.range_eq_univ]
  rfl

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
  simpa using congrArg (fun L ↦ L ((tangentSpaceCastModel 𝓘(𝕜, E) x).symm
    (tangentSpaceCastModel I ((homeomorph I M).symm x) v))) h

/-- Changing the target model preserves differentiability. -/
@[simp]
theorem mdifferentiableAt_target_iff (f : N → M) (x : N) :
    MDifferentiableAt J 𝓘(𝕜, E) ((homeomorph I M) ∘ f) x ↔
      MDifferentiableAt J I f x := by
  rw [mdifferentiableAt_iff, mdifferentiableAt_iff]
  simp only [writtenInExtChartAt, comp_apply, extChartAt_eq,
    Homeomorph.symm_apply_apply]
  exact and_congr ((homeomorph I M).comp_continuousAt_iff f x) Iff.rfl

-- Target transport leaves the coordinate derivative unchanged, before identifying tangent spaces.
private theorem fderivWithin_writtenInExtChartAt_target (f : N → M) (x : N) :
    fderivWithin 𝕜 (writtenInExtChartAt J 𝓘(𝕜, E) x ((homeomorph I M) ∘ f))
        (range J) (extChartAt J x x) =
      fderivWithin 𝕜 (writtenInExtChartAt J I x f) (range J) (extChartAt J x x) := by
  simp only [writtenInExtChartAt, comp_apply, extChartAt_eq, Homeomorph.symm_apply_apply]
  rfl

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
