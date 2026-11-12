/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-!
# Replacing a boundaryless model by its vector space

`BoundarylessModel I M` carries the topology of `M`, but its charts take values in the
model vector space `E` rather than in `H`. A chart `c` is replaced by `I ∘ c`.
The extended charts do not change, and the identity is a diffeomorphism.

This lets constructions stated for self-modelled manifolds apply to arbitrary boundaryless
models without installing a second atlas on the original manifold. In particular, local
normal forms and implicit-function constructions can retain their actual coordinates.

`OpenPartialHomeomorph.symm_trans_mem_contDiffGroupoid_iff_of_extend` compares coordinate changes
for any pair of extended charts, independently of model-boundarylessness.
The carrier also inherits monoid, additive monoid, group and additive group operations.
`homeomorph_one`, `homeomorph_mul`, `homeomorph_inv` and their `symm` forms give the algebraic
transport laws; `homeomorph_zero`, `homeomorph_add`, `homeomorph_neg` and their `symm` forms
are their additive counterparts.
`BoundarylessModel.isManifold_of_atlas_extend` and
`BoundarylessModel.extChartAt_eq_of_chartAt_toPartialEquiv` compare arbitrary chosen extended
atlases. `BoundarylessModel.diffeomorphOfExtChartAtEq` constructs the common identity
transport from the extended-chart comparison and manifold boundarylessness;
`coe_diffeomorphOfExtChartAtEq` and `coe_diffeomorphOfExtChartAtEq_symm` give its functions.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 1 (Smooth Manifolds), section Smooth Structures, Proposition 1.17, pp.13–14.
-/

public section

open Function Set
open scoped ContDiff Manifold

namespace TauCeti

variable {𝕜 E H : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]

section ExtendedCharts

variable {M : Type*} [TopologicalSpace M] {I : ModelWithCorners 𝕜 E H}

/-- Extended charts have the same smooth coordinate-change condition in the vector-space model
as their original charts in the model with corners. -/
theorem _root_.OpenPartialHomeomorph.symm_trans_mem_contDiffGroupoid_iff_of_extend
    (C D : OpenPartialHomeomorph M E) (c d : OpenPartialHomeomorph M H)
    (hC : C.toPartialEquiv = c.extend I) (hD : D.toPartialEquiv = d.extend I) (n : ℕ∞ω) :
    C.symm.trans D ∈ contDiffGroupoid n 𝓘(𝕜, E) ↔
      c.symm.trans d ∈ contDiffGroupoid n I := by
  have hCD : (C.symm.trans D).toPartialEquiv = I.extendCoordChange c d := by
    rw [ModelWithCorners.extendCoordChange, OpenPartialHomeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.symm_toPartialEquiv, hC, hD]
  have hDC : (D.symm.trans C).toPartialEquiv = I.extendCoordChange d c := by
    rw [ModelWithCorners.extendCoordChange, OpenPartialHomeomorph.trans_toPartialEquiv,
      OpenPartialHomeomorph.symm_toPartialEquiv, hD, hC]
  have transported_mem_iff :
      C.symm.trans D ∈ contDiffGroupoid n 𝓘(𝕜, E) ↔
        ContDiffOn 𝕜 n (C.symm.trans D).toPartialEquiv (C.symm.trans D).source ∧
          ContDiffOn 𝕜 n (D.symm.trans C).toPartialEquiv (D.symm.trans C).source := by
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid]
    simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, id_comp, comp_id,
      preimage_id_eq, range_id, inter_univ]
    -- Inverse transitions and their partial equivalences have the same functions and source sets.
    rfl
  have original_mem_iff : c.symm.trans d ∈ contDiffGroupoid n I ↔
      ContDiffOn 𝕜 n (I ∘ (c.symm.trans d) ∘ I.symm)
          (I.symm ⁻¹' (c.symm.trans d).source ∩ range I) ∧
        ContDiffOn 𝕜 n (I ∘ (d.symm.trans c) ∘ I.symm)
          (I.symm ⁻¹' (d.symm.trans c).source ∩ range I) := Iff.rfl
  rw [transported_mem_iff, original_mem_iff, hCD, hDC]
  simp only [I.extendCoordChange_source, I.image_eq]
  -- An extended transition is I ∘ (d ∘ c.symm) ∘ I.symm, in both directions.
  rfl

end ExtendedCharts

/-- A copy of a manifold with inherited topology and vector-space-valued atlas constructors.
The default atlas uses a globally boundaryless model. `BoundarylessModel.interiorChartedSpace`
also applies to a boundaryless C¹ manifold whose model may have boundary. -/
-- The exported carrier and chart equalities require this body under Lean's module system.
@[expose] def BoundarylessModel (_I : ModelWithCorners 𝕜 E H) (M : Type*) := M

namespace BoundarylessModel

/-- The model copy inherits its original monoid operations. -/
@[to_additive
  /-- The model copy inherits its original additive monoid operations. -/]
instance {I : ModelWithCorners 𝕜 E H} {M : Type*} [Monoid M] :
    Monoid (BoundarylessModel I M) := inferInstanceAs (Monoid M)

/-- The model copy inherits its original group operations. -/
@[to_additive
  /-- The model copy inherits its original additive group operations. -/]
instance {I : ModelWithCorners 𝕜 E H} {M : Type*} [Group M] :
    Group (BoundarylessModel I M) := inferInstanceAs (Group M)

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

/-- The identity homeomorphism preserves the inherited monoid identity. -/
@[to_additive
  /-- The identity homeomorphism preserves the inherited additive identity. -/]
theorem homeomorph_one [Monoid M] : homeomorph I M (1 : M) = 1 := by
  -- The copy inherits its algebraic operations definitionally from the original carrier.
  rfl

/-- The identity homeomorphism preserves the inherited multiplication. -/
@[to_additive
  /-- The identity homeomorphism preserves the inherited addition. -/]
theorem homeomorph_mul [Monoid M] (x y : M) :
    homeomorph I M (x * y) = homeomorph I M x * homeomorph I M y := by
  rfl

/-- The inverse identity homeomorphism preserves the inherited monoid identity. -/
@[to_additive
  /-- The inverse identity homeomorphism preserves the inherited additive identity. -/]
theorem homeomorph_symm_one [Monoid M] : (homeomorph I M).symm 1 = (1 : M) := by
  rfl

/-- The inverse identity homeomorphism preserves the inherited multiplication. -/
@[to_additive
  /-- The inverse identity homeomorphism preserves the inherited addition. -/]
theorem homeomorph_symm_mul [Monoid M] (x y : BoundarylessModel I M) :
    (homeomorph I M).symm (x * y) = (homeomorph I M).symm x * (homeomorph I M).symm y := by
  rfl

/-- The identity homeomorphism preserves the inherited inversion. -/
@[to_additive
  /-- The identity homeomorphism preserves the inherited negation. -/]
theorem homeomorph_inv [Group M] (x : M) :
    homeomorph I M x⁻¹ = (homeomorph I M x)⁻¹ := by
  rfl

/-- The inverse identity homeomorphism preserves the inherited inversion. -/
@[to_additive
  /-- The inverse identity homeomorphism preserves the inherited negation. -/]
theorem homeomorph_symm_inv [Group M] (x : BoundarylessModel I M) :
    (homeomorph I M).symm x⁻¹ = ((homeomorph I M).symm x)⁻¹ := by
  rfl

section ComparedAtlases

variable {M} [ChartedSpace H M] [ChartedSpace E (BoundarylessModel I M)]

/-- A chosen vector-space atlas of extended original charts preserves manifold regularity. -/
theorem isManifold_of_atlas_extend {n : ℕ∞ω} [IsManifold I n M]
    (h : ∀ C ∈ atlas E (BoundarylessModel I M),
      ∃ c : OpenPartialHomeomorph M H, c ∈ atlas H M ∧ C.toPartialEquiv = c.extend I) :
    IsManifold 𝓘(𝕜, E) n (BoundarylessModel I M) where
  compatible := by
    intro C D hC hD
    obtain ⟨c, hc, hC⟩ := h C hC
    obtain ⟨d, hd, hD⟩ := h D hD
    exact (C.symm_trans_mem_contDiffGroupoid_iff_of_extend (I := I) (M := M) D c d hC hD n).2
      ((contDiffGroupoid n I).compatible (M := M) hc hd)

/-- Extending a preferred chart already equal to the original extended chart changes nothing. -/
theorem extChartAt_eq_of_chartAt_toPartialEquiv
    (h : ∀ x : BoundarylessModel I M,
      (chartAt E x).toPartialEquiv = (chartAt H ((homeomorph I M).symm x)).extend I)
    (x : BoundarylessModel I M) :
    extChartAt 𝓘(𝕜, E) x = extChartAt I ((homeomorph I M).symm x) := by
  rw [extChartAt, OpenPartialHomeomorph.extend, modelWithCornersSelf_partialEquiv,
    PartialEquiv.trans_refl, h]
  rfl

/-- Matching extended charts on a boundaryless manifold give the identity diffeomorphism. -/
def diffeomorphOfExtChartAtEq [BoundarylessManifold I M]
    (hchart : ∀ x : BoundarylessModel I M,
      extChartAt 𝓘(𝕜, E) x = extChartAt I ((homeomorph I M).symm x))
    (n : ℕ∞ω) :
    Diffeomorph I 𝓘(𝕜, E) M (BoundarylessModel I M) n where
  toEquiv := (homeomorph I M).toEquiv
  contMDiff_toFun := by
    -- The Diffeomorph field projects through toEquiv, with no rewrite lemma to the homeomorphism.
    -- Expose the definitional equality of their carrier functions directly.
    change ContMDiff I 𝓘(𝕜, E) n (homeomorph I M)
    intro x
    have hcoord : writtenInExtChartAt I 𝓘(𝕜, E) x (homeomorph I M) =
        writtenInExtChartAt I I x id := by
      simp only [writtenInExtChartAt, hchart, Homeomorph.symm_apply_apply]
      simp only [coe_homeomorph]
      -- The identity carrier maps leave identical coordinate compositions.
      rfl
    have h := (contMDiff_id : ContMDiff I I n (id : M → M)) x
    rw [contMDiffAt_iff] at h ⊢
    refine ⟨(homeomorph I M).continuous.continuousAt, ?_⟩
    -- Fold the contMDiffAt_iff expression to writtenInExtChartAt so hcoord can rewrite it.
    change ContDiffWithinAt 𝕜 n (writtenInExtChartAt I 𝓘(𝕜, E) x (homeomorph I M)) _ _
    rw [hcoord]
    exact h.2
  contMDiff_invFun := by
    -- The inverse field projects through toEquiv, with no rewrite lemma to the homeomorphism.
    -- Expose the definitional equality of their inverse carrier functions directly.
    change ContMDiff 𝓘(𝕜, E) I n (homeomorph I M).symm
    intro x
    have hcoord : writtenInExtChartAt 𝓘(𝕜, E) I x (homeomorph I M).symm =
        writtenInExtChartAt I I ((homeomorph I M).symm x) id := by
      simp only [writtenInExtChartAt, hchart]
      simp only [coe_homeomorph_symm]
      -- The inverse identity carrier maps also leave identical coordinate compositions.
      rfl
    have h := (contMDiff_id : ContMDiff I I n (id : M → M)) ((homeomorph I M).symm x)
    rw [contMDiffAt_iff] at h ⊢
    refine ⟨(homeomorph I M).symm.continuous.continuousAt, ?_⟩
    -- Fold the contMDiffAt_iff expression to writtenInExtChartAt so hcoord can rewrite it.
    change ContDiffWithinAt 𝕜 n (writtenInExtChartAt 𝓘(𝕜, E) I x (homeomorph I M).symm) _ _
    rw [hcoord, hchart]
    -- Boundarylessness makes the original model range a neighbourhood at this point.
    simpa only [coe_homeomorph_symm, writtenInExtChartAt, id_eq] using
      (h.2.contDiffAt (range_mem_nhds_isInteriorPoint
        (BoundarylessManifold.isInteriorPoint (I := I)))).contDiffWithinAt

/-- The chart-comparison diffeomorphism has the identity homeomorphism as its function. -/
@[simp]
theorem coe_diffeomorphOfExtChartAtEq [BoundarylessManifold I M]
    (hchart : ∀ x : BoundarylessModel I M,
      extChartAt 𝓘(𝕜, E) x = extChartAt I ((homeomorph I M).symm x))
    (n : ℕ∞ω) :
    ⇑(diffeomorphOfExtChartAtEq I hchart n) = homeomorph I M := by rfl

/-- The inverse chart-comparison diffeomorphism has the inverse identity homeomorphism. -/
@[simp]
theorem coe_diffeomorphOfExtChartAtEq_symm [BoundarylessManifold I M]
    (hchart : ∀ x : BoundarylessModel I M,
      extChartAt 𝓘(𝕜, E) x = extChartAt I ((homeomorph I M).symm x))
    (n : ℕ∞ω) :
    ⇑(diffeomorphOfExtChartAtEq I hchart n).symm = (homeomorph I M).symm := by rfl

end ComparedAtlases

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

private theorem chart_trans_mem_contDiffGroupoid_iff (c d : OpenPartialHomeomorph M H)
    (n : ℕ∞ω) :
    (chart I c).symm.trans (chart I d) ∈ contDiffGroupoid n 𝓘(𝕜, E) ↔
      c.symm.trans d ∈ contDiffGroupoid n I :=
  (chart I c).symm_trans_mem_contDiffGroupoid_iff_of_extend (chart I d) c d
    (chart_toPartialEquiv I c) (chart_toPartialEquiv I d) n

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
    extChartAt 𝓘(𝕜, E) x = extChartAt I ((homeomorph I M).symm x) :=
  extChartAt_eq_of_chartAt_toPartialEquiv I (fun _ ↦ chart_toPartialEquiv I _) x

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
instance {n : ℕ∞ω} [IsManifold I n M] : IsManifold 𝓘(𝕜, E) n (BoundarylessModel I M) := by
  apply isManifold_of_atlas_extend I (M := M)
  rintro C ⟨c, hc, hC⟩
  rw [← hC]
  exact ⟨c, hc, chart_toPartialEquiv I c⟩

/-- The identity, as a diffeomorphism from the original model to the self-modelled copy. -/
def diffeomorph (n : ℕ∞ω) : Diffeomorph I 𝓘(𝕜, E) M (BoundarylessModel I M) n :=
  diffeomorphOfExtChartAtEq I (extChartAt_eq I) n

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
