/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.IsManifold.ExtChartAt
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import TauCeti.Geometry.Manifold.ExtChartAt.CoordChange

/-!
# Measurability for extended charts and coordinate changes

This file provides low-level measurability and measurable-embedding lemmas for arbitrary extended
charts `e.extend I` and extended coordinate changes `I.extendCoordChange e e'`, without Jacobian
change-of-variables or Haar integration dependencies.

## Main results

* `OpenPartialHomeomorph.measurableSet_extend_target`: the target of `e.extend I` is measurable.
* `OpenPartialHomeomorph.measurableEmbedding_extend_restrict`: `e.extend I` restricted to its
  source is a measurable embedding for the Borel measurable spaces.
* `OpenPartialHomeomorph.measurableSet_image_extend_iff`: a subset of `e.source` is Borel
  measurable iff its image under `e.extend I` is Borel measurable.
* `OpenPartialHomeomorph.measurableSet_image_extend`: the image under `e.extend I` of a
  measurable subset of `e.source` is measurable.
* `OpenPartialHomeomorph.measurableSet_preimage_extend_inter`: Borel preimages under `e.extend I`
  intersected with `e.source` are measurable.
* `ModelWithCorners.measurableSet_extendCoordChange_source`: the source of an extended
  coordinate change is measurable.
-/

public section

open scoped Manifold Topology

section ExtendMeasurable

variable {𝕜 E H M : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [TopologicalSpace H] [TopologicalSpace M]

namespace OpenPartialHomeomorph

/-- The target of an extended chart `e.extend I` is measurable in any measurable space on `E`
where open sets are measurable. -/
theorem measurableSet_extend_target [MeasurableSpace E] [OpensMeasurableSpace E]
    (e : OpenPartialHomeomorph M H) (I : ModelWithCorners 𝕜 E H) :
    MeasurableSet (e.extend I).target := by
  rw [e.extend_target]
  exact (e.open_target.preimage I.continuous_symm).measurableSet.inter
    I.isClosed_range.measurableSet

/-- An extended chart `e.extend I`, restricted to its source, is a measurable embedding for the
Borel measurable spaces. -/
theorem measurableEmbedding_extend_restrict [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) :
    MeasurableEmbedding (e.source.domRestrict (e.extend I)) := by
  let f : PartialHomeomorph M E :=
    { toPartialEquiv := e.extend I
      continuousOn_toFun := e.continuousOn_extend
      continuousOn_invFun := e.continuousOn_extend_symm }
  have hrange : MeasurableSet (Set.range (f.source.domRestrict f)) := by
    rw [Set.range_domRestrict, f.image_source_eq_target]
    exact e.measurableSet_extend_target I
  have hemb := f.isEmbedding_restrict.measurableEmbedding hrange
  rwa [e.extend_source] at hemb

/-- For Borel measurable spaces on `M` and `E`, a subset of `e.source` is measurable iff its
image under `e.extend I` is measurable. -/
theorem measurableSet_image_extend_iff [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) {s : Set M} (hsub : s ⊆ e.source) :
    MeasurableSet (e.extend I '' s) ↔ MeasurableSet s := by
  have him : e.source.domRestrict (e.extend I) '' (Subtype.val ⁻¹' s) = e.extend I '' s := by
    rw [Set.image_domRestrict, Set.inter_eq_left.2 hsub]
  rw [← him, (e.measurableEmbedding_extend_restrict I).measurableSet_image,
    ← (MeasurableEmbedding.subtypeVal e.open_source.measurableSet).measurableSet_image,
    Subtype.image_preimage_coe, Set.inter_eq_right.2 hsub]

/-- For a Borel measurable space on `M`, the image under `e.extend I` of a measurable subset of
`e.source` is measurable in any measurable space on `E` where open sets are measurable. -/
theorem measurableSet_image_extend [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace M] [BorelSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) {s : Set M} (hs : MeasurableSet s) (hsub : s ⊆ e.source) :
    MeasurableSet (e.extend I '' s) :=
  OpensMeasurableSpace.borel_le _ <| by
    let : MeasurableSpace E := borel E
    have : BorelSpace E := ⟨rfl⟩
    exact (e.measurableSet_image_extend_iff I hsub).2 hs

/-- The preimage of a Borel measurable set in `E` under `e.extend I`, intersected with `e.source`,
is measurable whenever open subsets of `M` are measurable. -/
theorem measurableSet_preimage_extend_inter [MeasurableSpace E] [BorelSpace E]
    [MeasurableSpace M] [OpensMeasurableSpace M] (e : OpenPartialHomeomorph M H)
    (I : ModelWithCorners 𝕜 E H) {A : Set E} (hA : MeasurableSet A) :
    MeasurableSet (e.extend I ⁻¹' A ∩ e.source) := by
  have hval : MeasurableEmbedding (Subtype.val : e.source → M) :=
    .subtypeVal e.open_source.measurableSet
  have hseq : e.extend I ⁻¹' A ∩ e.source =
      Subtype.val '' (e.source.domRestrict (e.extend I) ⁻¹' A) := by
    ext x
    simp [and_comm]
  rw [hseq]
  exact hval.measurableSet_image.2 ((e.continuous_domRestrict_extend I).measurable hA)

end OpenPartialHomeomorph

namespace ModelWithCorners

/-- The source of an extended coordinate change is measurable whenever open subsets of `E`
are measurable. -/
theorem measurableSet_extendCoordChange_source [MeasurableSpace E] [OpensMeasurableSpace E]
    (I : ModelWithCorners 𝕜 E H) (e e' : OpenPartialHomeomorph M H) :
    MeasurableSet (I.extendCoordChange e e').source := by
  simpa only [OpenPartialHomeomorph.extend_target', OpenPartialHomeomorph.symm_target,
    ← I.extendCoordChange_source] using
    ((e.symm ≫ₕ e').symm).measurableSet_extend_target I

end ModelWithCorners

end ExtendMeasurable
