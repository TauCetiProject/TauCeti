/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.OrientedAtlas
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Atlas

/-!
# Oriented atlases induce canonical orientations

An oriented subatlas of the maximal atlas determines an actual orientation, also at boundary and
corner points. The converse requires a boundaryless hypothesis and is not used here.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [cM : ChartedSpace H M] [mM : IsManifold I 1 M]
  {n : ℕ∞ω} [NeZero n]

/-- An oriented subatlas yields a genuine manifold orientation, including all boundary and
corner points. -/
theorem IsOrientedAtlas.nonempty_orientation {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) :
    Nonempty (Manifold.Orientation I M (Fin (Module.finrank ℝ E))) := by
  suffices Nonempty (Manifold.OrientationLift I M (Fin (Module.finrank ℝ E))) from
    this.map Manifold.Orientation.mk
  have hsub : A ⊆ IsManifold.maximalAtlas I 1 M :=
    hA.subset_maximalAtlas.trans (IsManifold.maximalAtlas_subset_of_le
      (ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne n)))
  have hAcover := hA.exists_mem_source
  have hAdet : ∀ {e e' : OpenPartialHomeomorph M H}, e ∈ A → e' ∈ A →
      ∀ {x : M}, x ∈ e.source → x ∈ e'.source →
      0 < (fderivWithin ℝ (e'.extend I ∘ (e.extend I).symm) (range I)
        (e.extend I x)).det := by
    intro e e' he he' x hx hx'
    exact hA.det_fderivWithin_pos he he' hx hx'
  have hcompat := @IsManifold.compatible_of_mem_maximalAtlas ℝ _ E _ _ H _ I 1 M _ _
  let enlarged : ChartedSpace H M := {
    atlas := IsManifold.maximalAtlas I 1 M
    chartAt := chartAt H
    mem_chart_source := mem_chart_source H
    chart_mem_atlas := IsManifold.chart_mem_maximalAtlas }
  let : ChartedSpace H M := enlarged
  let : HasGroupoid M (contDiffGroupoid 1 I) := ⟨fun he he' ↦ hcompat he he'⟩
  let : IsManifold I 1 M := IsManifold.mk' I 1 M
  let Z := tangentBundleCore I M
  let S : Set (atlas H M) := {e | e.val ∈ A}
  have hcover : ∀ x, ∃ e ∈ S, x ∈ Z.baseSet e := by
    intro x
    obtain ⟨e, he, hx⟩ := hAcover x
    exact ⟨⟨e, hsub he⟩, he, hx⟩
  have hpos : ∀ e ∈ S, ∀ e' ∈ S, ∀ x ∈ Z.baseSet e ∩ Z.baseSet e',
      0 < (Z.coordChange e e' x).det := by
    intro e he e' he' x hx
    exact hAdet he he' hx.1 hx.2
  let vb := Z.orientationOfPositiveAtlas (Module.finBasis ℝ E).orientation
    (Fintype.card_fin _) hcover hpos
  let l := Manifold.OrientationLift.ofVectorBundleOrientation (Module.finBasis ℝ E).orientation
    (Fintype.card_fin _) vb
  exact ⟨@Manifold.OrientationLift.mk E H _ _ _ I M _ cM
    (Fin (Module.finrank ℝ E)) _ _ l.modelOrientation l.card_eq l.sign
      l.locallyConstant_sign l.compatible⟩

end TauCeti
