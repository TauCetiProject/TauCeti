/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# Manifolds glued from open pieces

Let `M` be a topological space covered by the images of open embeddings `φ j : U j → M` of
charted spaces modelled on a common space `H`. Transporting the charts of each piece along its
embedding gives a charted-space structure on `M`, `TauCeti.chartedSpaceOfIsOpenEmbedding`. This is
how a space glued from manifolds along open subsets, such as `TopCat.GlueData.glued`, receives its
atlas.

The atlas is a `C^n` manifold as soon as the pieces are `C^n` manifolds and are glued along `C^n`
maps. The gluing condition is phrased without inverses: whenever `φ j x = φ k y`, some map
`T : U j → U k` that is `C^n` at `x` sends `x` to `y` and satisfies `φ k ∘ T = φ j` near `x`.
For a space glued along transition maps, `T` is the transition itself. Each embedding `φ j` is then
a `C^n` diffeomorphism onto its open image.

## Main declarations

* `TauCeti.chartedSpaceOfIsOpenEmbedding`: the charts transported from the pieces.
* `TauCeti.isManifold_chartedSpaceOfIsOpenEmbedding`: pieces glued along `C^n` maps give a `C^n`
  manifold.
* `TauCeti.partialDiffeomorphOfIsOpenEmbedding`: each embedding of a piece is a `C^n`
  diffeomorphism onto its image.

## Implementation notes

The pieces are assumed nonempty, so that each embedding is an open partial homeomorphism defined
on its whole piece; an empty piece covers nothing and can be discarded.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the smooth manifold chart lemma).
-/

public section

open Set Filter Topology IsManifold
open scoped Manifold ContDiff

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  {J : Type*} {U : J → Type*} [∀ j, TopologicalSpace (U j)] [∀ j, Nonempty (U j)]
  [∀ j, ChartedSpace H (U j)] {M : Type*} [TopologicalSpace M] {φ : ∀ j, U j → M}
  (hφ : ∀ j, IsOpenEmbedding (φ j)) (hcover : ∀ x, ∃ j y, φ j y = x)

/-- The charted-space structure on a space covered by open embeddings of charted spaces: the chart
at a point is the inverse of the embedding of a piece containing it, followed by a chart of that
piece. -/
@[instance_reducible]
noncomputable def chartedSpaceOfIsOpenEmbedding : ChartedSpace H M where
  atlas := range fun x ↦ ((hφ (hcover x).choose).toOpenPartialHomeomorph _).symm.trans
    (chartAt H (hcover x).choose_spec.choose)
  chartAt x := ((hφ (hcover x).choose).toOpenPartialHomeomorph _).symm.trans
    (chartAt H (hcover x).choose_spec.choose)
  mem_chart_source x := by
    have hx := (hcover x).choose_spec.choose_spec
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      IsOpenEmbedding.toOpenPartialHomeomorph_target, mem_inter_iff, mem_preimage]
    refine ⟨⟨_, hx⟩, ?_⟩
    have h := (hφ _).toOpenPartialHomeomorph_left_inv _ (x := (hcover x).choose_spec.choose)
    rw [hx] at h
    rw [h]
    exact mem_chart_source H _
  chart_mem_atlas x := mem_range_self x

include hcover in
/-- Every chart of `chartedSpaceOfIsOpenEmbedding` is the inverse of the embedding of a piece
followed by a chart of that piece. -/
theorem exists_chartAt_chartedSpaceOfIsOpenEmbedding_eq (x : M) :
    ∃ (j : J) (y : U j), φ j y = x ∧
      @chartAt H _ M _ (chartedSpaceOfIsOpenEmbedding hφ hcover) x =
        ((hφ j).toOpenPartialHomeomorph _).symm.trans (chartAt H y) :=
  ⟨_, _, (hcover x).choose_spec.choose_spec, rfl⟩

variable (hdeck : ∀ (j k : J) (x : U j) (y : U k), φ j x = φ k y →
  ∃ T : U j → U k, ContMDiffAt I I n T x ∧ T x = y ∧ φ k ∘ T =ᶠ[𝓝 x] φ j)

include hdeck in
/-- If the pieces are glued along `C^n` maps, then the inverse of the embedding of one piece,
composed with the embedding of another, is `C^n` wherever it is defined. -/
private theorem contMDiffAt_symm_comp {j k : J} {x : U j} (hx : φ j x ∈ range (φ k)) :
    ContMDiffAt I I n (((hφ k).toOpenPartialHomeomorph _).symm ∘ φ j) x := by
  obtain ⟨T, hT, -, hTφ⟩ := hdeck j k x _ ((hφ k).toOpenPartialHomeomorph_right_inv _ hx).symm
  refine hT.congr_of_eventuallyEq ?_
  filter_upwards [hTφ] with z hz
  rw [Function.comp_apply, ← hz, Function.comp_apply,
    IsOpenEmbedding.toOpenPartialHomeomorph_left_inv]

include hdeck in
/-- Pieces that are `C^n` manifolds glued along `C^n` maps give a `C^n` manifold. -/
theorem isManifold_chartedSpaceOfIsOpenEmbedding [∀ j, IsManifold I n (U j)] :
    letI := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
    IsManifold I n M := by
  let := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
  refine isManifold_of_contDiffOn I n M ?_
  rintro _ _ ⟨p, rfl⟩ ⟨q, rfl⟩ u hu
  set a := (hcover p).choose
  set b := (hcover q).choose
  set ψa := (hφ a).toOpenPartialHomeomorph _
  set ψb := (hφ b).toOpenPartialHomeomorph _
  set ca := chartAt H (hcover p).choose_spec.choose
  set cb := chartAt H (hcover q).choose_spec.choose
  have hmem := hu
  simp only [mfld_simps] at hmem
  obtain ⟨⟨hva, hvb, hvcb⟩, huI⟩ := hmem
  set z := ca.symm (I.symm u)
  have hz : z ∈ ca.source := ca.map_target hva
  have key := (contMDiffAt_iff_of_mem_maximalAtlas (chart_mem_maximalAtlas _)
    (chart_mem_maximalAtlas _) hz hvcb).1 (contMDiffAt_symm_comp hφ hdeck hvb) |>.2
  have hu' : ca.extend I z = u := by
    simp [z, ca.right_inv hva, I.right_inv huI]
  rw [hu'] at key
  refine (key.mono inter_subset_right).congr_of_mem (fun y _ ↦ ?_) hu
  simp only [mfld_simps]

include hdeck in
/-- The inverse of the embedding of a piece is `C^n` on its image. -/
theorem contMDiffOn_symm_chartedSpaceOfIsOpenEmbedding [∀ j, IsManifold I n (U j)] (j : J) :
    letI := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
    ContMDiffOn I I n ((hφ j).toOpenPartialHomeomorph _).symm (range (φ j)) := by
  let := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
  have := isManifold_chartedSpaceOfIsOpenEmbedding hφ hcover hdeck
  rintro _ ⟨z, rfl⟩
  refine ContMDiffAt.contMDiffWithinAt ?_
  obtain ⟨a, y, hy, hc⟩ :=
    exists_chartAt_chartedSpaceOfIsOpenEmbedding_eq (H := H) hφ hcover (φ j z)
  set ψa := (hφ a).toOpenPartialHomeomorph _
  have hright : ∀ w ∈ range (φ a), φ a (ψa.symm w) = w := fun w hw ↦
    (hφ a).toOpenPartialHomeomorph_right_inv _ hw
  have hψy : ψa.symm (φ j z) = y := by
    rw [← hy]
    exact (hφ a).toOpenPartialHomeomorph_left_inv _
  have hmem : ψa.symm.trans (chartAt H y) ∈ maximalAtlas I n M :=
    hc ▸ chart_mem_maximalAtlas (φ j z)
  have hsrc : φ j z ∈ (ψa.symm.trans (chartAt H y)).source := hc ▸ mem_chart_source H (φ j z)
  -- Near `φ j z`, the inverse of `φ a` is the chart of `M` followed by the inverse chart of `U a`.
  have hψa : ContMDiffAt I I n ψa.symm (φ j z) := by
    have h₁ := contMDiffAt_of_mem_maximalAtlas hmem hsrc
    have h₂ : ContMDiffAt I I n (chartAt H y).symm ((ψa.symm.trans (chartAt H y)) (φ j z)) := by
      refine contMDiffAt_symm_of_mem_maximalAtlas (chart_mem_maximalAtlas y) ?_
      rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hψy]
      exact (chartAt H y).map_source (mem_chart_source H y)
    refine (h₂.comp _ h₁).congr_of_eventuallyEq ?_
    filter_upwards [(ψa.symm.trans (chartAt H y)).open_source.mem_nhds hsrc] with w hw
    exact ((chartAt H y).left_inv hw.2).symm
  -- The inverse of `φ j` is the inverse of `φ a` followed by a transition map.
  have hza : φ a (ψa.symm (φ j z)) ∈ range (φ j) := by
    rw [hψy, hy]
    exact mem_range_self z
  refine ((contMDiffAt_symm_comp hφ hdeck hza).comp _ hψa).congr_of_eventuallyEq ?_
  filter_upwards [(hφ a).isOpen_range.mem_nhds ⟨y, hy⟩] with w hw
  rw [Function.comp_apply, Function.comp_apply, hright w hw]

include hdeck in
/-- The embedding of a piece is `C^n`. -/
theorem contMDiff_chartedSpaceOfIsOpenEmbedding [∀ j, IsManifold I n (U j)] (j : J) :
    letI := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
    ContMDiff I I n (φ j) := by
  let := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
  have := isManifold_chartedSpaceOfIsOpenEmbedding hφ hcover hdeck
  intro z
  obtain ⟨a, y, hy, hc⟩ :=
    exists_chartAt_chartedSpaceOfIsOpenEmbedding_eq (H := H) hφ hcover (φ j z)
  set ψa := (hφ a).toOpenPartialHomeomorph _
  have hright : ∀ w ∈ range (φ a), φ a (ψa.symm w) = w := fun w hw ↦
    (hφ a).toOpenPartialHomeomorph_right_inv _ hw
  have hψy : ψa.symm (φ j z) = y := by
    rw [← hy]
    exact (hφ a).toOpenPartialHomeomorph_left_inv _
  have hmem : ψa.symm.trans (chartAt H y) ∈ maximalAtlas I n M :=
    hc ▸ chart_mem_maximalAtlas (φ j z)
  have hsrc : φ j z ∈ (ψa.symm.trans (chartAt H y)).source := hc ▸ mem_chart_source H (φ j z)
  -- Near `y`, the embedding `φ a` is the chart of `U a` followed by the inverse chart of `M`.
  have hφa : ContMDiffAt I I n (φ a) ((ψa.symm ∘ φ j) z) := by
    rw [Function.comp_apply, hψy]
    have h₁ := contMDiffAt_of_mem_maximalAtlas (chart_mem_maximalAtlas (I := I) (n := n) y)
      (mem_chart_source H y)
    have h₂ : ContMDiffAt I I n (ψa.symm.trans (chartAt H y)).symm (chartAt H y y) := by
      refine contMDiffAt_symm_of_mem_maximalAtlas hmem ?_
      have h := (ψa.symm.trans (chartAt H y)).map_source hsrc
      rwa [OpenPartialHomeomorph.coe_trans, Function.comp_apply, hψy] at h
    refine (h₂.comp y h₁).congr_of_eventuallyEq ?_
    filter_upwards [(chartAt H y).open_source.mem_nhds (mem_chart_source H y)] with v hv
    simp [(chartAt H y).left_inv hv, ψa]
  -- The embedding `φ j` is a transition map followed by `φ a`.
  refine (hφa.comp z (contMDiffAt_symm_comp hφ hdeck ⟨y, hy⟩)).congr_of_eventuallyEq ?_
  filter_upwards [(hφ j).continuous.continuousAt.preimage_mem_nhds
    ((hφ a).isOpen_range.mem_nhds ⟨y, hy⟩)] with v hv
  exact (hright _ hv).symm

include hdeck in
/-- The embedding of a piece, as a `C^n` diffeomorphism from the piece onto its open image. -/
noncomputable def partialDiffeomorphOfIsOpenEmbedding [∀ j, IsManifold I n (U j)] (j : J) :
    letI := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
    PartialDiffeomorph I I (U j) M n :=
  letI := chartedSpaceOfIsOpenEmbedding (H := H) hφ hcover
  { toPartialEquiv := ((hφ j).toOpenPartialHomeomorph (φ j)).toPartialEquiv
    open_source := ((hφ j).toOpenPartialHomeomorph (φ j)).open_source
    open_target := ((hφ j).toOpenPartialHomeomorph (φ j)).open_target
    contMDiffOn_toFun := (contMDiff_chartedSpaceOfIsOpenEmbedding hφ hcover hdeck j).contMDiffOn
    contMDiffOn_invFun := by
      simpa using contMDiffOn_symm_chartedSpaceOfIsOpenEmbedding hφ hcover hdeck j }

/-- The diffeomorphism of a piece onto its image is defined on the whole piece. -/
@[simp]
theorem partialDiffeomorphOfIsOpenEmbedding_source [∀ j, IsManifold I n (U j)] (j : J) :
    (partialDiffeomorphOfIsOpenEmbedding hφ hcover hdeck j).source = univ :=
  (rfl)

/-- The diffeomorphism of a piece onto its image has the image of the embedding as its target. -/
@[simp]
theorem partialDiffeomorphOfIsOpenEmbedding_target [∀ j, IsManifold I n (U j)] (j : J) :
    (partialDiffeomorphOfIsOpenEmbedding hφ hcover hdeck j).target = range (φ j) :=
  (hφ j).toOpenPartialHomeomorph_target _

/-- The diffeomorphism of a piece onto its image is the embedding of the piece. -/
@[simp]
theorem coe_partialDiffeomorphOfIsOpenEmbedding [∀ j, IsManifold I n (U j)] (j : J) :
    ⇑(partialDiffeomorphOfIsOpenEmbedding hφ hcover hdeck j) = φ j :=
  (rfl)

end TauCeti
