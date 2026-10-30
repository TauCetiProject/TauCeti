/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Gluing
public import TauCeti.Geometry.Manifold.Gluing.Basic

/-!
# Manifold atlases on spaces glued from open pieces

Let `D : TopCat.GlueData` glue spaces `D.U i` along open subspaces `D.V (i, j)`, and suppose all the
pieces and overlaps are charted spaces modelled on one space `H`. The canonical maps
`D.toGlueData.ι i` are open embeddings that jointly cover the glued space, so transporting charts
along them gives the glued space a charted-space structure, `TopCat.GlueData.chartedSpace`.

The overlap `D.V (i, j)` maps to its two adjacent pieces, by `D.f i j` into `D.U i` and by
`D.f j i ∘ D.t i j` into `D.U j`. The pieces and overlaps are *compatible*,
`TopCat.GlueData.IsCompatible I n`, when both maps are `C^n` local diffeomorphisms: the atlas of
the overlap is then compatible with the atlases of both pieces, and the second map records the
transition between the pieces. If moreover every piece is a `C^n` manifold, then the glued space
is a `C^n` manifold and every canonical map is a `C^n` local diffeomorphism, hence a `C^n`
diffeomorphism onto its open image.
For `𝕜 = ℂ` this glues complex manifolds along holomorphic transitions.

The relation identifying points of different pieces is consumed through `D.ι_eq_iff_rel`; it is
not copied into a new structure. Empty pieces need no special treatment.

## Main declarations

* `TopCat.GlueData.chartedSpace`: the atlas on the glued space transported from the pieces.
* `TopCat.GlueData.IsCompatible`: the overlap compatibility condition.
* `TopCat.GlueData.IsCompatible.isManifold`: compatible pieces glue to a `C^n` manifold.
* `TopCat.GlueData.IsCompatible.isLocalDiffeomorph_ι`: the canonical maps are `C^n` local
  diffeomorphisms.
* `TopCat.GlueData.IsCompatible.partialDiffeomorphι`: a canonical map as a `C^n` diffeomorphism
  from a piece onto its image.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the smooth manifold chart lemma).
* Shoshichi Kobayashi and Katsumi Nomizu, *Foundations of Differential Geometry*, Volume I,
  Chapter I (atlases compatible with a pseudogroup).
-/

public section

open Set Filter Topology IsManifold
open scoped Manifold ContDiff

namespace TopCat.GlueData

universe u

variable (D : TopCat.GlueData.{u}) {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω} [∀ i, ChartedSpace H (D.U i)]

variable (H) in
/-- The charted-space structure on the glued space of `D`: the chart at a point is the inverse of
the canonical map of a piece containing it, followed by a chart of that piece. Its body is exposed
so that the lemmas about `TauCeti.chartedSpaceOfIsOpenEmbedding` apply to it directly. -/
@[expose, instance_reducible]
noncomputable def chartedSpace : ChartedSpace H D.toGlueData.glued :=
  TauCeti.chartedSpaceOfIsOpenEmbedding D.ι_isOpenEmbedding D.ι_jointly_surjective

/-- Every chart of `D.chartedSpace H` is the inverse of the canonical map of a piece followed by a
chart of that piece. -/
theorem exists_chartAt_chartedSpace_eq (x : D.toGlueData.glued) :
    ∃ (i : D.J) (y : D.U i), D.toGlueData.ι i y = x ∧
      haveI : Nonempty (D.U i) := ⟨y⟩
      @chartAt H _ _ _ (D.chartedSpace H) x =
        ((D.ι_isOpenEmbedding i).toOpenPartialHomeomorph _).symm.trans (chartAt H y) :=
  TauCeti.exists_chartAt_chartedSpaceOfIsOpenEmbedding_eq D.ι_isOpenEmbedding
    D.ι_jointly_surjective x

variable [∀ ij, ChartedSpace H (D.V ij)]

variable (I n) in
/-- The atlases of the pieces and overlaps of `D` are `C^n` compatible when both maps from an
overlap `D.V (i, j)` to its adjacent pieces, `D.f i j` to `D.U i` and `D.f j i ∘ D.t i j` to
`D.U j`, are `C^n` local diffeomorphisms. -/
structure IsCompatible : Prop where
  /-- The inclusion of an overlap into the first adjacent piece is a local diffeomorphism. -/
  isLocalDiffeomorph_f (i j : D.J) : IsLocalDiffeomorph I I n (D.f i j)
  /-- The transition from an overlap into the second adjacent piece is a local diffeomorphism. -/
  isLocalDiffeomorph_f_comp_t (i j : D.J) : IsLocalDiffeomorph I I n (D.f j i ∘ D.t i j)

variable {D}

/-- If the inclusions `D.f i j` and the transitions `D.t i j` are `C^n` local diffeomorphisms,
then the pieces and overlaps of `D` are `C^n` compatible. -/
theorem IsCompatible.of_isLocalDiffeomorph_t (hf : ∀ i j, IsLocalDiffeomorph I I n (D.f i j))
    (ht : ∀ i j, IsLocalDiffeomorph I I n (D.t i j)) : D.IsCompatible I n where
  isLocalDiffeomorph_f := hf
  isLocalDiffeomorph_f_comp_t i j x := (ht i j x).comp (hg := hf j i (D.t i j x))

/-- **Transitions of a compatible gluing.** If a point `x` of the piece `D.U i` and a point `y` of
the piece `D.U j` have the same image in the glued space, then near `x` the canonical map of `D.U i`
factors through that of `D.U j` along a map that is `C^n` at `x`. -/
theorem IsCompatible.exists_contMDiffAt_transition (h : D.IsCompatible I n) {i j : D.J}
    {x : D.U i} {y : D.U j} (hxy : D.toGlueData.ι i x = D.toGlueData.ι j y) :
    ∃ T : D.U i → D.U j, ContMDiffAt I I n T x ∧
      D.toGlueData.ι j ∘ T =ᶠ[𝓝 x] D.toGlueData.ι i := by
  obtain ⟨z, rfl, -⟩ : ∃ z : D.V (i, j), D.f i j z = x ∧ D.f j i (D.t i j z) = y :=
    (D.ι_eq_iff_rel i j x y).1 hxy
  have hz := h.isLocalDiffeomorph_f i j z
  refine ⟨(D.f j i ∘ D.t i j) ∘ hz.localInverse,
    (h.isLocalDiffeomorph_f_comp_t i j).contMDiff.contMDiffAt.comp _ hz.contMDiffAt_localInverse,
    ?_⟩
  filter_upwards [hz.localInverse_eventuallyEq_right] with w hw
  simp only [Function.comp_apply, id_eq] at hw ⊢
  rw [D.glue_condition_apply, hw]

variable [∀ i, IsManifold I n (D.U i)]

/-- **Compatible open gluing.** If the pieces of `D` are `C^n` manifolds whose atlases are
compatible with those of the overlaps, then the glued space is a `C^n` manifold. -/
theorem IsCompatible.isManifold (h : D.IsCompatible I n) :
    letI := D.chartedSpace H
    IsManifold I n D.toGlueData.glued :=
  TauCeti.isManifold_chartedSpaceOfIsOpenEmbedding D.ι_isOpenEmbedding D.ι_jointly_surjective
    fun _ _ _ _ ↦ h.exists_contMDiffAt_transition

/-- The canonical map of a piece into a compatible gluing is `C^n`. -/
theorem IsCompatible.contMDiff_ι (h : D.IsCompatible I n) (i : D.J) :
    letI := D.chartedSpace H
    ContMDiff I I n (D.toGlueData.ι i) :=
  TauCeti.contMDiff_chartedSpaceOfIsOpenEmbedding D.ι_isOpenEmbedding D.ι_jointly_surjective
    (fun _ _ _ _ ↦ h.exists_contMDiffAt_transition) i

/-- The inverse of the canonical map of a nonempty piece into a compatible gluing is `C^n` on the
image of that piece. -/
theorem IsCompatible.contMDiffOn_ι_symm (h : D.IsCompatible I n) (i : D.J) [Nonempty (D.U i)] :
    letI := D.chartedSpace H
    ContMDiffOn I I n ((D.ι_isOpenEmbedding i).toOpenPartialHomeomorph _).symm
      (range (D.toGlueData.ι i)) :=
  TauCeti.contMDiffOn_symm_chartedSpaceOfIsOpenEmbedding D.ι_isOpenEmbedding
    D.ι_jointly_surjective (fun _ _ _ _ ↦ h.exists_contMDiffAt_transition) i

/-- The canonical map of a nonempty piece into a compatible gluing, as a `C^n` diffeomorphism from
the piece onto its open image. -/
noncomputable def IsCompatible.partialDiffeomorphι (h : D.IsCompatible I n) (i : D.J)
    [Nonempty (D.U i)] :
    letI := D.chartedSpace H
    PartialDiffeomorph I I (D.U i) D.toGlueData.glued n :=
  TauCeti.partialDiffeomorphOfIsOpenEmbedding D.ι_isOpenEmbedding D.ι_jointly_surjective
    (fun _ _ _ _ ↦ h.exists_contMDiffAt_transition) i

/-- The diffeomorphism of a piece onto its image in a compatible gluing is defined on the whole
piece. -/
@[simp]
theorem IsCompatible.partialDiffeomorphι_source (h : D.IsCompatible I n) (i : D.J)
    [Nonempty (D.U i)] : (h.partialDiffeomorphι i).source = univ :=
  TauCeti.partialDiffeomorphOfIsOpenEmbedding_source _ _ _ i

/-- The diffeomorphism of a piece onto its image in a compatible gluing has the image of the
canonical map as its target. -/
@[simp]
theorem IsCompatible.partialDiffeomorphι_target (h : D.IsCompatible I n) (i : D.J)
    [Nonempty (D.U i)] : (h.partialDiffeomorphι i).target = range (D.toGlueData.ι i) :=
  TauCeti.partialDiffeomorphOfIsOpenEmbedding_target _ _ _ i

/-- The diffeomorphism of a piece onto its image in a compatible gluing is the canonical map. -/
@[simp]
theorem IsCompatible.coe_partialDiffeomorphι (h : D.IsCompatible I n) (i : D.J)
    [Nonempty (D.U i)] : ⇑(h.partialDiffeomorphι i) = D.toGlueData.ι i :=
  TauCeti.coe_partialDiffeomorphOfIsOpenEmbedding _ _ _ i

/-- The canonical map of a piece into a compatible gluing is a `C^n` local diffeomorphism. -/
theorem IsCompatible.isLocalDiffeomorph_ι (h : D.IsCompatible I n) (i : D.J) :
    letI := D.chartedSpace H
    IsLocalDiffeomorph I I n (D.toGlueData.ι i) :=
  TauCeti.isLocalDiffeomorph_chartedSpaceOfIsOpenEmbedding D.ι_isOpenEmbedding
    D.ι_jointly_surjective (fun _ _ _ _ ↦ h.exists_contMDiffAt_transition) i

/-- **Smooth maps out of a compatible gluing.** A map out of the glued space is `C^n` exactly when
its composite with the canonical map of every piece is `C^n`. -/
theorem IsCompatible.contMDiff_iff (h : D.IsCompatible I n) {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {g : D.toGlueData.glued → N} :
    letI := D.chartedSpace H
    ContMDiff I I' n g ↔ ∀ i, ContMDiff I I' n (g ∘ D.toGlueData.ι i) :=
  TauCeti.contMDiff_iff_chartedSpaceOfIsOpenEmbedding D.ι_isOpenEmbedding D.ι_jointly_surjective
    fun _ _ _ _ ↦ h.exists_contMDiffAt_transition

end TopCat.GlueData
