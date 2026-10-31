/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Gluing
public import TauCeti.Geometry.Manifold.Gluing
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition

/-!
# Manifolds glued from `TopCat.GlueData`

Let `D : TopCat.GlueData` be gluing data whose pieces `D.U i` and overlaps `D.V (i, j)` carry
charted-space structures modelled on a common space `H`. The glued space `D.toGlueData.glued`
receives the atlas `TopCat.GlueData.chartedSpace`, obtained by transporting the charts of each
piece along the open embedding `D.toGlueData.ι i`; this is the open-cover atlas
`TauCeti.chartedSpaceOfIsOpenEmbedding` applied to the canonical inclusions.

The overlap atlases are *compatible* with the pieces, `TopCat.GlueData.ContMDiffCompatible`, when
both canonical maps out of each overlap, the inclusion `D.f i j : D.V (i, j) → D.U i` and the
composite `x ↦ D.f j i (D.t i j x) : D.V (i, j) → D.U j`, are `C^n` local diffeomorphisms. The
second condition records the transition equation: since the overlap atlases are chosen
independently, smoothness of `D.t i j` alone would say nothing about the pieces. Equivalently, every
inclusion `D.f i j` and every transition `D.t i j` is a `C^n` local diffeomorphism
(`TopCat.GlueData.contMDiffCompatible_iff`).

For compatible data whose pieces are `C^n` manifolds, the glued space is a `C^n` manifold, every
canonical inclusion `D.toGlueData.ι i` is a `C^n` local diffeomorphism onto its open image, and a
map out of the glued space is `C^m`, for `m ≤ n`, exactly when its restriction to every piece is.
Over `𝓘(ℂ, E)` at `n = ∞` this glues complex manifolds, and the inclusions are local
biholomorphisms. No piece is required to be nonempty.

## Main declarations

* `TopCat.GlueData.chartedSpace`: the atlas of the glued space transported from the pieces.
* `TopCat.GlueData.ContMDiffCompatible`: compatibility of the overlap atlases with the pieces.
* `TopCat.GlueData.contMDiffCompatible_iff`: compatibility means that the overlap inclusions and
  the transition maps are local diffeomorphisms.
* `TopCat.GlueData.ContMDiffCompatible.isManifold_chartedSpace`: compatible manifold pieces glue to
  a manifold.
* `TopCat.GlueData.ContMDiffCompatible.isLocalDiffeomorph_ι`: the canonical inclusions are local
  diffeomorphisms.
* `TopCat.GlueData.ContMDiffCompatible.contMDiff_iff_comp_ι`: smoothness of a map out of the glued
  manifold is tested on the pieces.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Chapter 1 (the smooth manifold chart lemma).
* Shoshichi Kobayashi and Katsumi Nomizu, *Foundations of Differential Geometry*, Volume I,
  Chapter I, for atlases compatible with a pseudogroup.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace TopCat.GlueData

universe u

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} {n : ℕ∞ω}
  (D : TopCat.GlueData.{u}) [∀ i, ChartedSpace H (D.U i)]

/-! ### The atlas of the glued space -/

variable (H) in
/-- The atlas of the glued space: the chart at a point is the inverse of the canonical inclusion of
a piece containing it, followed by a chart of that piece. -/
@[instance_reducible]
protected noncomputable def chartedSpace : ChartedSpace H D.toGlueData.glued :=
  TauCeti.chartedSpaceOfIsOpenEmbedding (fun i ↦ D.ι_isOpenEmbedding i) D.ι_jointly_surjective

/-! ### Compatible overlap atlases -/

variable [∀ ij, ChartedSpace H (D.V ij)]

variable (I n) in
/-- The overlap atlases of gluing data are `C^n` compatible with the atlases of the pieces when
both canonical maps out of every overlap `D.V (i, j)`, into `D.U i` by `D.f i j` and into `D.U j`
by `D.f j i ∘ D.t i j`, are `C^n` local diffeomorphisms. -/
structure ContMDiffCompatible : Prop where
  /-- The inclusion of an overlap into the first piece is a local diffeomorphism. -/
  isLocalDiffeomorph_f (i j : D.J) : IsLocalDiffeomorph I I n (D.f i j)
  /-- The transition from an overlap into the second piece is a local diffeomorphism. -/
  isLocalDiffeomorph_f_comp_t (i j : D.J) :
    IsLocalDiffeomorph I I n fun x : D.V (i, j) ↦ D.f j i (D.t i j x)

variable {D}

namespace ContMDiffCompatible

/-- For compatible overlap atlases, every transition map `D.t i j` is a local diffeomorphism. -/
theorem isLocalDiffeomorph_t (h : D.ContMDiffCompatible I n) (i j : D.J) :
    IsLocalDiffeomorph I I n (D.t i j) := fun x ↦
  (h.isLocalDiffeomorph_f_comp_t i j x).of_comp_left (h.isLocalDiffeomorph_f j i _)
    (D.t i j).hom.continuous.continuousAt

end ContMDiffCompatible

/-- The overlap atlases are compatible with the pieces exactly when every overlap inclusion
`D.f i j` and every transition map `D.t i j` is a `C^n` local diffeomorphism. -/
theorem contMDiffCompatible_iff :
    D.ContMDiffCompatible I n ↔
      (∀ i j, IsLocalDiffeomorph I I n (D.f i j)) ∧ ∀ i j, IsLocalDiffeomorph I I n (D.t i j) :=
  ⟨fun h ↦ ⟨h.isLocalDiffeomorph_f, h.isLocalDiffeomorph_t⟩, fun ⟨hf, ht⟩ ↦
    ⟨hf, fun i j x ↦ (ht i j x).comp (hg := hf j i _)⟩⟩

namespace ContMDiffCompatible

/-- For compatible overlap atlases, two points of the pieces with the same image in the glued space
are related by a map between the pieces which is `C^n` at the first point and commutes with the
canonical inclusions near it: the transition through the overlap. -/
theorem exists_contMDiffAt_transition (h : D.ContMDiffCompatible I n) {i j : D.J} {x : D.U i}
    {y : D.U j} (hxy : D.toGlueData.ι i x = D.toGlueData.ι j y) :
    ∃ T : D.U i → D.U j, ContMDiffAt I I n T x ∧
      D.toGlueData.ι j ∘ T =ᶠ[𝓝 x] D.toGlueData.ι i := by
  obtain ⟨z, rfl, rfl⟩ : ∃ z : D.V (i, j), D.f i j z = x ∧ D.f j i (D.t i j z) = y :=
    (D.ι_eq_iff_rel i j x y).1 hxy
  have hf := h.isLocalDiffeomorph_f i j z
  refine ⟨fun w ↦ D.f j i (D.t i j (hf.localInverse w)), ?_, ?_⟩
  · exact (h.isLocalDiffeomorph_f_comp_t i j z).contMDiffAt.comp_of_eq
      hf.contMDiffAt_localInverse (hf.localInverse_left_inv hf.localInverse_mem_target)
  · filter_upwards [hf.localInverse.open_source.mem_nhds hf.localInverse_mem_source] with w hw
    rw [Function.comp_apply, D.glue_condition_apply, hf.localInverse_right_inv hw]

variable [∀ i, IsManifold I n (D.U i)]

/-- Gluing `C^n` manifolds along compatible overlap atlases gives a `C^n` manifold. -/
theorem isManifold_chartedSpace (h : D.ContMDiffCompatible I n) :
    letI := D.chartedSpace H
    IsManifold I n D.toGlueData.glued :=
  TauCeti.isManifold_chartedSpaceOfIsOpenEmbedding _ D.ι_jointly_surjective
    fun _ _ _ _ hxy ↦ h.exists_contMDiffAt_transition hxy

/-- For compatible overlap atlases on `C^n` manifold pieces, the canonical inclusion of every piece
into the glued space is a `C^n` local diffeomorphism. -/
theorem isLocalDiffeomorph_ι (h : D.ContMDiffCompatible I n) (i : D.J) :
    letI := D.chartedSpace H
    IsLocalDiffeomorph I I n (D.toGlueData.ι i) := fun x ↦ by
  let := D.chartedSpace H
  have : Nonempty (D.U i) := ⟨x⟩
  let Φ := TauCeti.partialDiffeomorphOfIsOpenEmbedding (I := I) (n := n)
    (fun i ↦ D.ι_isOpenEmbedding i) D.ι_jointly_surjective
    (fun _ _ _ _ hxy ↦ h.exists_contMDiffAt_transition hxy) i
  have hΦ := Φ.isLocalDiffeomorphAt I I n (x := x) (by simp [Φ])
  rwa [TauCeti.coe_partialDiffeomorphOfIsOpenEmbedding] at hΦ

/-- For compatible overlap atlases on `C^n` manifold pieces and `m ≤ n`, a map out of the glued
space is `C^m` exactly when its composite with the canonical inclusion of every piece is. -/
theorem contMDiff_iff_comp_ι (h : D.ContMDiffCompatible I n) {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners 𝕜 E' H'}
    {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] {m : ℕ∞ω} (hm : m ≤ n)
    {g : D.toGlueData.glued → N} :
    letI := D.chartedSpace H
    ContMDiff I I' m g ↔ ∀ i, ContMDiff I I' m (g ∘ D.toGlueData.ι i) := by
  let := D.chartedSpace H
  refine ⟨fun hg i ↦ hg.comp ((h.isLocalDiffeomorph_ι i).contMDiff.of_le hm), fun hg x ↦ ?_⟩
  obtain ⟨i, y, rfl⟩ := D.ι_jointly_surjective x
  exact ((h.isLocalDiffeomorph_ι i y).contMDiffAt_comp_iff hm).1 (hg i y)

end ContMDiffCompatible

end TopCat.GlueData
