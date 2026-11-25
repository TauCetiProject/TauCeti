/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import TauCeti.Topology.Category.TopCat.GlueData
public import TauCeti.Topology.Category.TopCat.GlueData.Star

/-!
# Gluing two spaces along an open partial homeomorphism

Let `e : Y ⇀ X` be an open partial homeomorphism, from the open subset `e.source` of `Y` onto the
open subset `e.target` of `X`. Gluing `X` and `Y` along `e` identifies each point `y` of
`e.source` with its image `e y`, and nothing else. This is the star gluing
(`TauCeti.starGlueData`) of the two pieces `X` and `Y` about the centre `X`, the piece `X` attached
to it by the identity and the piece `Y` by `e`: `OpenPartialHomeomorph.e.glueData`, whose pieces
are indexed by `ULift Bool`, `X` at `true` and `Y` at `false`.

Both canonical maps are open embeddings, they jointly cover the glued space, and a point `x` of
`X` and a point `y` of `Y` have the same image exactly when `y ∈ e.source` and `e y = x`
(`OpenPartialHomeomorph.glueInl_eq_glueInr_iff`). The glued space is Hausdorff exactly when `X`
and `Y` are and the graph of `e` on its source is closed in `Y × X`
(`OpenPartialHomeomorph.t2Space_glueData_iff`): `e` must not converge at any point of the frontier
of its source. For the double of `X` along an open subset `U`, the gluing along the identity of
`U`, this holds exactly when `U` is closed.

**Cylindrical ends.** Let `X` be the interior of a manifold with boundary `S`, and `e` a collar
`S × ℝ ⇀ X` with source `S × (-∞, 0)`, the boundary sitting at `t = 0`. Gluing along `e` continues
the collar coordinate `t` to all of `ℝ`: outside `X`, the glued space is the end `S × [0, ∞)`
(`OpenPartialHomeomorph.bijOn_glueInr_Ici`). It is Hausdorff as soon as the collar extends
continuously to `S × (-∞, 0]` in a Hausdorff space containing `X`, with the slice `S × {0}`
outside `X` (`OpenPartialHomeomorph.t2Space_glueData_of_continuousOn`, with
`F = S × (-∞, 0]`). For the collar of the boundary of a Liouville domain `W` by the backward
Liouville flow, this is the underlying space `W ∪ (∂W × [0, ∞))` of the completion of `W`, in the
logarithm `t = log r` of its radial coordinate `r`.

## Main declarations

* `OpenPartialHomeomorph.glueData`: `X` and `Y` glued along `e`.
* `OpenPartialHomeomorph.glueInl`, `OpenPartialHomeomorph.glueInr`: the canonical open
  embeddings of `X` and `Y`.
* `OpenPartialHomeomorph.glueInl_eq_glueInr_iff`: the gluing relation.
* `OpenPartialHomeomorph.range_glueInl_union_range_glueInr`: the two pieces cover the glued space.
* `OpenPartialHomeomorph.compl_range_glueInl`, `OpenPartialHomeomorph.compl_range_glueInr`:
  outside one piece, the glued space is the image of the rest of the other piece.
* `OpenPartialHomeomorph.t2Space_glueData_iff`: the Hausdorff criterion.
* `OpenPartialHomeomorph.bijOn_glueInr_Ici`: outside `X`, a space with a cylindrical end `S × ℝ`
  attached along `S × (-∞, 0)` is the end `S × [0, ∞)`.
* `OpenPartialHomeomorph.t2Space_glueData_of_continuousOn`: the glued space is Hausdorff when `e`
  extends continuously beyond its source, for instance a collar to the boundary.

## References

* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  §2(a) (the completion of a Liouville domain).
-/

public section

open CategoryTheory TopologicalSpace Set Topology

universe u

namespace TauCeti

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

variable (X Y) in
/-- The two pieces of a gluing of `X` and `Y`: `X` at `true` and `Y` at `false`. -/
@[expose] def partialHomeomorphGluePiece : ULift.{u} Bool → Type u
  | ⟨true⟩ => X
  | ⟨false⟩ => Y

/-- The topologies of the two pieces of a gluing of `X` and `Y`. -/
instance instTopologicalSpacePartialHomeomorphGluePiece :
    ∀ i, TopologicalSpace (partialHomeomorphGluePiece X Y i)
  | ⟨true⟩ => inferInstanceAs (TopologicalSpace X)
  | ⟨false⟩ => inferInstanceAs (TopologicalSpace Y)

end TauCeti

namespace OpenPartialHomeomorph

open TauCeti

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]

variable (e : OpenPartialHomeomorph Y X)

/-- The attaching sets of the two pieces: all of `X`, and the source of `e` in `Y`. -/
@[expose] def glueSource : ∀ i, Opens (partialHomeomorphGluePiece X Y i)
  | ⟨true⟩ => ⊤
  | ⟨false⟩ => ⟨e.source, e.open_source⟩

/-- The images of the attaching sets of the two pieces in `X`: all of `X`, and the target of
`e`. -/
@[expose] def glueTarget : ULift.{u} Bool → Opens X
  | ⟨true⟩ => ⊤
  | ⟨false⟩ => ⟨e.target, e.open_target⟩

/-- The attaching maps of the two pieces to `X`: the identity of `X`, and `e` from its source onto
its target. -/
@[expose] def glueMap : ∀ i, e.glueSource i ≃ₜ e.glueTarget i
  | ⟨true⟩ => Homeomorph.refl _
  | ⟨false⟩ => e.toHomeomorphSourceTarget

/-- **The gluing of `X` and `Y` along an open partial homeomorphism `e : Y ⇀ X`**: every point `y`
of the source of `e` is identified with `e y`. The pieces are `X` at `true` and `Y` at `false`. -/
noncomputable abbrev glueData : TopCat.GlueData.{u} :=
  starGlueData e.glueMap

/-- The canonical map of `X` into the gluing along `e`. -/
noncomputable def glueInl : C(X, e.glueData.toGlueData.glued) :=
  (e.glueData.toGlueData.ι ⟨true⟩).hom

/-- The canonical map of `Y` into the gluing along `e`. -/
noncomputable def glueInr : C(Y, e.glueData.toGlueData.glued) :=
  (e.glueData.toGlueData.ι ⟨false⟩).hom

/-- The canonical map of `X` into the gluing along `e` is the canonical map of its piece. -/
theorem coe_glueInl :
    ⇑(e.glueInl) = e.glueData.toGlueData.ι ⟨true⟩ :=
  (rfl)

/-- The canonical map of `Y` into the gluing along `e` is the canonical map of its piece. -/
theorem coe_glueInr :
    ⇑(e.glueInr) = e.glueData.toGlueData.ι ⟨false⟩ :=
  (rfl)

/-- The canonical map of `X` into the gluing along `e` is an open embedding. -/
theorem isOpenEmbedding_glueInl : IsOpenEmbedding (e.glueInl) :=
  e.glueData.ι_isOpenEmbedding ⟨true⟩

/-- The canonical map of `Y` into the gluing along `e` is an open embedding. -/
theorem isOpenEmbedding_glueInr : IsOpenEmbedding (e.glueInr) :=
  e.glueData.ι_isOpenEmbedding ⟨false⟩

variable {e}

/-- **The gluing relation.** A point `x` of `X` and a point `y` of `Y` have the same image in the
gluing along `e` exactly when `y` lies in the source of `e` and `e y = x`. -/
@[simp]
theorem glueInl_eq_glueInr_iff {x : X} {y : Y} :
    e.glueInl x = e.glueInr y ↔ y ∈ e.source ∧ e y = x :=
  (starGlueData_ι_eq_iff_of_ne (ψ := e.glueMap) (i := ⟨true⟩) (j := ⟨false⟩)
    (by simp) (x := x) (y := y)).trans ⟨fun ⟨_, hy, h⟩ ↦ ⟨hy, h.symm⟩, fun ⟨hy, h⟩ ↦
      ⟨trivial, hy, h.symm⟩⟩

/-- A point of the source of `e` and its image under `e` have the same image in the gluing along
`e`. -/
theorem glueInl_apply {y : Y} (hy : y ∈ e.source) :
    e.glueInl (e y) = e.glueInr y :=
  glueInl_eq_glueInr_iff.2 ⟨hy, rfl⟩

variable (e) in
/-- The images of `X` and `Y` cover the gluing along `e`. -/
theorem range_glueInl_union_range_glueInr :
    range (e.glueInl) ∪ range (e.glueInr) = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  obtain ⟨⟨b⟩, w, rfl⟩ := e.glueData.ι_jointly_surjective z
  cases b
  · exact Or.inr ⟨w, rfl⟩
  · exact Or.inl ⟨w, rfl⟩

/-- The points of the gluing along `e` outside the image of `X` are the images of the points of `Y`
outside the source of `e`. -/
theorem compl_range_glueInl :
    (range (e.glueInl))ᶜ = e.glueInr '' e.sourceᶜ := by
  ext z
  refine ⟨fun hz ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ :=
      (range_glueInl_union_range_glueInr e).symm ▸
        mem_univ z
    · exact (hz ⟨x, rfl⟩).elim
    · exact ⟨y, fun hy ↦ hz ⟨e y, glueInl_apply hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩ ⟨x, hx⟩
    exact hy (glueInl_eq_glueInr_iff.1 hx).1

/-- The points of the gluing along `e` outside the image of `Y` are the images of the points of `X`
outside the target of `e`. -/
theorem compl_range_glueInr :
    (range (e.glueInr))ᶜ = e.glueInl '' e.targetᶜ := by
  ext z
  refine ⟨fun hz ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ :=
      (range_glueInl_union_range_glueInr e).symm ▸
        mem_univ z
    · refine ⟨x, fun hx ↦ hz ⟨e.symm x, ?_⟩, rfl⟩
      rw [← glueInl_apply (e.map_target hx), e.right_inv hx]
    · exact (hz ⟨y, rfl⟩).elim
  · rintro ⟨x, hx, rfl⟩ ⟨y, hy⟩
    obtain ⟨hys, rfl⟩ := glueInl_eq_glueInr_iff.1 hy.symm
    exact hx (e.map_source hys)

/-- The relation between the piece `X` and the piece `Y` of the gluing along `e` is the graph of
`e`, read with its two factors exchanged. -/
private theorem chartRel_true_false :
    e.glueData.chartRel ⟨true⟩ ⟨false⟩ = Prod.swap ⁻¹' e.source.graphOn e :=
  Set.ext fun p ↦ e.glueData.mem_chartRel_iff.trans
    (glueInl_eq_glueInr_iff.trans (Set.mem_graphOn (x := p.swap)).symm)

/-- **Hausdorff criterion for the gluing along an open partial homeomorphism.** The gluing of `X`
and `Y` along `e` is Hausdorff exactly when `X` and `Y` are Hausdorff and the graph
`{(y, e y) | y ∈ e.source}` of `e` on its source is closed in `Y × X`. -/
theorem t2Space_glueData_iff :
    T2Space e.glueData.toGlueData.glued ↔
      T2Space X ∧ T2Space Y ∧ IsClosed (e.source.graphOn e) := by
  -- The relation of a piece with itself is the diagonal of that piece.
  have hdiag (i : ULift.{u} Bool) : e.glueData.chartRel i i =
      diagonal (partialHomeomorphGluePiece X Y i) :=
    Set.ext fun _ ↦ e.glueData.mem_chartRel_iff.trans
      (e.glueData.ι_isOpenEmbedding i).injective.eq_iff
  -- The relation of `Y` with `X` is the graph of `e`.
  have hswap : e.glueData.chartRel ⟨false⟩ ⟨true⟩ =
      e.source.graphOn e :=
    Set.ext fun p ↦ e.glueData.swap_mem_chartRel_iff.symm.trans <| by
      rw [chartRel_true_false]
      rfl
  rw [e.glueData.t2Space_iff_isClosed_chartRel]
  refine ⟨fun h ↦ ⟨?_, ?_, hswap ▸ h ⟨false⟩ ⟨true⟩⟩, fun ⟨hX, hY, hg⟩ ↦ ?_⟩
  · have h' := h ⟨true⟩ ⟨true⟩
    rw [hdiag] at h'
    exact t2_iff_isClosed_diagonal.2 h'
  · have h' := h ⟨false⟩ ⟨false⟩
    rw [hdiag] at h'
    exact t2_iff_isClosed_diagonal.2 h'
  rintro ⟨i⟩ ⟨j⟩
  cases i <;> cases j
  · exact hdiag ⟨false⟩ ▸ t2_iff_isClosed_diagonal.1 hY
  · exact hswap ▸ hg
  · rw [chartRel_true_false]
    exact hg.preimage continuous_swap
  · exact hdiag ⟨true⟩ ▸ t2_iff_isClosed_diagonal.1 hX

/-- The gluing of Hausdorff spaces along an open partial homeomorphism with closed graph is
Hausdorff. -/
theorem t2Space_glueData [T2Space X] [T2Space Y]
    (he : IsClosed (e.source.graphOn e)) :
    T2Space e.glueData.toGlueData.glued :=
  t2Space_glueData_iff.2 ⟨‹_›, ‹_›, he⟩

/-- **The graph of a partial homeomorphism that extends beyond its source is closed.** Let
`j : X → W` be a continuous injection into a Hausdorff space, and `F` a closed subset of `Y`
containing the source of `e`. If `e` followed by `j` extends to a map `c` continuous on `F` which
sends the points of `F` outside the source of `e` outside the image of `j`, then the graph of `e`
on its source is closed in `Y × X`.

This is the situation of a collar `(s, t) ↦ φ_t(s)`, `t < 0`, of the boundary `S` of a manifold
with boundary `W` by the backward flow of an outward vector field, with `X` the interior of `W` and
`F = S × (-∞, 0]`. -/
theorem isClosed_graphOn_source_of_continuousOn {W : Type*} [TopologicalSpace W] [T2Space W]
    {j : X → W} (hj : Continuous j) (hj' : Function.Injective j) {c : Y → W} {F : Set Y}
    (hF : IsClosed F) (hc : ContinuousOn c F) (hsF : e.source ⊆ F)
    (hce : ∀ y ∈ e.source, c y = j (e y)) (hcF : ∀ y ∈ F \ e.source, c y ∉ range j) :
    IsClosed (e.source.graphOn e) := by
  -- The graph lies in the closed set of pairs `(y, x)` with `y ∈ F` and `c y = j x`.
  have hK : IsClosed ({p : Y × X | p.1 ∈ F} ∩
      (fun p : Y × X ↦ (c p.1, j p.2)) ⁻¹' diagonal W) :=
    ((hc.comp continuous_fst.continuousOn fun _ hp ↦ hp).prodMk
      (hj.comp continuous_snd).continuousOn).preimage_isClosed_of_isClosed
      (hF.preimage continuous_fst) isClosed_diagonal
  have hsub : e.source.graphOn e ⊆ {p : Y × X | p.1 ∈ F} ∩
      (fun p : Y × X ↦ (c p.1, j p.2)) ⁻¹' diagonal W := by
    rintro ⟨y, x⟩ hyx
    obtain ⟨hy, hyx⟩ := Set.mem_graphOn.1 hyx
    exact ⟨hsF hy, (hce y hy).trans (congrArg j hyx)⟩
  refine isClosed_of_closure_subset fun p hp ↦ ?_
  obtain ⟨hpF, hpc⟩ := hK.closure_subset_iff.2 hsub hp
  have hpc' : c p.1 = j p.2 := hpc
  -- The point `p.1` lies in `F` and `c` sends it into the image of `j`, so it lies in the source.
  have hps : p.1 ∈ e.source := of_not_not fun h ↦ hcF p.1 ⟨hpF, h⟩ ⟨p.2, hpc'.symm⟩
  exact Set.mem_graphOn.2 ⟨hps, hj' ((hce p.1 hps).symm.trans hpc')⟩

/-- **Hausdorffness from an extension beyond the source.** The gluing of a space `X` with a
Hausdorff space `Y` along `e` is Hausdorff when `e` extends as in
`OpenPartialHomeomorph.isClosed_graphOn_source_of_continuousOn`; then `X` is Hausdorff, since it
injects continuously into a Hausdorff space. -/
theorem t2Space_glueData_of_continuousOn [T2Space Y] {W : Type*} [TopologicalSpace W] [T2Space W]
    {j : X → W} (hj : Continuous j) (hj' : Function.Injective j) {c : Y → W} {F : Set Y}
    (hF : IsClosed F) (hc : ContinuousOn c F) (hsF : e.source ⊆ F)
    (hce : ∀ y ∈ e.source, c y = j (e y)) (hcF : ∀ y ∈ F \ e.source, c y ∉ range j) :
    T2Space e.glueData.toGlueData.glued :=
  haveI : T2Space X := .of_injective_continuous hj' hj
  t2Space_glueData (isClosed_graphOn_source_of_continuousOn hj hj' hF hc hsF hce hcF)

/-! ### Cylindrical ends -/

section CylindricalEnd

variable {S : Type u} [TopologicalSpace S] {e : OpenPartialHomeomorph (S × ℝ) X}

/-- **The end of a space with a cylindrical end attached.** Let `X` be glued to `S × ℝ` along `e`
with source `S × (-∞, 0)`, a collar of a missing boundary `S × {0}`. Then the canonical map of the
cylinder is a bijection from the end `S × [0, ∞)` onto the complement of `X` in the glued space. -/
theorem bijOn_glueInr_Ici (he : e.source = {p | p.2 < 0}) :
    BijOn e.glueInr {p | 0 ≤ p.2} (range e.glueInl)ᶜ := by
  have hc : e.sourceᶜ = {p : S × ℝ | 0 ≤ p.2} := by
    ext p
    simp [he]
  rw [compl_range_glueInl, hc]
  exact (isOpenEmbedding_glueInr e).injective.injOn.bijOn_image

end CylindricalEnd

end OpenPartialHomeomorph
