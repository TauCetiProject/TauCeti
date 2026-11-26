/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.OpenPartialHomeomorph.Basic
public import TauCeti.Topology.Category.TopCat.GlueData
public import TauCeti.Topology.Category.TopCat.GlueData.Star
public import TauCeti.Topology.ContinuousOn.ClosedGraph

/-!
# Gluing two spaces along an open partial homeomorphism

Let `e : Y ⇀ X` be an open partial homeomorphism, from the open subset `e.source` of `Y` onto the
open subset `e.target` of `X`. Gluing `X` and `Y` along `e` identifies each point `y` of
`e.source` with its image `e y`, and nothing else. This is the star gluing
(`TauCeti.starGlueData`) of the two pieces `X` and `Y` about the centre `X`, the piece `X` attached
to it by the identity and the piece `Y` by `e`: `OpenPartialHomeomorph.glueData`, whose pieces
are indexed by `ULift Bool`, `X` at `true` and `Y` at `false`.

Both canonical maps are open embeddings, they jointly cover the glued space, and a point `x` of
`X` and a point `y` of `Y` have the same image exactly when `y ∈ e.source` and `e y = x`
(`OpenPartialHomeomorph.glueInl_eq_glueInr_iff`). Continuous maps out of the glued space are
glued from continuous maps on `X` and `Y` which agree along `e`
(`OpenPartialHomeomorph.glueDesc`). The glued space is Hausdorff exactly when `X`
and `Y` are and the graph of `e` on its source is closed in `Y × X`
(`OpenPartialHomeomorph.t2Space_glueData_iff`): `e` must not converge at any point of the frontier
of its source. For the double of `X` along an open subset `U`, the gluing along the identity of
`U`, this holds exactly when `U` is closed.

Outside `X`, the glued space is the image of the complement of the source of `e`
(`OpenPartialHomeomorph.bijOn_glueInr_compl_source`).

**Cylindrical ends.** Let `X` be the interior of a manifold with boundary `S`, and `e` a collar
`S × ℝ ⇀ X` with source `S × (-∞, 0)`, the boundary sitting at `t = 0`. Gluing along `e` continues
the collar coordinate `t` to all of `ℝ`: outside `X`, the glued space is the end `S × [0, ∞)`
(`OpenPartialHomeomorph.bijOn_glueInr_Ici`, stated for any linearly ordered `R` in place of `ℝ`).
For Hausdorff `S`, it is Hausdorff as soon as the collar extends continuously to `S × (-∞, 0]` in
a Hausdorff space containing `X`, with the slice `S × {0}` outside `X`
(`OpenPartialHomeomorph.t2Space_glueData_of_continuousOn`, with `F = S × (-∞, 0]`). For the collar
of the boundary of a Liouville domain `W` by the backward Liouville flow, this is the underlying
space `W ∪ (∂W × [0, ∞))` of the completion of `W`, in the logarithm `t = log r` of its radial
coordinate `r`.

## Main declarations

* `OpenPartialHomeomorph.glueData`: `X` and `Y` glued along `e`.
* `OpenPartialHomeomorph.glueInl`, `OpenPartialHomeomorph.glueInr`: the canonical open
  embeddings of `X` and `Y`.
* `OpenPartialHomeomorph.glueInl_eq_glueInr_iff`: the gluing relation.
* `OpenPartialHomeomorph.glueDesc`: the continuous map out of the glued space glued from
  continuous maps on `X` and `Y` which agree along `e`.
* `OpenPartialHomeomorph.range_glueInl_union_range_glueInr`: the two pieces cover the glued space.
* `OpenPartialHomeomorph.compl_range_glueInl`, `OpenPartialHomeomorph.compl_range_glueInr`:
  outside one piece, the glued space is the image of the rest of the other piece.
* `OpenPartialHomeomorph.bijOn_glueInr_compl_source`: outside `X`, the glued space is the
  complement of the source of `e` in `Y`.
* `OpenPartialHomeomorph.t2Space_glueData_iff`: the Hausdorff criterion.
* `OpenPartialHomeomorph.bijOn_glueInr_Ici`: outside `X`, a space with a cylindrical end `S × R`
  attached along `S × (-∞, a)` is the end `S × [a, ∞)`.
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

/-- The attaching set of the piece `X` is all of `X`. -/
@[simp] theorem glueSource_true : e.glueSource ⟨true⟩ = ⊤ := (rfl)

/-- The attaching set of the piece `Y` is the source of `e`. -/
@[simp] theorem glueSource_false : e.glueSource ⟨false⟩ = ⟨e.source, e.open_source⟩ := (rfl)

/-- The piece `X` is attached onto all of `X`. -/
@[simp] theorem glueTarget_true : e.glueTarget ⟨true⟩ = ⊤ := (rfl)

/-- The piece `Y` is attached onto the target of `e`. -/
@[simp] theorem glueTarget_false : e.glueTarget ⟨false⟩ = ⟨e.target, e.open_target⟩ := (rfl)

/-- The piece `X` is attached to `X` by the identity. -/
@[simp] theorem coe_glueMap_true_apply (x : e.glueSource ⟨true⟩) :
    (e.glueMap ⟨true⟩ x : X) = (x : partialHomeomorphGluePiece X Y ⟨true⟩) :=
  (rfl)

/-- The piece `Y` is attached to `X` by `e`. -/
@[simp] theorem coe_glueMap_false_apply (y : e.glueSource ⟨false⟩) :
    (e.glueMap ⟨false⟩ y : X) = e (y : partialHomeomorphGluePiece X Y ⟨false⟩) :=
  (rfl)

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
    (by simp) (x := x) (y := y)).trans <| by
    simp only [coe_glueMap_true_apply, coe_glueMap_false_apply]
    exact ⟨fun ⟨_, hy, h⟩ ↦ ⟨hy, h.symm⟩, fun ⟨hy, h⟩ ↦ ⟨trivial, hy, h.symm⟩⟩

/-- The gluing relation, read from the piece `Y`. -/
@[simp]
theorem glueInr_eq_glueInl_iff {x : X} {y : Y} :
    e.glueInr y = e.glueInl x ↔ y ∈ e.source ∧ e y = x :=
  eq_comm.trans glueInl_eq_glueInr_iff

/-- Distinct points of `X` stay distinct in the gluing along `e`. -/
@[simp]
theorem glueInl_inj {x x' : X} : e.glueInl x = e.glueInl x' ↔ x = x' :=
  (isOpenEmbedding_glueInl e).injective.eq_iff

/-- Distinct points of `Y` stay distinct in the gluing along `e`. -/
@[simp]
theorem glueInr_inj {y y' : Y} : e.glueInr y = e.glueInr y' ↔ y = y' :=
  (isOpenEmbedding_glueInr e).injective.eq_iff

/-- A point of the source of `e` and its image under `e` have the same image in the gluing along
`e`. -/
theorem glueInl_apply_eq_glueInr {y : Y} (hy : y ∈ e.source) :
    e.glueInl (e y) = e.glueInr y :=
  glueInl_eq_glueInr_iff.2 ⟨hy, rfl⟩

variable (e) in
/-- Every point of the gluing along `e` is the image of a point of `X` or of a point of `Y`. -/
theorem exists_glueInl_eq_or_exists_glueInr_eq (z : e.glueData.toGlueData.glued) :
    (∃ x, e.glueInl x = z) ∨ ∃ y, e.glueInr y = z := by
  obtain ⟨⟨b⟩, w, rfl⟩ := e.glueData.ι_jointly_surjective z
  cases b
  · exact Or.inr ⟨w, rfl⟩
  · exact Or.inl ⟨w, rfl⟩

variable (e) in
/-- The images of `X` and `Y` cover the gluing along `e`. -/
theorem range_glueInl_union_range_glueInr :
    range (e.glueInl) ∪ range (e.glueInr) = univ :=
  eq_univ_of_forall (exists_glueInl_eq_or_exists_glueInr_eq e)

/-- The points of the gluing along `e` outside the image of `X` are the images of the points of `Y`
outside the source of `e`. -/
theorem compl_range_glueInl :
    (range (e.glueInl))ᶜ = e.glueInr '' e.sourceᶜ := by
  ext z
  refine ⟨fun hz ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := exists_glueInl_eq_or_exists_glueInr_eq e z
    · exact (hz ⟨x, rfl⟩).elim
    · exact ⟨y, fun hy ↦ hz ⟨e y, glueInl_apply_eq_glueInr hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩ ⟨x, hx⟩
    exact hy (glueInl_eq_glueInr_iff.1 hx).1

/-- The points of the gluing along `e` outside the image of `Y` are the images of the points of `X`
outside the target of `e`. -/
theorem compl_range_glueInr :
    (range (e.glueInr))ᶜ = e.glueInl '' e.targetᶜ := by
  ext z
  refine ⟨fun hz ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := exists_glueInl_eq_or_exists_glueInr_eq e z
    · refine ⟨x, fun hx ↦ hz ⟨e.symm x, ?_⟩, rfl⟩
      rw [← glueInl_apply_eq_glueInr (e.map_target hx), e.right_inv hx]
    · exact (hz ⟨y, rfl⟩).elim
  · rintro ⟨x, hx, rfl⟩ ⟨y, hy⟩
    obtain ⟨hys, rfl⟩ := glueInl_eq_glueInr_iff.1 hy.symm
    exact hx (e.map_source hys)

variable (e) in
/-- The canonical map of `Y` is a bijection from the complement of the source of `e` onto the
complement of the image of `X` in the gluing along `e`. -/
theorem bijOn_glueInr_compl_source : BijOn e.glueInr e.sourceᶜ (range e.glueInl)ᶜ := by
  rw [compl_range_glueInl]
  exact (isOpenEmbedding_glueInr e).injective.injOn.bijOn_image

variable (e) in
/-- The canonical map of `X` is a bijection from the complement of the target of `e` onto the
complement of the image of `Y` in the gluing along `e`. -/
theorem bijOn_glueInl_compl_target : BijOn e.glueInl e.targetᶜ (range e.glueInr)ᶜ := by
  rw [compl_range_glueInr]
  exact (isOpenEmbedding_glueInl e).injective.injOn.bijOn_image

/-! ### Maps out of the gluing -/

section glueDesc

variable {Z : Type*} [TopologicalSpace Z] {f : C(X, Z)} {g : C(Y, Z)}

variable (e) in
/-- The maps `f` and `g` on the two pieces. -/
private def glueDescPiece (f : C(X, Z)) (g : C(Y, Z)) :
    ∀ i : ULift.{u} Bool, C(e.glueData.U i, Z)
  | ⟨true⟩ => f
  | ⟨false⟩ => g

/-- Maps on `X` and `Y` which agree along `e` agree on points identified in the gluing. -/
private theorem glueDescPiece_eq_of_ι_eq (h : ∀ y ∈ e.source, f (e y) = g y)
    {i j : ULift.{u} Bool} {a : e.glueData.U i} {b : e.glueData.U j}
    (hab : e.glueData.toGlueData.ι i a = e.glueData.toGlueData.ι j b) :
    glueDescPiece e f g i a = glueDescPiece e f g j b := by
  obtain ⟨⟨⟩ | ⟨⟩⟩ := i <;> obtain ⟨⟨⟩ | ⟨⟩⟩ := j
  · exact congrArg g (glueInr_inj.1 hab)
  · obtain ⟨hb, rfl⟩ := glueInr_eq_glueInl_iff.1 hab
    exact (h a hb).symm
  · obtain ⟨hb, rfl⟩ := glueInl_eq_glueInr_iff.1 hab
    exact h b hb
  · exact congrArg f (glueInl_inj.1 hab)

variable (e f g) in
/-- **Maps out of the gluing along `e`.** Continuous maps `f` on `X` and `g` on `Y` which agree
along `e`, `f (e y) = g y` on the source of `e`, glue to a continuous map on the gluing. -/
noncomputable def glueDesc (h : ∀ y ∈ e.source, f (e y) = g y) :
    C(e.glueData.toGlueData.glued, Z) :=
  IsQuotientMap.lift (f := .sigma fun i ↦ (e.glueData.toGlueData.ι i).hom)
    e.glueData.isOpenQuotientMap_sigma_ι.isQuotientMap (.sigma (glueDescPiece e f g))
    fun _ _ hab ↦ glueDescPiece_eq_of_ι_eq h hab

/-- The map glued from `f` and `g` restricts to `f` and `g` on the pieces. -/
private theorem glueDesc_comp_sigma (h : ∀ y ∈ e.source, f (e y) = g y) :
    (e.glueDesc f g h).comp (.sigma fun i ↦ (e.glueData.toGlueData.ι i).hom) =
      .sigma (glueDescPiece e f g) :=
  IsQuotientMap.lift_comp _ _ _

/-- The map glued from `f` and `g` is `f` on `X`. -/
@[simp]
theorem glueDesc_glueInl (h : ∀ y ∈ e.source, f (e y) = g y) (x : X) :
    e.glueDesc f g h (e.glueInl x) = f x :=
  DFunLike.congr_fun (glueDesc_comp_sigma h) ⟨⟨true⟩, x⟩

/-- The map glued from `f` and `g` is `g` on `Y`. -/
@[simp]
theorem glueDesc_glueInr (h : ∀ y ∈ e.source, f (e y) = g y) (y : Y) :
    e.glueDesc f g h (e.glueInr y) = g y :=
  DFunLike.congr_fun (glueDesc_comp_sigma h) ⟨⟨false⟩, y⟩

/-- A continuous map out of the gluing along `e` is determined by its values on `X` and `Y`. -/
@[ext]
theorem glued_continuousMap_ext {φ φ' : C(e.glueData.toGlueData.glued, Z)}
    (hl : ∀ x, φ (e.glueInl x) = φ' (e.glueInl x))
    (hr : ∀ y, φ (e.glueInr y) = φ' (e.glueInr y)) : φ = φ' := by
  ext z
  obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := exists_glueInl_eq_or_exists_glueInr_eq e z
  · exact hl x
  · exact hr y

/-- The map glued from `f` and `g` is the only continuous map out of the gluing along `e` which is
`f` on `X` and `g` on `Y`. -/
theorem glueDesc_unique (h : ∀ y ∈ e.source, f (e y) = g y)
    {φ : C(e.glueData.toGlueData.glued, Z)} (hl : ∀ x, φ (e.glueInl x) = f x)
    (hr : ∀ y, φ (e.glueInr y) = g y) : φ = e.glueDesc f g h :=
  glued_continuousMap_ext (fun x ↦ by rw [hl, glueDesc_glueInl])
    fun y ↦ by rw [hr, glueDesc_glueInr]

end glueDesc

/-- The relation between the piece `X` and the piece `Y` of the gluing along `e` is the graph of
`e`, read with its two factors exchanged. -/
private theorem chartRel_true_false :
    e.glueData.chartRel ⟨true⟩ ⟨false⟩ = Prod.swap ⁻¹' e.source.graphOn e :=
  Set.ext fun p ↦ e.glueData.mem_chartRel_iff.trans
    (glueInl_eq_glueInr_iff.trans (Set.mem_graphOn (x := p.swap)).symm)

/-- The relation between the piece `Y` and the piece `X` of the gluing along `e` is the graph of
`e`. -/
private theorem chartRel_false_true :
    e.glueData.chartRel ⟨false⟩ ⟨true⟩ = e.source.graphOn e :=
  Set.ext fun (_ : Y × X) ↦ e.glueData.mem_chartRel_iff.trans
    (glueInr_eq_glueInl_iff.trans Set.mem_graphOn.symm)

/-- **Hausdorff criterion for the gluing along an open partial homeomorphism.** The gluing of `X`
and `Y` along `e` is Hausdorff exactly when `X` and `Y` are Hausdorff and the graph
`{(y, e y) | y ∈ e.source}` of `e` on its source is closed in `Y × X`. -/
theorem t2Space_glueData_iff :
    T2Space e.glueData.toGlueData.glued ↔
      T2Space X ∧ T2Space Y ∧ IsClosed (e.source.graphOn e) := by
  rw [e.glueData.t2Space_iff_isClosed_chartRel]
  refine ⟨fun h ↦ ⟨?_, ?_, chartRel_false_true (e := e) ▸ h ⟨false⟩ ⟨true⟩⟩, fun ⟨hX, hY, hg⟩ ↦ ?_⟩
  · exact t2_iff_isClosed_diagonal.2 (e.glueData.chartRel_self ⟨true⟩ ▸ h ⟨true⟩ ⟨true⟩)
  · exact t2_iff_isClosed_diagonal.2 (e.glueData.chartRel_self ⟨false⟩ ▸ h ⟨false⟩ ⟨false⟩)
  rintro ⟨i⟩ ⟨j⟩
  cases i <;> cases j
  · exact e.glueData.chartRel_self ⟨false⟩ ▸ t2_iff_isClosed_diagonal.1 hY
  · exact chartRel_false_true (e := e) ▸ hg
  · rw [chartRel_true_false]
    exact hg.preimage continuous_swap
  · exact e.glueData.chartRel_self ⟨true⟩ ▸ t2_iff_isClosed_diagonal.1 hX

/-- The gluing of Hausdorff spaces along an open partial homeomorphism with closed graph is
Hausdorff. -/
theorem t2Space_glueData [T2Space X] [T2Space Y]
    (he : IsClosed (e.source.graphOn e)) :
    T2Space e.glueData.toGlueData.glued :=
  t2Space_glueData_iff.2 ⟨‹_›, ‹_›, he⟩

/-- **Hausdorffness from an extension beyond the source.** The gluing of a space `X` with a
Hausdorff space `Y` along `e` is Hausdorff when `e` extends beyond its source as in
`TauCeti.isClosed_graphOn_of_continuousOn`, which shows that the graph of `e` on its source is
closed; then `X` is Hausdorff, since it injects continuously into a Hausdorff space. -/
theorem t2Space_glueData_of_continuousOn [T2Space Y] {W : Type*} [TopologicalSpace W] [T2Space W]
    {j : X → W} (hj : Continuous j) (hj' : Function.Injective j) {c : Y → W} {F : Set Y}
    (hF : IsClosed F) (hc : ContinuousOn c F) (hsF : e.source ⊆ F)
    (hce : ∀ y ∈ e.source, c y = j (e y)) (hcF : ∀ y ∈ F \ e.source, c y ∉ range j) :
    T2Space e.glueData.toGlueData.glued :=
  haveI : T2Space X := .of_injective_continuous hj' hj
  t2Space_glueData (isClosed_graphOn_of_continuousOn hj hj' hF hc hsF hce hcF)

/-! ### Cylindrical ends -/

section CylindricalEnd

variable {S R : Type u} [TopologicalSpace S] [TopologicalSpace R] [LinearOrder R] {a : R}
  {e : OpenPartialHomeomorph (S × R) X}

/-- **The end of a space with a cylindrical end attached.** Let `X` be glued to `S × R` along `e`
with source `S × (-∞, a)`, a collar of a missing boundary `S × {a}`. Then the canonical map of the
cylinder is a bijection from the end `S × [a, ∞)` onto the complement of `X` in the glued space.
The main case is `R = ℝ` and `a = 0`. -/
theorem bijOn_glueInr_Ici (he : e.source = Prod.snd ⁻¹' Iio a) :
    BijOn e.glueInr (Prod.snd ⁻¹' Ici a) (range e.glueInl)ᶜ := by
  rw [← compl_Iio, preimage_compl, ← he]
  exact bijOn_glueInr_compl_source e

end CylindricalEnd

end OpenPartialHomeomorph
