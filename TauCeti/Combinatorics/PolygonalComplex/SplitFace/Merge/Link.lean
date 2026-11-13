/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.SplitFace.Merge.Basic

/-!
# Merging two faces of a polygonal surface model

Merging two faces `g₁ = X d` and `g₂ = d⁻¹ Y` of a polygonal complex along their common side `d`
(`PolygonalComplex.mergeFaces`) does not change the surface. The link of a vertex in the merged
complex is its link in the original complex with the germs `d` and `d⁻¹` smoothed out. At the
source of `d`, the link edges `x⁻¹, d` of the last corner of `g₁` and `d, y` of the second corner
of `g₂`, where `x` is the last side of `X` and `y` the first side of `Y`, become the single link
edge `x⁻¹, y` of the corner of `X Y` where `Y` starts. At the target of `d`, the link edges of the
first corners of `g₂` and `g₁` become the link edge of the first corner of `X Y`. When `X` or `Y`
is empty, `d` is a loop and the three link edges through `d` and `d⁻¹` become one. Every other
corner keeps its two germs. The link therefore stays connected and the remaining germs keep their
degrees, so a circle stays a circle and an interval stays an interval
(`PolygonalComplex.HasSurfaceLink.mergeFaces`). The one-skeleton stays connected as well: the
sides of `X` join the two ends of `d` in the merged complex
(`PolygonalComplex.IsMergeable.nonempty_path_tgt_src`).

A surface model therefore stays a surface model (`SurfaceModel.mergeFaces`), with the same Euler
characteristic, the same orientability and the same boundary darts: the deleted edge is interior.

## Main definitions

* `TauCeti.SurfaceModel.mergeFaces`: the surface model obtained by merging two faces.

## Main results

* `TauCeti.PolygonalComplex.IsMergeable.linkDegree_incoming`: the deleted edge lies on two face
  sides, so it is interior.
* `TauCeti.PolygonalComplex.HasSurfaceLink.mergeFaces`: a surface link stays a surface link.
* `TauCeti.PolygonalComplex.IsMergeable.nonempty_path_tgt_src`: the merged face joins the target
  of the deleted edge to its source.
* `TauCeti.SurfaceModel.eulerChar_mergeFaces`, `TauCeti.SurfaceModel.isOrientable_mergeFaces_iff`:
  the Euler characteristic and orientability are unchanged.
* `TauCeti.SurfaceModel.image_val_boundaryDarts_mergeFaces`: the boundary darts are unchanged.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definition 6.3, operation (P2), and its inverse (P2)⁻¹ before Lemma 6.1.
-/

public section

universe u v w

namespace TauCeti

namespace PolygonalComplex

variable {C : PolygonalComplex.{u, v, w}} {g₁ g₂ : C.Face} (h : C.IsMergeable g₁ g₂)

/-! ### The corners of the merged face at the two ends of `d` -/

omit h in
/-- A side off the edge of `d` is not one of the two occurrences of `d`. -/
private theorem toGeomEdge_outgoing_ne_of_ne {c : C.Corner} (h : C.IsMergeable g₁ g₂)
    (h₁ : c ≠ C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) (h₂ : c ≠ ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩) :
    C.graph.toGeomEdge (C.outgoing c) ≠
      C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) :=
  fun he => (h.eq_or_eq_of_toGeomEdge_eq c he).elim h₁ h₂

/-- The first corner of the merged face `X Y`, at the target of `d`. -/
private def firstCorner : (C.mergeFaces h).Corner :=
  ⟨none, ⟨0, (C.mergeFaces h).sides_pos none⟩⟩

/-- The corner of the merged face `X Y` where `Y` starts, at the source of `d`. It is the first
corner when `X` or `Y` is empty. -/
private def joinCorner : (C.mergeFaces h).Corner :=
  ⟨none, ⟨(C.sides g₁ - 1) % C.mergeFacesSides g₁ g₂ none,
    Nat.mod_lt _ ((C.mergeFaces h).sides_pos none)⟩⟩

private theorem joinCorner_eq_firstCorner (h' : C.sides g₁ = 1 ∨ C.sides g₂ = 1) :
    joinCorner h = firstCorner h := by
  rw [joinCorner, firstCorner]
  refine Sigma.ext rfl (heq_of_eq (Fin.ext ?_))
  have hN : C.mergeFacesSides g₁ g₂ none = C.sides g₁ + C.sides g₂ - 2 := rfl
  dsimp only
  rcases h' with h' | h'
  · rw [h', Nat.sub_self, Nat.zero_mod]
  · rw [hN, h', show C.sides g₁ + 1 - 2 = C.sides g₁ - 1 by omega, Nat.mod_self]

private theorem coe_outgoing_firstCorner_of_one_lt (h₁ : 1 < C.sides g₁) :
    ((C.mergeFaces h).outgoing (firstCorner h)).1 = C.outgoing ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩ := by
  rw [coe_outgoing_mergeFaces, firstCorner,
    mergeFacesCornerOrigin_none_of_lt (by dsimp only; omega)]

private theorem coe_outgoing_firstCorner_of_eq_one (h₁ : C.sides g₁ = 1) :
    ((C.mergeFaces h).outgoing (firstCorner h)).1 =
      C.outgoing (C.nextCorner ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩) := by
  have := h.two_lt_sides_add_sides
  rw [coe_outgoing_mergeFaces, firstCorner,
    mergeFacesCornerOrigin_none_of_not_lt (by dsimp only; omega), nextCorner_def]
  refine congrArg C.outgoing (Sigma.ext rfl (heq_of_eq (Fin.ext ?_)))
  have h0 := Fin.coe_finRotate_eq_ite (⟨0, C.sides_pos g₂⟩ : Fin (C.sides g₂))
  dsimp only at h0 ⊢
  split_ifs at h0 <;> omega

private theorem coe_incoming_firstCorner_of_one_lt (h₂ : 1 < C.sides g₂) :
    ((C.mergeFaces h).incoming (firstCorner h)).1 = C.incoming ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩ := by
  have := C.sides_pos g₁
  have hN : C.mergeFacesSides g₁ g₂ none = C.sides g₁ + C.sides g₂ - 2 := rfl
  rw [firstCorner, (C.mergeFaces h).incoming_mk_zero none, ← outgoing_def _ ⟨_, _⟩,
    coe_outgoing_mergeFaces, mergeFacesCornerOrigin_none_of_not_lt (by dsimp only; omega),
    C.incoming_mk_zero g₂, ← outgoing_def _ ⟨_, _⟩]
  exact congrArg C.outgoing (Sigma.ext rfl (heq_of_eq (Fin.ext (by dsimp only; omega))))

private theorem coe_incoming_firstCorner_of_eq_one (h₂ : C.sides g₂ = 1) :
    ((C.mergeFaces h).incoming (firstCorner h)).1 =
      C.incoming (C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := by
  have := h.two_lt_sides_add_sides
  have hN : C.mergeFacesSides g₁ g₂ none = C.sides g₁ + C.sides g₂ - 2 := rfl
  rw [firstCorner, (C.mergeFaces h).incoming_mk_zero none, ← outgoing_def _ ⟨_, _⟩,
    coe_outgoing_mergeFaces, mergeFacesCornerOrigin_none_of_lt (by dsimp only; omega),
    prevCorner_mk_zero,
    C.incoming_mk_of_ne_zero (i := ⟨C.sides g₁ - 2, by omega⟩) (by dsimp only; omega)
      (by dsimp only; omega)]
  exact congrArg C.outgoing (Sigma.ext rfl (heq_of_eq (Fin.ext (by dsimp only; omega))))

private theorem joinCorner_of_one_lt (h₂ : 1 < C.sides g₂) :
    joinCorner h = ⟨none, ⟨C.sides g₁ - 1, sides_sub_one_lt_mergeFacesSides h₂⟩⟩ :=
  Sigma.ext rfl (heq_of_eq (Fin.ext (Nat.mod_eq_of_lt (sides_sub_one_lt_mergeFacesSides h₂))))

private theorem coe_outgoing_joinCorner_of_one_lt (h₂ : 1 < C.sides g₂) :
    ((C.mergeFaces h).outgoing (joinCorner h)).1 =
      C.outgoing (C.nextCorner ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩) := by
  have := C.sides_pos g₁
  rw [joinCorner_of_one_lt h h₂, coe_outgoing_mergeFaces,
    mergeFacesCornerOrigin_none_of_not_lt (by dsimp only; omega), nextCorner_def]
  refine congrArg C.outgoing (Sigma.ext rfl (heq_of_eq (Fin.ext ?_)))
  have h0 := Fin.coe_finRotate_eq_ite (⟨0, C.sides_pos g₂⟩ : Fin (C.sides g₂))
  dsimp only at h0 ⊢
  split_ifs at h0 <;> omega

private theorem coe_incoming_joinCorner_of_one_lt (h₁ : 1 < C.sides g₁) :
    ((C.mergeFaces h).incoming (joinCorner h)).1 =
      C.incoming (C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := by
  rcases Nat.lt_or_ge 1 (C.sides g₂) with h₂ | h₂
  · rw [joinCorner_of_one_lt h h₂, (C.mergeFaces h).incoming_mk_of_ne_zero
        (i := ⟨C.sides g₁ - 2, by simp only [mergeFacesSides]; omega⟩) (by dsimp only; omega)
        (by dsimp only; omega),
      coe_outgoing_mergeFaces, mergeFacesCornerOrigin_none_of_lt (by dsimp only; omega),
      prevCorner_mk_zero, C.incoming_mk_of_ne_zero (i := ⟨C.sides g₁ - 2, by omega⟩)
        (by dsimp only; omega) (by dsimp only; omega)]
  · rw [joinCorner_eq_firstCorner h (.inr (by have := C.sides_pos g₂; omega))]
    exact coe_incoming_firstCorner_of_eq_one h (by have := C.sides_pos g₂; omega)

private theorem cornerVertex_firstCorner : (C.mergeFaces h).cornerVertex (firstCorner h) =
    C.graph.tgt (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := by
  rw [← src_outgoing, outgoing_def]
  exact src_mergeFacesSide_zero h

private theorem cornerVertex_joinCorner : (C.mergeFaces h).cornerVertex (joinCorner h) =
    C.graph.src (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := by
  rcases Nat.lt_or_ge 1 (C.sides g₂) with h₂ | h₂
  · rw [joinCorner_of_one_lt h h₂, ← src_outgoing, outgoing_def]
    exact src_mergeFacesSide_sides_sub_one h h₂
  · have h₂ : C.sides g₂ = 1 := by have := C.sides_pos g₂; omega
    rw [joinCorner_eq_firstCorner h (.inr h₂), cornerVertex_firstCorner]
    -- `g₂ = d⁻¹` is a monogon, so `d` is a loop
    have hl := C.tgt_side_eq_src_side_of_sides_eq_one h₂ ⟨0, C.sides_pos g₂⟩
    rw [← outgoing_def _ ⟨_, _⟩, h.outgoing_eq, SerreGraph.tgt_rev, SerreGraph.src_rev] at hl
    exact hl.symm

/-! ### Germs -/

/-- The germ of the merged complex standing for a germ of `C`: a germ off the edge of `d` stands
for itself, `d` stands for the outgoing side of the corner of the merged face at its source, and
`d⁻¹` for the outgoing side of the corner of the merged face at its target. -/
private noncomputable def mergeGerm (e : C.graph.E) : (C.mergeFaces h).graph.E := by
  classical
  exact if he : C.graph.toGeomEdge e = C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)
    then if e = C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩ then (C.mergeFaces h).outgoing (joinCorner h)
      else (C.mergeFaces h).outgoing (firstCorner h)
    else ⟨e, he⟩

private theorem mergeGerm_of_ne {e : C.graph.E}
    (he : C.graph.toGeomEdge e ≠ C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)) :
    mergeGerm h e = ⟨e, he⟩ := by
  rw [mergeGerm, dite_eq_right he]

private theorem mergeGerm_incoming : mergeGerm h (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) =
    (C.mergeFaces h).outgoing (joinCorner h) := by
  rw [mergeGerm, dite_eq_left rfl, ite_eq_left rfl]

private theorem mergeGerm_rev_incoming :
    mergeGerm h (C.graph.rev (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)) =
      (C.mergeFaces h).outgoing (firstCorner h) := by
  rw [mergeGerm, dite_eq_left (SerreGraph.toGeomEdge_rev _ _), ite_eq_right (C.graph.rev_ne _)]

private theorem src_mergeGerm (e : C.graph.E) : C.graph.src (mergeGerm h e).1 = C.graph.src e := by
  by_cases he : C.graph.toGeomEdge e = C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)
  · rcases C.graph.toGeomEdge_eq_toGeomEdge_iff.1 he.symm with rfl | rfl
    · rw [mergeGerm_incoming]
      exact ((C.mergeFaces h).src_outgoing _).trans (cornerVertex_joinCorner h)
    · rw [mergeGerm_rev_incoming, SerreGraph.src_rev]
      exact ((C.mergeFaces h).src_outgoing _).trans (cornerVertex_firstCorner h)
  · rw [mergeGerm_of_ne h he]

/-! ### Vertex links -/

omit h in
/-- The edge of `d` lies on exactly the two face sides `d` of `g₁` and `d⁻¹` of `g₂`, so `d` has
degree two in its link. -/
theorem IsMergeable.linkDegree_incoming (h : C.IsMergeable g₁ g₂) :
    C.linkDegree (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) = 2 := by
  have hd₁ := (C.incoming_eq_outgoing_prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩).symm
  have hne := C.graph.rev_ne (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)
  have h₁ : Nat.card {c : C.Corner // C.outgoing c = C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩} = 1 :=
    Nat.card_eq_one_iff_exists.2 ⟨⟨_, hd₁⟩, fun ⟨c, hc⟩ => Subtype.ext <| by
      rcases h.eq_or_eq_of_toGeomEdge_eq c (by rw [hc]) with rfl | rfl
      · rfl
      · exact absurd (h.outgoing_eq.symm.trans hc) hne⟩
  have h₂ : Nat.card {c : C.Corner //
      C.outgoing c = C.graph.rev (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)} = 1 :=
    Nat.card_eq_one_iff_exists.2 ⟨⟨_, h.outgoing_eq⟩, fun ⟨c, hc⟩ => Subtype.ext <| by
      rcases h.eq_or_eq_of_toGeomEdge_eq c (by rw [hc, SerreGraph.toGeomEdge_rev]) with rfl | rfl
      · exact absurd (hd₁.symm.trans hc) hne.symm
      · rfl⟩
  have := Nat.finite_of_card_ne_zero (h₁.symm ▸ one_ne_zero)
  have := Nat.finite_of_card_ne_zero (h₂.symm ▸ one_ne_zero)
  rw [linkDegree_eq_natCard_sum, Nat.card_sum, h₁, h₂]


omit h in
/-- Two germs of a link with the same underlying dart are joined by the empty path. -/
private theorem nonempty_vertexLink_path_of_val_eq {D : PolygonalComplex.{u, v, w}} {x : D.graph.V}
    {a b : (D.vertexLink x).V} (hab : a.1 = b.1) : Nonempty ((D.vertexLink x).Path a b) := by
  obtain rfl := Subtype.ext hab
  exact ⟨.nil⟩

/-- The link edge `x⁻¹, d` of the last corner of `g₁` becomes the link edge `x⁻¹, y` of the corner
of the merged face where `Y` starts; it collapses when `X` is empty. -/
private theorem nonempty_vertexLink_path_mergeGerm_prevCorner {v : C.graph.V}
    {a b : ((C.mergeFaces h).vertexLink v).V}
    (ha : a.1 = mergeGerm h (C.outgoing (C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)))
    (hb : b.1 = mergeGerm h (C.graph.rev (C.incoming (C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)))) :
    Nonempty (((C.mergeFaces h).vertexLink v).Path a b) := by
  rw [← incoming_eq_outgoing_prevCorner, mergeGerm_incoming] at ha
  rcases Nat.lt_or_ge 1 (C.sides g₁) with h₁ | h₁
  · have hne : C.graph.toGeomEdge
        (C.graph.rev (C.incoming (C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩))) ≠
        C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := by
      rw [SerreGraph.toGeomEdge_rev, incoming_eq_outgoing_prevCorner]
      refine toGeomEdge_outgoing_ne_of_ne h (fun he => ?_) fun he => h.ne ?_
      · have := C.prevCorner_eq_self_iff.1 he
        simp only [prevCorner_fst] at this
        omega
      · simpa using congrArg Sigma.fst he
    rw [mergeGerm_of_ne h hne] at hb
    exact (C.mergeFaces h).nonempty_vertexLink_path_of_corner (joinCorner h) ha (hb.trans
      (Subtype.ext (congrArg C.graph.rev (coe_incoming_joinCorner_of_one_lt h h₁).symm)))
  · have h₁ : C.sides g₁ = 1 := by have := C.sides_pos g₁; omega
    rw [C.prevCorner_eq_self_iff.2 h₁, mergeGerm_rev_incoming] at hb
    rw [joinCorner_eq_firstCorner h (.inl h₁)] at ha
    exact nonempty_vertexLink_path_of_val_eq (ha.trans hb.symm)

/-- The link edge `y'⁻¹, d⁻¹` of the first corner of `g₂` becomes the link edge `y'⁻¹, x₁` of the
first corner of the merged face; it collapses when `Y` is empty. -/
private theorem nonempty_vertexLink_path_mergeGerm_mk_zero {v : C.graph.V}
    {a b : ((C.mergeFaces h).vertexLink v).V}
    (ha : a.1 = mergeGerm h (C.outgoing ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩))
    (hb : b.1 = mergeGerm h (C.graph.rev (C.incoming ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩))) :
    Nonempty (((C.mergeFaces h).vertexLink v).Path a b) := by
  rw [h.outgoing_eq, mergeGerm_rev_incoming] at ha
  rcases Nat.lt_or_ge 1 (C.sides g₂) with h₂ | h₂
  · have hne : C.graph.toGeomEdge (C.graph.rev (C.incoming ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩)) ≠
        C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := by
      rw [SerreGraph.toGeomEdge_rev, incoming_eq_outgoing_prevCorner]
      refine toGeomEdge_outgoing_ne_of_ne h (fun he => h.ne ?_) fun he => ?_
      · simpa using (congrArg Sigma.fst he).symm
      · exact (by omega : C.sides g₂ ≠ 1) (C.prevCorner_eq_self_iff.1 he)
    rw [mergeGerm_of_ne h hne] at hb
    exact (C.mergeFaces h).nonempty_vertexLink_path_of_corner (firstCorner h) ha (hb.trans
      (Subtype.ext (congrArg C.graph.rev (coe_incoming_firstCorner_of_one_lt h h₂).symm)))
  · have h₂ : C.sides g₂ = 1 := by have := C.sides_pos g₂; omega
    rw [incoming_eq_outgoing_prevCorner, C.prevCorner_eq_self_iff.2 h₂, h.outgoing_eq,
      SerreGraph.rev_rev, mergeGerm_incoming, joinCorner_eq_firstCorner h (.inr h₂)] at hb
    exact nonempty_vertexLink_path_of_val_eq (ha.trans hb.symm)

/-- The link edges `d⁻¹, x₁` and `d, y` of the corners following `d` and `d⁻¹` collapse. -/
private theorem nonempty_vertexLink_path_mergeGerm_of_prevCorner {c : C.Corner} {v : C.graph.V}
    {a b : ((C.mergeFaces h).vertexLink v).V} (h₁ : c ≠ C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)
    (h₂ : c ≠ ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩)
    (hc : C.prevCorner c = C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩ ∨
      C.prevCorner c = ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩)
    (ha : a.1 = mergeGerm h (C.outgoing c)) (hb : b.1 = mergeGerm h (C.graph.rev (C.incoming c))) :
    Nonempty (((C.mergeFaces h).vertexLink v).Path a b) := by
  rw [mergeGerm_of_ne h (toGeomEdge_outgoing_ne_of_ne h h₁ h₂)] at ha
  refine nonempty_vertexLink_path_of_val_eq ((ha.trans ?_).trans hb.symm)
  rcases hc with hc | hc
  · obtain rfl : c = ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩ := (C.nextCorner_prevCorner c).symm.trans
      ((congrArg C.nextCorner hc).trans (C.nextCorner_prevCorner _))
    have h₁' : 1 < C.sides g₁ := by
      by_contra hn
      have := C.sides_pos g₁
      exact h₁ (C.prevCorner_eq_self_iff.2 (by dsimp only; omega)).symm
    rw [mergeGerm_rev_incoming]
    exact Subtype.ext (coe_outgoing_firstCorner_of_one_lt h h₁').symm
  · obtain rfl : c = C.nextCorner ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩ :=
      (C.nextCorner_prevCorner c).symm.trans (congrArg C.nextCorner hc)
    have h₂' : 1 < C.sides g₂ := by
      by_contra hn
      have := C.sides_pos g₂
      exact h₂ (C.nextCorner_eq_self_iff.2 (by dsimp only; omega))
    rw [incoming_nextCorner, h.outgoing_eq, SerreGraph.rev_rev, mergeGerm_incoming]
    exact Subtype.ext (coe_outgoing_joinCorner_of_one_lt h h₂').symm

/-- A corner of `C` touching neither `d` nor `d⁻¹` is a corner of the merged complex with the same
two germs. -/
private theorem nonempty_vertexLink_path_mergeGerm_of_ne {c : C.Corner} {v : C.graph.V}
    {a b : ((C.mergeFaces h).vertexLink v).V} (h₁ : c ≠ C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)
    (h₂ : c ≠ ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩)
    (h₁' : C.prevCorner c ≠ C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩)
    (h₂' : C.prevCorner c ≠ ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩)
    (ha : a.1 = mergeGerm h (C.outgoing c)) (hb : b.1 = mergeGerm h (C.graph.rev (C.incoming c))) :
    Nonempty (((C.mergeFaces h).vertexLink v).Path a b) := by
  obtain ⟨x, rfl⟩ := exists_mergeFacesCornerOrigin_eq h₁ h₂
  have hi : C.graph.toGeomEdge (C.graph.rev (C.incoming (C.mergeFacesCornerOrigin g₁ g₂ x))) ≠
      C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := by
    rw [SerreGraph.toGeomEdge_rev, incoming_eq_outgoing_prevCorner]
    exact toGeomEdge_outgoing_ne_of_ne h h₁' h₂'
  rw [mergeGerm_of_ne h (toGeomEdge_outgoing_ne_of_ne h h₁ h₂)] at ha
  rw [mergeGerm_of_ne h hi] at hb
  refine (C.mergeFaces h).nonempty_vertexLink_path_of_corner x
    (ha.trans (Subtype.ext (coe_outgoing_mergeFaces h x).symm)) (hb.trans (Subtype.ext ?_))
  exact congrArg C.graph.rev (coe_incoming_mergeFaces h x (fun he => h₁' (by rw [he]))
    fun he => h₂' (by rw [he, prevCorner_nextCorner])).symm

/-- In the link of the merged complex, the germs standing for the two germs of a corner of `C` are
joined by a path: the corner itself if it does not touch `d`, a corner of the merged face where
`X` and `Y` meet, or no edge at all. -/
private theorem nonempty_vertexLink_path_mergeGerm (c : C.Corner) {v : C.graph.V}
    {a b : ((C.mergeFaces h).vertexLink v).V} (ha : a.1 = mergeGerm h (C.outgoing c))
    (hb : b.1 = mergeGerm h (C.graph.rev (C.incoming c))) :
    Nonempty (((C.mergeFaces h).vertexLink v).Path a b) := by
  by_cases h₁ : c = C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩
  · subst h₁
    exact nonempty_vertexLink_path_mergeGerm_prevCorner h ha hb
  by_cases h₂ : c = ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩
  · subst h₂
    exact nonempty_vertexLink_path_mergeGerm_mk_zero h ha hb
  by_cases h₁' : C.prevCorner c = C.prevCorner ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩
  · exact nonempty_vertexLink_path_mergeGerm_of_prevCorner h h₁ h₂ (.inl h₁') ha hb
  by_cases h₂' : C.prevCorner c = ⟨g₂, ⟨0, C.sides_pos g₂⟩⟩
  · exact nonempty_vertexLink_path_mergeGerm_of_prevCorner h h₁ h₂ (.inr h₂') ha hb
  exact nonempty_vertexLink_path_mergeGerm_of_ne h h₁ h₂ h₁' h₂' ha hb

/-- A path in the link of a vertex of `C` gives a path between the corresponding germs in the link
of the merged complex. -/
private theorem nonempty_vertexLink_path_mergeFaces_of_path {v : C.graph.V}
    {a b : (C.vertexLink v).V} (P : (C.vertexLink v).Path a b) :
    Nonempty (((C.mergeFaces h).vertexLink v).Path
      ⟨mergeGerm h a.1, (src_mergeGerm h a.1).trans a.2⟩
      ⟨mergeGerm h b.1, (src_mergeGerm h b.1).trans b.2⟩) := by
  induction P with
  | nil => exact ⟨.nil⟩
  | cons _ e ih =>
    rename_i b' c' _
    obtain ⟨Q⟩ := ih
    obtain ⟨⟨c, _ | _⟩, hs, ht⟩ := e
    · obtain ⟨R⟩ := nonempty_vertexLink_path_mergeGerm h c.1
        (a := ⟨mergeGerm h c'.1, (src_mergeGerm h c'.1).trans c'.2⟩)
        (b := ⟨mergeGerm h b'.1, (src_mergeGerm h b'.1).trans b'.2⟩)
        (congrArg (mergeGerm h)
          ((congrArg Subtype.val ht).symm.trans (C.vertexLink_src_true c)))
        (congrArg (mergeGerm h)
          ((congrArg Subtype.val hs).symm.trans (C.vertexLink_src_false c)))
      exact ⟨Q.comp R.reverse⟩
    · obtain ⟨R⟩ := nonempty_vertexLink_path_mergeGerm h c.1
        (a := ⟨mergeGerm h b'.1, (src_mergeGerm h b'.1).trans b'.2⟩)
        (b := ⟨mergeGerm h c'.1, (src_mergeGerm h c'.1).trans c'.2⟩)
        (congrArg (mergeGerm h)
          ((congrArg Subtype.val hs).symm.trans (C.vertexLink_src_true c)))
        (congrArg (mergeGerm h)
          ((congrArg Subtype.val ht).symm.trans (C.vertexLink_src_false c)))
      exact ⟨Q.comp R⟩

/-- A vertex with finitely many corners in `C` has finitely many corners in the merged complex:
they come from corners of `C` at the same vertex. -/
instance {v : C.graph.V} [Finite (C.vertexLink v).E] :
    Finite ((C.mergeFaces h).vertexLink v).E := by
  have : Finite {c : C.Corner // C.cornerVertex c = v} :=
    .of_injective (β := (C.vertexLink v).E) (fun c => (c, true)) fun _ _ h => congrArg Prod.fst h
  have : Finite {c : (C.mergeFaces h).Corner // (C.mergeFaces h).cornerVertex c = v} :=
    .of_injective (β := {c : C.Corner // C.cornerVertex c = v})
      (fun c => ⟨C.mergeFacesCornerOrigin g₁ g₂ c.1,
        (cornerVertex_mergeFaces h c.1).symm.trans c.2⟩)
      fun c c' he => Subtype.ext (mergeFacesCornerOrigin_injective h.ne (congrArg Subtype.val he))
  exact inferInstanceAs (Finite ({c : (C.mergeFaces h).Corner // _} × Bool))

/-- Merging two faces keeps the surface links: a circle link stays a circle and an interval link
stays an interval, since the merge only smooths out the germs `d` and `d⁻¹` of the link and the
remaining germs keep their degrees. -/
theorem HasSurfaceLink.mergeFaces {v : C.graph.V} (hv : C.HasSurfaceLink v) :
    (C.mergeFaces h).HasSurfaceLink v := by
  obtain ⟨hfin, hconn, hdeg⟩ := (C.hasSurfaceLink_iff v).1 hv
  obtain ⟨⟨a⟩, hpre⟩ := (C.vertexLink v).connected_iff.1 hconn
  have hφ (b : ((C.mergeFaces h).vertexLink v).V) :
      (⟨mergeGerm h b.1.1, (src_mergeGerm h b.1.1).trans b.2⟩ :
        ((C.mergeFaces h).vertexLink v).V) = b :=
    Subtype.ext (mergeGerm_of_ne h b.1.2)
  have hconn' : ((C.mergeFaces h).vertexLink v).Connected := by
    refine ((C.mergeFaces h).vertexLink v).connected_iff.2
      ⟨⟨⟨mergeGerm h a.1, (src_mergeGerm h a.1).trans a.2⟩⟩,
        ((C.mergeFaces h).vertexLink v).preconnected_iff.2 fun b b' => ?_⟩
    obtain ⟨P⟩ := (C.vertexLink v).preconnected_iff.1 hpre ⟨b.1.1, b.2⟩ ⟨b'.1.1, b'.2⟩
    obtain ⟨Q⟩ := nonempty_vertexLink_path_mergeFaces_of_path h P
    rw [hφ b, hφ b'] at Q
    exact ⟨Q⟩
  have hd (e : C.graph.E) (he : C.linkDegree e = 1) : C.graph.toGeomEdge e ≠
      C.graph.toGeomEdge (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := fun hed => by
    rcases C.graph.toGeomEdge_eq_toGeomEdge_iff.1 hed.symm with rfl | rfl <;>
      simp [h.linkDegree_incoming] at he
  refine ((C.mergeFaces h).hasSurfaceLink_iff v).2 ⟨inferInstance, hconn', ?_⟩
  rcases hdeg with hcirc | ⟨e₁, e₂, hne, h₁, h₂, hd₁, hd₂, hrest⟩
  · exact .inl fun e he => (linkDegree_mergeFaces h e).trans (hcirc e.1 he)
  · refine .inr ⟨⟨e₁, hd e₁ hd₁⟩, ⟨e₂, hd e₂ hd₂⟩, fun he => hne (congrArg Subtype.val he), h₁,
      h₂, (linkDegree_mergeFaces h _).trans hd₁, (linkDegree_mergeFaces h _).trans hd₂,
      fun e he hne₁ hne₂ => (linkDegree_mergeFaces h e).trans
        (hrest e.1 he (fun h' => hne₁ (Subtype.ext h')) fun h' => hne₂ (Subtype.ext h'))⟩

/-! ### The one-skeleton -/

/-- In the merged complex the target of `d` is joined to its source, along the sides of `X`. -/
theorem IsMergeable.nonempty_path_tgt_src :
    Nonempty ((C.mergeFaces h).graph.Path (C.graph.tgt (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩))
      (C.graph.src (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩))) := by
  obtain ⟨P⟩ := (C.mergeFaces h).nonempty_path_cornerVertex none (firstCorner h).2 (joinCorner h).2
  have e₁ : (C.mergeFaces h).cornerVertex ⟨none, (firstCorner h).2⟩ =
      C.graph.tgt (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := cornerVertex_firstCorner h
  have e₂ : (C.mergeFaces h).cornerVertex ⟨none, (joinCorner h).2⟩ =
      C.graph.src (C.incoming ⟨g₁, ⟨0, C.sides_pos g₁⟩⟩) := cornerVertex_joinCorner h
  rw [e₁, e₂] at P
  exact ⟨P⟩

end PolygonalComplex

namespace PolygonalComplex.IsMergeable

variable {S : SurfaceModel.{u, v, w}} {g₁ g₂ : S.Face}

/-- The common side of two mergeable faces of a surface model is interior: it lies on the two face
sides `d` and `d⁻¹`. -/
theorem incoming_notMem_boundaryDarts (h : S.IsMergeable g₁ g₂) :
    S.incoming ⟨g₁, ⟨0, S.sides_pos g₁⟩⟩ ∉ S.boundaryDarts := by
  rw [← SurfaceModel.linkDegree_eq_one_iff_mem_boundaryDarts, h.linkDegree_incoming]
  decide

end PolygonalComplex.IsMergeable

namespace SurfaceModel

variable (S : SurfaceModel.{u, v, w}) {g₁ g₂ : S.Face} (h : S.IsMergeable g₁ g₂)

/-- The surface model obtained by merging the faces `g₁ = X d` and `g₂ = d⁻¹ Y` of a surface model
along the last side `d` of `g₁`. It is reducible, so that its underlying complex is seen to be
`S.toPolygonalComplex.mergeFaces h`. -/
abbrev mergeFaces : SurfaceModel.{u, v, w} where
  toPolygonalComplex := S.toPolygonalComplex.mergeFaces h
  connected := S.connected.deleteEdge h.nonempty_path_tgt_src
  hasSurfaceLink v := (S.hasSurfaceLink v).mergeFaces h

/-- Merging two faces of a surface model does not change its Euler characteristic. -/
@[simp] theorem eulerChar_mergeFaces : (S.mergeFaces h).eulerChar = S.eulerChar :=
  haveI : Finite S.graph.GeomEdge := Finite.of_surjective _ S.graph.toGeomEdge_surjective
  S.toPolygonalComplex.eulerChar_mergeFaces h

/-- Merging two faces of a surface model does not change its orientability. -/
theorem isOrientable_mergeFaces_iff : (S.mergeFaces h).IsOrientable ↔ S.IsOrientable :=
  S.toPolygonalComplex.isOrientable_mergeFaces_iff h

/-- A remaining dart is a boundary dart of the merged model exactly when it is one of the original
model. -/
@[simp] theorem mem_boundaryDarts_mergeFaces_iff {e : (S.mergeFaces h).graph.E} :
    e ∈ (S.mergeFaces h).boundaryDarts ↔ e.1 ∈ S.boundaryDarts := by
  rw [mem_boundaryDarts_iff, mem_boundaryDarts_iff]
  exact Eq.congr_left (congrArg₂ (· + ·) (PolygonalComplex.sideCount_mergeFaces h _)
    (PolygonalComplex.sideCount_mergeFaces h e))

/-- Merging two faces of a surface model does not change its boundary darts. -/
theorem image_val_boundaryDarts_mergeFaces :
    Subtype.val '' (S.mergeFaces h).boundaryDarts = S.boundaryDarts := by
  ext e
  refine ⟨?_, fun he => ⟨⟨e, fun hed => ?_⟩, (S.mem_boundaryDarts_mergeFaces_iff h).2 he, rfl⟩⟩
  · rintro ⟨e', he', rfl⟩
    exact (S.mem_boundaryDarts_mergeFaces_iff h).1 he'
  · rcases S.graph.toGeomEdge_eq_toGeomEdge_iff.1 hed.symm with rfl | rfl
    · exact h.incoming_notMem_boundaryDarts he
    · exact h.incoming_notMem_boundaryDarts (rev_mem_boundaryDarts_iff.1 he)

end SurfaceModel

end TauCeti
