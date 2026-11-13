/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PolygonalComplex.Examples
public import TauCeti.Combinatorics.PolygonalComplex.SplitFace.Basic
import Mathlib.Data.Set.Finite.Range

/-!
# Splitting a face of a polygonal surface model

Splitting a face of a polygonal complex along a new side (`PolygonalComplex.splitFace`) does not
change the surface. The link of a vertex in the split complex is its link in the original complex
with the link edges of the two cut corners subdivided at the new germs: the corner `p` of the
split face, with germs `aₚ₋₁⁻¹` and `aₚ`, becomes the two corners `aₚ₋₁⁻¹, d` and `d, aₚ`, and the
corner `0`, with germs `aₙ₋₁⁻¹` and `a₀`, becomes the two corners `aₙ₋₁⁻¹, d⁻¹` and `d⁻¹, a₀`. For
`p = 0` the single cut corner becomes the three corners `aₙ₋₁⁻¹, d⁻¹` and `d⁻¹, d` and `d, a₀`.
Every other corner is unchanged. The link therefore stays connected, the old germs keep their
degrees and the new germs have degree two, so a circle stays a circle and an interval stays an
interval (`PolygonalComplex.HasSurfaceLink.splitFace`).

A surface model therefore stays a surface model (`SurfaceModel.splitFace`), with the same Euler
characteristic, the same orientability and the same boundary darts: the new side is interior.
For the disc, the split model has the two darts of the original edge as its boundary darts.

## Main definitions

* `TauCeti.SurfaceModel.splitFace`: the surface model obtained by splitting a face.

## Main results

* `TauCeti.PolygonalComplex.HasSurfaceLink.splitFace`: a surface link stays a surface link.
* `TauCeti.SurfaceModel.eulerChar_splitFace`, `TauCeti.SurfaceModel.isOrientable_splitFace_iff`:
  the Euler characteristic and orientability are unchanged.
* `TauCeti.SurfaceModel.boundaryDarts_splitFace`: the boundary darts are unchanged.
* `TauCeti.SurfaceModel.boundaryDarts_disc_splitFace`: a split disc keeps its boundary edge.

## References

* J. Gallier, D. Xu, *A Guide to the Classification Theorem for Compact Surfaces*, Springer, 2013,
  Chapter 6, Definition 6.3, operation (P2).
-/

public section

universe u v w

namespace TauCeti

namespace PolygonalComplex

variable (C : PolygonalComplex.{u, v, w}) (f : C.Face) (p : Fin (C.sides f))

/-! ### The corners of the two new faces -/

private theorem incoming_splitFace_false_zero :
    (C.splitFace f p).incoming ⟨.inr false, ⟨0, Nat.succ_pos _⟩⟩ =
      .inl (C.incoming ⟨f, ⟨0, C.sides_pos f⟩⟩) := by
  have hp := p.2
  rw [(C.splitFace f p).incoming_mk_of_eq_zero (f := .inr false)
      (i := (⟨C.sides f - p, Nat.lt_succ_self _⟩ : Fin (C.sides f - p + 1))) rfl
      (Nat.add_sub_cancel _ _).symm,
    outgoing_splitFace, splitFaceCornerOrigin_inr_false_of_ne_zero (by dsimp only; omega),
    Sum.map_inl, C.incoming_mk_of_eq_zero (i := ⟨p + (C.sides f - p) - 1, by omega⟩) rfl
      (by dsimp only; omega)]

private theorem outgoing_splitFace_false_one :
    (C.splitFace f p).outgoing ⟨.inr false, ⟨1, Nat.succ_lt_succ (Nat.sub_pos_of_lt p.2)⟩⟩ =
      .inl (C.outgoing ⟨f, p⟩) := by
  rw [outgoing_splitFace, splitFaceCornerOrigin_inr_false_of_ne_zero (by simp), Sum.map_inl]
  rfl

private theorem incoming_splitFace_false_one :
    (C.splitFace f p).incoming ⟨.inr false, ⟨1, Nat.succ_lt_succ (Nat.sub_pos_of_lt p.2)⟩⟩ =
      .inr false := by
  rw [(C.splitFace f p).incoming_mk_of_ne_zero (f := .inr false)
    (i := (⟨0, Nat.succ_pos _⟩ : Fin (C.sides f - p + 1))) one_ne_zero rfl]
  exact outgoing_splitFace_inr_false_zero C f p

private theorem incoming_splitFace_true_last_of_ne_zero (hp : (p : ℕ) ≠ 0) :
    (C.splitFace f p).incoming ⟨.inr true, ⟨p, Nat.lt_succ_self _⟩⟩ = .inl (C.incoming ⟨f, p⟩) := by
  have hp' := p.2
  rw [(C.splitFace f p).incoming_mk_of_ne_zero (f := .inr true)
      (i := (⟨p - 1, by omega⟩ : Fin (p + 1))) hp rfl,
    outgoing_splitFace, splitFaceCornerOrigin_inr_true_of_lt (by dsimp only; omega),
    Sum.map_inl, C.incoming_mk_of_ne_zero (i := ⟨p - 1, by omega⟩) hp rfl]

private theorem outgoing_splitFace_true_zero (hp : (p : ℕ) ≠ 0) :
    (C.splitFace f p).outgoing ⟨.inr true, ⟨0, Nat.succ_pos _⟩⟩ =
      .inl (C.outgoing ⟨f, ⟨0, C.sides_pos f⟩⟩) := by
  rw [outgoing_splitFace, splitFaceCornerOrigin_inr_true_of_lt (Nat.pos_of_ne_zero hp),
    Sum.map_inl]

private theorem incoming_splitFace_true_zero :
    (C.splitFace f p).incoming ⟨.inr true, ⟨0, Nat.succ_pos _⟩⟩ = .inr true := by
  rw [(C.splitFace f p).incoming_mk_of_eq_zero (f := .inr true)
    (i := (⟨p, Nat.lt_succ_self _⟩ : Fin (p + 1))) rfl (Nat.add_sub_cancel _ _).symm]
  exact outgoing_splitFace_inr_true_last C f p

/-- A corner of the split face other than the two corners cut by the new edge is a corner of one
of the two new faces, with the same two sides. -/
private theorem exists_corner_splitFace_self (k : Fin (C.sides f)) (hk0 : (k : ℕ) ≠ 0)
    (hkp : (k : ℕ) ≠ p) :
    ∃ c : (C.splitFace f p).Corner, (C.splitFace f p).outgoing c = .inl (C.outgoing ⟨f, k⟩) ∧
      (C.splitFace f p).incoming c = .inl (C.incoming ⟨f, k⟩) := by
  have hk := k.2
  rw [C.incoming_mk_of_ne_zero (i := ⟨k - 1, by omega⟩) hk0 rfl]
  by_cases hlt : (k : ℕ) < p
  · refine ⟨⟨.inr true, ⟨k, Nat.lt_succ_of_lt hlt⟩⟩, ?_, ?_⟩
    · rw [outgoing_splitFace, splitFaceCornerOrigin_inr_true_of_lt hlt, Sum.map_inl]
    · rw [(C.splitFace f p).incoming_mk_of_ne_zero (f := .inr true)
          (i := (⟨k - 1, by omega⟩ : Fin (p + 1))) hk0 rfl,
        outgoing_splitFace, splitFaceCornerOrigin_inr_true_of_lt (by dsimp only; omega),
        Sum.map_inl]
  · refine ⟨⟨.inr false, (⟨k - p + 1, by omega⟩ : Fin (C.sides f - p + 1))⟩, ?_, ?_⟩
    · rw [outgoing_splitFace, splitFaceCornerOrigin_inr_false_of_ne_zero (Nat.succ_ne_zero _),
        Sum.map_inl]
      exact congrArg (fun j => (Sum.inl (C.outgoing ⟨f, j⟩) : C.graph.E ⊕ Bool))
        (Fin.ext (by dsimp only; omega))
    · rw [(C.splitFace f p).incoming_mk_of_ne_zero (f := .inr false)
          (i := (⟨k - p, by omega⟩ : Fin (C.sides f - p + 1))) (Nat.succ_ne_zero _) rfl,
        outgoing_splitFace,
        splitFaceCornerOrigin_inr_false_of_ne_zero (by dsimp only; omega), Sum.map_inl]
      exact congrArg (fun j => (Sum.inl (C.outgoing ⟨f, j⟩) : C.graph.E ⊕ Bool))
        (Fin.ext (by dsimp only; omega))

/-- A corner of `C` other than the two corners cut by the new edge is a corner of
`C.splitFace f p` with the same two sides. -/
private theorem exists_corner_splitFace (g : C.Face) (k : Fin (C.sides g))
    (h0 : g = f → (k : ℕ) ≠ 0) (hp : g = f → (k : ℕ) ≠ p) :
    ∃ c : (C.splitFace f p).Corner, (C.splitFace f p).outgoing c = .inl (C.outgoing ⟨g, k⟩) ∧
      (C.splitFace f p).incoming c = .inl (C.incoming ⟨g, k⟩) := by
  by_cases hg : g = f
  · subst hg
    exact exists_corner_splitFace_self C g p k (h0 rfl) (hp rfl)
  · refine ⟨⟨.inl ⟨g, hg⟩, k⟩, ?_, ?_⟩
    · rw [outgoing_splitFace, splitFaceCornerOrigin_inl, Sum.map_inl]
    · have h := C.outgoing_splitFace f p ⟨.inl ⟨g, hg⟩, (finRotate (C.sides g)).symm k⟩
      rw [splitFaceCornerOrigin_inl, Sum.map_inl, outgoing_def, outgoing_def] at h
      rw [incoming_def, incoming_def]
      exact h

/-! ### Vertex links -/

variable {C f p}

/-- In the link of `C.splitFace f p`, the two germs of the corner `0` of the split face are joined
through the new germs. -/
private theorem nonempty_vertexLink_path_splitFace_zero {v : C.graph.V}
    {a b : ((C.splitFace f p).vertexLink v).V}
    (ha : a.1 = .inl (C.outgoing ⟨f, ⟨0, C.sides_pos f⟩⟩))
    (hb : b.1 = .inl (C.graph.rev (C.incoming ⟨f, ⟨0, C.sides_pos f⟩⟩))) :
    Nonempty (((C.splitFace f p).vertexLink v).Path a b) := by
  have hv : C.graph.src (C.side f ⟨0, C.sides_pos f⟩) = v :=
    (congrArg (C.splitFace f p).graph.src
      (ha.trans (congrArg Sum.inl (C.outgoing_def _)))).symm.trans a.2
  let m : ((C.splitFace f p).vertexLink v).V := ⟨.inr false, hv⟩
  obtain ⟨Q⟩ := (C.splitFace f p).nonempty_vertexLink_path_of_corner
    ⟨.inr false, ⟨0, Nat.succ_pos _⟩⟩ (a := m) (b := b)
    (outgoing_splitFace_inr_false_zero C f p).symm
    (hb.trans (congrArg (C.splitFace f p).graph.rev (incoming_splitFace_false_zero C f p).symm))
  by_cases hp : (p : ℕ) = 0
  · obtain rfl : p = ⟨0, C.sides_pos f⟩ := Fin.ext hp
    let m' : ((C.splitFace f ⟨0, C.sides_pos f⟩).vertexLink v).V := ⟨.inr true, hv⟩
    obtain ⟨P⟩ := (C.splitFace f ⟨0, C.sides_pos f⟩).nonempty_vertexLink_path_of_corner
      ⟨.inr false, ⟨1, Nat.succ_lt_succ (Nat.sub_pos_of_lt (C.sides_pos f))⟩⟩ (a := a) (b := m')
      (ha.trans (outgoing_splitFace_false_one C f _).symm)
      (congrArg (C.splitFace f ⟨0, C.sides_pos f⟩).graph.rev
        (incoming_splitFace_false_one C f _).symm)
    obtain ⟨R⟩ := (C.splitFace f ⟨0, C.sides_pos f⟩).nonempty_vertexLink_path_of_corner
      ⟨.inr true, ⟨0, Nat.succ_pos _⟩⟩ (a := m') (b := m)
      (outgoing_splitFace_inr_true_last C f _).symm
      (congrArg (C.splitFace f ⟨0, C.sides_pos f⟩).graph.rev
        (incoming_splitFace_true_zero C f _).symm)
    exact ⟨(P.comp R).comp Q⟩
  · obtain ⟨P⟩ := (C.splitFace f p).nonempty_vertexLink_path_of_corner
      ⟨.inr true, ⟨0, Nat.succ_pos _⟩⟩ (a := a) (b := m)
      (ha.trans (outgoing_splitFace_true_zero C f p hp).symm)
      (congrArg (C.splitFace f p).graph.rev (incoming_splitFace_true_zero C f p).symm)
    exact ⟨P.comp Q⟩

/-- In the link of `C.splitFace f p`, the two germs of the corner `p` of the split face are joined
through the new germ, when `p` is not the corner `0`. -/
private theorem nonempty_vertexLink_path_splitFace_cut (hp : (p : ℕ) ≠ 0) {v : C.graph.V}
    {a b : ((C.splitFace f p).vertexLink v).V} (ha : a.1 = .inl (C.outgoing ⟨f, p⟩))
    (hb : b.1 = .inl (C.graph.rev (C.incoming ⟨f, p⟩))) :
    Nonempty (((C.splitFace f p).vertexLink v).Path a b) := by
  have hv : C.graph.src (C.side f p) = v :=
    (congrArg (C.splitFace f p).graph.src
      (ha.trans (congrArg Sum.inl (C.outgoing_def _)))).symm.trans a.2
  let m : ((C.splitFace f p).vertexLink v).V := ⟨.inr true, hv⟩
  obtain ⟨P⟩ := (C.splitFace f p).nonempty_vertexLink_path_of_corner
    ⟨.inr false, ⟨1, Nat.succ_lt_succ (Nat.sub_pos_of_lt p.2)⟩⟩ (a := a) (b := m)
    (ha.trans (outgoing_splitFace_false_one C f p).symm)
    (congrArg (C.splitFace f p).graph.rev (incoming_splitFace_false_one C f p).symm)
  obtain ⟨Q⟩ := (C.splitFace f p).nonempty_vertexLink_path_of_corner
    ⟨.inr true, ⟨p, Nat.lt_succ_self _⟩⟩ (a := m) (b := b)
    (outgoing_splitFace_inr_true_last C f p).symm
    (hb.trans (congrArg (C.splitFace f p).graph.rev
      (incoming_splitFace_true_last_of_ne_zero C f p hp).symm))
  exact ⟨P.comp Q⟩

/-- In the link of `C.splitFace f p`, the two germs of a corner of `C` are joined by a path: the
corner itself if it is not cut, and otherwise the path through the new germs subdividing it. -/
private theorem nonempty_vertexLink_path_splitFace {v : C.graph.V} (c₀ : C.Corner)
    {a b : ((C.splitFace f p).vertexLink v).V} (ha : a.1 = .inl (C.outgoing c₀))
    (hb : b.1 = .inl (C.graph.rev (C.incoming c₀))) :
    Nonempty (((C.splitFace f p).vertexLink v).Path a b) := by
  obtain ⟨g, k⟩ := c₀
  by_cases h0 : g = f ∧ (k : ℕ) = 0
  · obtain ⟨rfl, hk⟩ := h0
    obtain rfl : k = ⟨0, C.sides_pos g⟩ := Fin.ext hk
    exact nonempty_vertexLink_path_splitFace_zero ha hb
  by_cases hp : g = f ∧ (k : ℕ) = p
  · obtain ⟨rfl, hk⟩ := hp
    obtain rfl : k = p := Fin.ext hk
    exact nonempty_vertexLink_path_splitFace_cut (fun h => h0 ⟨rfl, h⟩) ha hb
  obtain ⟨c, hout, hin⟩ := exists_corner_splitFace C f p g k (fun hg hk => h0 ⟨hg, hk⟩)
    fun hg hk => hp ⟨hg, hk⟩
  exact (C.splitFace f p).nonempty_vertexLink_path_of_corner c (ha.trans hout.symm)
    (hb.trans (congrArg (C.splitFace f p).graph.rev hin.symm))

/-- A path in the link of a vertex of `C` gives a path between the same germs in the link of
`C.splitFace f p`. -/
private theorem nonempty_vertexLink_path_splitFace_of_path {v : C.graph.V}
    {a b : (C.vertexLink v).V} (P : (C.vertexLink v).Path a b) :
    Nonempty (((C.splitFace f p).vertexLink v).Path ⟨.inl a.1, a.2⟩ ⟨.inl b.1, b.2⟩) := by
  induction P with
  | nil => exact ⟨.nil⟩
  | cons _ e ih =>
    rename_i b' c' _
    obtain ⟨Q⟩ := ih
    obtain ⟨⟨c, _ | _⟩, hs, ht⟩ := e
    · obtain ⟨R⟩ := nonempty_vertexLink_path_splitFace (f := f) (p := p) c.1
        (a := ⟨.inl c'.1, c'.2⟩) (b := ⟨.inl b'.1, b'.2⟩)
        (congrArg Sum.inl ((congrArg Subtype.val ht).symm.trans (C.vertexLink_src_true c)))
        (congrArg Sum.inl ((congrArg Subtype.val hs).symm.trans (C.vertexLink_src_false c)))
      exact ⟨Q.comp R.reverse⟩
    · obtain ⟨R⟩ := nonempty_vertexLink_path_splitFace (f := f) (p := p) c.1
        (a := ⟨.inl b'.1, b'.2⟩) (b := ⟨.inl c'.1, c'.2⟩)
        (congrArg Sum.inl ((congrArg Subtype.val hs).symm.trans (C.vertexLink_src_true c)))
        (congrArg Sum.inl ((congrArg Subtype.val ht).symm.trans (C.vertexLink_src_false c)))
      exact ⟨Q.comp R⟩

/-- If the link of a vertex of `C` is preconnected, every germ of `C.splitFace f p` at that vertex
is joined to any old germ: the new germs are joined to the germs of the corners they subdivide. -/
private theorem nonempty_vertexLink_path_splitFace_of_preconnected {v : C.graph.V}
    (h : (C.vertexLink v).Preconnected) (a : (C.vertexLink v).V)
    (b : ((C.splitFace f p).vertexLink v).V) :
    Nonempty (((C.splitFace f p).vertexLink v).Path ⟨.inl a.1, a.2⟩ b) := by
  obtain ⟨e | _ | _, he⟩ := b
  · obtain ⟨P⟩ := (C.vertexLink v).preconnected_iff.1 h a ⟨e, he⟩
    exact nonempty_vertexLink_path_splitFace_of_path P
  · have hv : C.graph.src (C.graph.rev (C.incoming ⟨f, ⟨0, C.sides_pos f⟩⟩)) = v := by
      rw [SerreGraph.src_rev, tgt_incoming, ← src_outgoing, outgoing_def]
      exact he
    obtain ⟨P⟩ := (C.vertexLink v).preconnected_iff.1 h a ⟨_, hv⟩
    obtain ⟨Q⟩ := nonempty_vertexLink_path_splitFace_of_path (f := f) (p := p) P
    obtain ⟨R⟩ := (C.splitFace f p).nonempty_vertexLink_path_of_corner
      ⟨.inr false, ⟨0, Nat.succ_pos _⟩⟩ (a := ⟨.inr false, he⟩) (b := ⟨.inl _, hv⟩)
      (outgoing_splitFace_inr_false_zero C f p).symm
      (congrArg (C.splitFace f p).graph.rev (incoming_splitFace_false_zero C f p).symm)
    exact ⟨Q.comp R.reverse⟩
  · have hv : C.graph.src (C.outgoing ⟨f, p⟩) = v := by
      rw [outgoing_def]
      exact he
    obtain ⟨P⟩ := (C.vertexLink v).preconnected_iff.1 h a ⟨_, hv⟩
    obtain ⟨Q⟩ := nonempty_vertexLink_path_splitFace_of_path (f := f) (p := p) P
    obtain ⟨R⟩ := (C.splitFace f p).nonempty_vertexLink_path_of_corner
      ⟨.inr false, ⟨1, Nat.succ_lt_succ (Nat.sub_pos_of_lt p.2)⟩⟩
      (a := ⟨.inl _, hv⟩) (b := ⟨.inr true, he⟩) (outgoing_splitFace_false_one C f p).symm
      (congrArg (C.splitFace f p).graph.rev (incoming_splitFace_false_one C f p).symm)
    exact ⟨Q.comp R⟩

variable (f p) in
/-- A vertex with finitely many corners in `C` has finitely many corners in `C.splitFace f p`:
they come from its corners in `C` and the two occurrences of the new edge. -/
instance {v : C.graph.V} [Finite (C.vertexLink v).E] :
    Finite ((C.splitFace f p).vertexLink v).E := by
  have : Finite {c : C.Corner // C.cornerVertex c = v} :=
    .of_injective (β := (C.vertexLink v).E) (fun c => (c, true)) fun _ _ h => congrArg Prod.fst h
  have hs : (C.splitFaceCornerOrigin f p '' {c | (C.splitFace f p).cornerVertex c = v}).Finite := by
    refine (((Set.toFinite {c : C.Corner | C.cornerVertex c = v}).image Sum.inl).union
      (Set.finite_range Sum.inr)).subset ?_
    rintro _ ⟨c, rfl, rfl⟩
    rcases hc : C.splitFaceCornerOrigin f p c with c₀ | b
    · refine .inl ⟨c₀, ?_, rfl⟩
      rw [Set.mem_ofPred_eq, ← src_outgoing, ← src_outgoing, outgoing_splitFace, hc, Sum.map_inl]
      rfl
    · exact .inr ⟨b, rfl⟩
  have := (hs.of_finite_image (C.splitFaceCornerOrigin_injective f p).injOn).to_subtype
  exact inferInstanceAs (Finite ({c : (C.splitFace f p).Corner // _} × Bool))

variable (f p) in
/-- Splitting a face keeps the surface links: the link of a vertex in `C.splitFace f p` is its
link in `C` with the edges of the cut corners subdivided at the new germs, which have degree
two. -/
theorem HasSurfaceLink.splitFace {v : C.graph.V} (h : C.HasSurfaceLink v) :
    (C.splitFace f p).HasSurfaceLink v := by
  obtain ⟨hfin, hconn, hdeg⟩ := (C.hasSurfaceLink_iff v).1 h
  obtain ⟨⟨a⟩, hpre⟩ := (C.vertexLink v).connected_iff.1 hconn
  refine ((C.splitFace f p).hasSurfaceLink_iff v).2 ⟨inferInstance,
    ((C.splitFace f p).vertexLink v).connected_iff.2 ⟨⟨⟨.inl a.1, a.2⟩⟩,
      SerreGraph.preconnected_of_forall_nonempty_path _ ⟨.inl a.1, a.2⟩
        (nonempty_vertexLink_path_splitFace_of_preconnected hpre a)⟩, ?_⟩
  rcases hdeg with hcirc | ⟨e₁, e₂, hne, h₁, h₂, hd₁, hd₂, hrest⟩
  · refine .inl ?_
    rintro (e | b) he
    · exact (C.linkDegree_splitFace_inl f p e).trans (hcirc e he)
    · exact C.linkDegree_splitFace_inr f p b
  · refine .inr ⟨.inl e₁, .inl e₂, fun h => hne (Sum.inl_injective h), h₁, h₂,
      (C.linkDegree_splitFace_inl f p e₁).trans hd₁,
      (C.linkDegree_splitFace_inl f p e₂).trans hd₂, ?_⟩
    rintro (e | b) he hne₁ hne₂
    · exact (C.linkDegree_splitFace_inl f p e).trans
        (hrest e he (fun h => hne₁ (congrArg Sum.inl h)) fun h => hne₂ (congrArg Sum.inl h))
    · exact C.linkDegree_splitFace_inr f p b

end PolygonalComplex

namespace SurfaceModel

variable (S : SurfaceModel.{u, v, w}) (f : S.Face) (p : Fin (S.sides f))

/-- The surface model obtained by splitting the face `f` of a surface model at its corner `p`,
along a new edge from the corner `p` to the corner `0`. It is reducible, so that its underlying
complex is seen to be `S.toPolygonalComplex.splitFace f p`. -/
abbrev splitFace : SurfaceModel.{u, v, w} where
  toPolygonalComplex := S.toPolygonalComplex.splitFace f p
  connected := S.connected.addEdge _ _
  hasSurfaceLink v := (S.hasSurfaceLink v).splitFace f p

/-- Splitting a face of a surface model does not change its Euler characteristic. -/
theorem eulerChar_splitFace : (S.splitFace f p).eulerChar = S.eulerChar :=
  S.toPolygonalComplex.eulerChar_splitFace f p

/-- Splitting a face of a surface model does not change its orientability. -/
theorem isOrientable_splitFace_iff : (S.splitFace f p).IsOrientable ↔ S.IsOrientable :=
  S.toPolygonalComplex.isOrientable_splitFace_iff f p

/-- The new edge of a split face is interior: its two darts are not boundary darts. -/
@[simp] theorem inr_notMem_boundaryDarts_splitFace (b : Bool) :
    .inr b ∉ (S.splitFace f p).boundaryDarts := by
  rw [notMem_boundaryDarts_iff]
  exact congrArg₂ (· + ·) (S.sideCount_splitFace_inr f p !b) (S.sideCount_splitFace_inr f p b)

/-- An old dart is a boundary dart of the split model exactly when it is one of the original
model. -/
@[simp] theorem inl_mem_boundaryDarts_splitFace_iff {e : S.graph.E} :
    .inl e ∈ (S.splitFace f p).boundaryDarts ↔ e ∈ S.boundaryDarts := by
  rw [mem_boundaryDarts_iff, mem_boundaryDarts_iff]
  exact Eq.congr_left (congrArg₂ (· + ·) (S.sideCount_splitFace_inl f p (S.graph.rev e))
    (S.sideCount_splitFace_inl f p e))

/-- Splitting a face of a surface model does not change its boundary darts. -/
theorem boundaryDarts_splitFace : (S.splitFace f p).boundaryDarts = Sum.inl '' S.boundaryDarts := by
  ext (e | b)
  · rw [inl_mem_boundaryDarts_splitFace_iff, Set.mem_image]
    exact ⟨fun h => ⟨e, h, rfl⟩, fun ⟨e', h, he⟩ => Sum.inl_injective he ▸ h⟩
  · exact iff_of_false (S.inr_notMem_boundaryDarts_splitFace f p b) (by simp)

/-! ### The split disc -/

/-- Splitting the face of the disc keeps its boundary: the boundary darts of the split model are
the two darts of the original edge, and the new side is interior. -/
theorem boundaryDarts_disc_splitFace (f : disc.Face) (p : Fin (disc.sides f)) :
    (disc.splitFace f p).boundaryDarts = Set.range Sum.inl := by
  rw [boundaryDarts_splitFace, boundaryDarts_disc, Set.image_univ]

/-- A split disc has Euler characteristic `1`. -/
theorem eulerChar_disc_splitFace (f : disc.Face) (p : Fin (disc.sides f)) :
    (disc.splitFace f p).eulerChar = 1 :=
  (disc.eulerChar_splitFace f p).trans eulerChar_disc

end SurfaceModel

end TauCeti
