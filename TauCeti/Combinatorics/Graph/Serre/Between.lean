/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Helly
public import Mathlib.Data.List.NodupEquivFin
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Betweenness in Serre graphs

A vertex `x` of a Serre graph lies *between* the vertices `a` and `b` when
`dist a x + dist x b = dist a b`, and a dart `e` is *crossed* from `a` to `b` when its two ends
lie between `a` and `b` and its target is one step farther from `a` than its source. In a tree
these are the vertices and the darts of the geodesic from `a` to `b`: there are `dist a b` crossed
darts, and three vertices have a unique *median*, the vertex lying between any two of them.

The darts of a shortest path are crossed from its start to its end, and in an acyclic graph the
crossed darts are exactly those of the reduced path, which is the shortest path. In a tree the
vertices between two vertices form a convex set, so Helly's theorem for subtrees gives a vertex
between any two of three given vertices; it is unique because a vertex between `a` and `b` is
determined by its distance from `a`.

## Main definitions

* `TauCeti.SerreGraph.IsBetween`: the vertex `x` lies between `a` and `b`.
* `TauCeti.SerreGraph.Crosses`: the dart `e` is crossed from `a` to `b`.

## Main results

* `TauCeti.SerreGraph.IsAcyclic.crosses_iff_mem_darts`: in an acyclic graph, the darts crossed
  from `a` to `b` are the darts of the reduced path from `a` to `b`.
* `TauCeti.SerreGraph.IsAcyclic.natCard_crosses`: in an acyclic graph, `dist a b` darts are
  crossed from `a` to `b`.
* `TauCeti.SerreGraph.IsTree.existsUnique_isBetween`: three vertices of a tree have a unique
  median.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2.
* M. J. Dunwoody, *The accessibility of finitely presented groups*, Invent. Math. 81 (1985),
  Proposition 2.3 (the number of lines of a pattern in a two-simplex).
-/

public section

namespace TauCeti

namespace SerreGraph

variable (Γ : SerreGraph)

/-- The vertex `x` lies between `a` and `b`: the distances from `a` to `x` and from `x` to `b`
add up to the distance from `a` to `b`. -/
def IsBetween (a x b : Γ.V) : Prop :=
  Γ.dist a x + Γ.dist x b = Γ.dist a b

/-- The dart `e` is crossed from `a` to `b`: both ends of `e` lie between `a` and `b`, and its
target is one step farther from `a` than its source. -/
def Crosses (a b : Γ.V) (e : Γ.E) : Prop :=
  Γ.IsBetween a (Γ.src e) b ∧ Γ.IsBetween a (Γ.tgt e) b ∧
    Γ.dist a (Γ.tgt e) = Γ.dist a (Γ.src e) + 1

variable {Γ} {a b c x : Γ.V} {e : Γ.E}

/-- Unfold betweenness. -/
theorem isBetween_iff : Γ.IsBetween a x b ↔ Γ.dist a x + Γ.dist x b = Γ.dist a b := Iff.rfl

/-- Unfold crossing. -/
theorem crosses_iff : Γ.Crosses a b e ↔ Γ.IsBetween a (Γ.src e) b ∧ Γ.IsBetween a (Γ.tgt e) b ∧
    Γ.dist a (Γ.tgt e) = Γ.dist a (Γ.src e) + 1 := Iff.rfl

/-- Betweenness is symmetric in the two ends. -/
theorem isBetween_comm : Γ.IsBetween a x b ↔ Γ.IsBetween b x a := by
  simp [isBetween_iff, dist_comm, add_comm]

/-- A vertex lies between itself and any vertex. -/
@[simp] theorem isBetween_left (a b : Γ.V) : Γ.IsBetween a a b := by simp [isBetween_iff]

/-- A vertex lies between any vertex and itself. -/
@[simp] theorem isBetween_right (a b : Γ.V) : Γ.IsBetween a b b := by simp [isBetween_iff]

/-- Among the vertices joined to `a` by a path, only `a` lies between `a` and itself. -/
theorem isBetween_self_iff (h : Nonempty (Γ.Path a x)) : Γ.IsBetween a x a ↔ x = a := by
  refine ⟨fun hx => ?_, fun hx => hx ▸ isBetween_left a a⟩
  rw [isBetween_iff, dist_self, Nat.add_eq_zero_iff] at hx
  exact ((dist_eq_zero_iff h).mp hx.1).symm

/-- A vertex at which a shortest path splits lies between the endpoints of the path. -/
theorem isBetween_of_length_comp_eq_dist {p : Γ.Path a x} {q : Γ.Path x b}
    (h : (p.comp q).length = Γ.dist a b) : Γ.IsBetween a x b := by
  rw [isBetween_iff, ← length_eq_dist_of_comp_left h, ← length_eq_dist_of_comp_right h, ← h,
    Quiver.Path.length_comp]

/-- The source of a dart crossed from `a` to `b` lies between `a` and `b`. -/
theorem Crosses.isBetween_src (h : Γ.Crosses a b e) : Γ.IsBetween a (Γ.src e) b := h.1

/-- The target of a dart crossed from `a` to `b` lies between `a` and `b`. -/
theorem Crosses.isBetween_tgt (h : Γ.Crosses a b e) : Γ.IsBetween a (Γ.tgt e) b := h.2.1

/-- The target of a crossed dart is one step farther from `a` than its source. -/
theorem Crosses.dist_tgt (h : Γ.Crosses a b e) : Γ.dist a (Γ.tgt e) = Γ.dist a (Γ.src e) + 1 :=
  h.2.2

/-- A dart is crossed from `a` to `b` exactly when its reverse is crossed from `b` to `a`. -/
@[simp] theorem crosses_rev : Γ.Crosses b a (Γ.rev e) ↔ Γ.Crosses a b e := by
  simp only [crosses_iff, isBetween_iff, src_rev, tgt_rev]
  grind [dist_comm]

/-- No dart is crossed from a vertex to itself. -/
@[simp] theorem not_crosses_self (a : Γ.V) (e : Γ.E) : ¬Γ.Crosses a a e := by
  simp only [crosses_iff, isBetween_iff, dist_self]
  lia

/-- A dart and its reverse are not both crossed from `a` to `b`. -/
theorem Crosses.not_crosses_rev (h : Γ.Crosses a b e) : ¬Γ.Crosses a b (Γ.rev e) := by
  simp only [crosses_iff, src_rev, tgt_rev] at h ⊢
  lia

/-- Every dart of a shortest path is crossed from the start to the end of the path. -/
theorem Path.crosses_of_length_eq_dist {p : Γ.Path a b} (hp : p.length = Γ.dist a b)
    (he : e ∈ Path.darts Γ p) : Γ.Crosses a b e := by
  obtain ⟨q, r, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
  have hsrc : (q.comp ((Γ.dart e).toPath.comp r)).length = Γ.dist a b := by
    rwa [← Quiver.Path.comp_assoc, Quiver.Path.comp_toPath_eq_cons]
  refine ⟨isBetween_of_length_comp_eq_dist hsrc, isBetween_of_length_comp_eq_dist hp, ?_⟩
  rw [← length_eq_dist_of_comp_left hp, ← length_eq_dist_of_comp_left hsrc,
    Quiver.Path.length_cons]

private theorem Crosses.dist_pos (h : Γ.Crosses a b e) : 0 < Γ.dist a b := by
  rw [crosses_iff, isBetween_iff, isBetween_iff] at h
  lia

private theorem Crosses.exists_isReduced_comp (h : Γ.Crosses a b e) :
    ∃ (q : Γ.Path a (Γ.src e)) (r : Γ.Path (Γ.tgt e) b),
      q.length = Γ.dist a (Γ.src e) ∧ Path.IsReduced Γ ((q.cons (Γ.dart e)).comp r) := by
  -- A shortest path to the source, the dart, and a shortest path from its target form a
  -- shortest path, hence a reduced one.
  obtain ⟨p⟩ := nonempty_path_of_dist_ne_zero (a := a) (b := Γ.tgt e) (by rw [h.dist_tgt]; lia)
  obtain ⟨s⟩ := nonempty_path_of_dist_ne_zero h.dist_pos.ne'
  obtain ⟨q, hq⟩ := exists_length_eq_dist ⟨p.comp (Γ.dart e).toPath.reverse⟩
  obtain ⟨r, hr⟩ := exists_length_eq_dist ⟨p.reverse.comp s⟩
  refine ⟨q, r, hq, Path.isReduced_of_length_le_dist (le_of_eq ?_)⟩
  have := isBetween_iff.mp h.isBetween_tgt
  have := h.dist_tgt
  simp only [Quiver.Path.length_comp, Quiver.Path.length_cons]
  lia

/-- A vertex `x ≠ b` joined to `b` and lying between `a` and `b` is the source of a dart crossed
from `a` to `b`. -/
theorem exists_crosses_of_isBetween (h : Nonempty (Γ.Path x b)) (hx : Γ.IsBetween a x b)
    (hxb : x ≠ b) : ∃ e : Γ.E, Γ.Crosses a b e ∧ Γ.src e = x := by
  have hpos : Γ.dist x b ≠ 0 := (dist_eq_zero_iff h).not.mpr hxb
  rw [isBetween_iff] at hx
  obtain ⟨r⟩ := nonempty_path_of_dist_ne_zero (a := a) (b := b) (by lia)
  obtain ⟨s⟩ := h
  obtain ⟨p, hp⟩ := exists_length_eq_dist ⟨r.comp s.reverse⟩
  obtain ⟨q, hq⟩ := exists_length_eq_dist ⟨s⟩
  obtain ⟨y, f, q', -, rfl⟩ := q.eq_toPath_comp_of_length_eq_succ (n := q.length - 1) (by lia)
  exact ⟨f.1, Path.crosses_of_length_eq_dist (by rw [Quiver.Path.length_comp, hp, hq, hx])
    (by simp), f.2.1⟩

/-! ### Acyclic graphs -/

/-- In an acyclic graph, the darts crossed from `a` to `b` are the darts of the reduced path
from `a` to `b`. -/
theorem IsAcyclic.crosses_iff_mem_darts (h : Γ.IsAcyclic) {p : Γ.Path a b}
    (hp : Path.IsReduced Γ p) : Γ.Crosses a b e ↔ e ∈ Path.darts Γ p := by
  refine ⟨fun he => ?_, Path.crosses_of_length_eq_dist (h.dist_eq_length hp).symm⟩
  obtain ⟨q, r, -, hqr⟩ := he.exists_isReduced_comp
  rw [h.eq_of_isReduced hp hqr]
  simp

/-- In an acyclic graph, a dart crossed from `a` to `b` is determined by its source. -/
theorem IsAcyclic.eq_of_crosses_of_src_eq (h : Γ.IsAcyclic) {e e' : Γ.E} (he : Γ.Crosses a b e)
    (he' : Γ.Crosses a b e') (hs : Γ.src e = Γ.src e') : e = e' := by
  -- The two reduced paths through `e` and through `e'` coincide, and so do their prefixes.
  obtain ⟨q, r, hq, hqr⟩ := he.exists_isReduced_comp
  obtain ⟨q', r', hq', hqr'⟩ := he'.exists_isReduced_comp
  have := congrArg (Path.darts Γ) (h.eq_of_isReduced hqr hqr')
  simp only [Path.darts_comp, Path.darts_cons, dart_val, List.append_assoc,
    List.singleton_append] at this
  have hlen : (Path.darts Γ q).length = (Path.darts Γ q').length := by
    rw [Path.length_darts, Path.length_darts, hq, hq', hs]
  exact (List.cons.inj (List.append_inj this hlen).2).1

/-- In an acyclic graph, the darts crossed from `a` to `b` are the darts of the geodesic from `a`
to `b`: there are `dist a b` of them. -/
theorem IsAcyclic.natCard_crosses (h : Γ.IsAcyclic) (a b : Γ.V) :
    Nat.card {e : Γ.E // Γ.Crosses a b e} = Γ.dist a b := by
  classical
  rcases Nat.eq_zero_or_pos (Γ.dist a b) with h0 | hpos
  · rw [h0, Nat.card_eq_zero]
    exact .inl ⟨fun e => e.2.dist_pos.ne' h0⟩
  obtain ⟨p⟩ := nonempty_path_of_dist_ne_zero hpos.ne'
  have hp := Path.isReduced_reduce Γ p
  have hlen := h.dist_eq_length hp
  rw [hlen, ← Path.length_darts, ← Nat.card_fin (Path.darts Γ (Path.reduce Γ p)).length]
  exact Nat.card_congr ((Equiv.subtypeEquivRight fun e => h.crosses_iff_mem_darts hp).trans
    ((Path.nodup_darts_of_length_eq_dist hlen.symm).getEquiv _).symm)

/-! ### Trees -/

/-- In a tree, a vertex between `a` and `b` lies between `a` and `c` or between `c` and `b`. -/
theorem IsTree.isBetween_or_isBetween (h : Γ.IsTree) (hx : Γ.IsBetween a x b) (c : Γ.V) :
    Γ.IsBetween a x c ∨ Γ.IsBetween c x b := by
  rcases eq_or_ne x b with rfl | hxb
  · exact .inr (isBetween_right c x)
  obtain ⟨e, he, rfl⟩ := exists_crosses_of_isBetween (h.nonempty_path _ _) hx hxb
  -- The reduced path from `a` to `b` is the reduction of the reduced paths through `c`.
  obtain ⟨p, hp, -⟩ := h.existsUnique_isReduced a c
  obtain ⟨q, hq, -⟩ := h.existsUnique_isReduced c b
  have hr := (Path.darts_reduce_sublist Γ (p.comp q)).subset
    ((h.isAcyclic.crosses_iff_mem_darts (Path.isReduced_reduce Γ _)).mp he)
  rw [Path.darts_comp, List.mem_append] at hr
  exact hr.imp (fun he => ((h.isAcyclic.crosses_iff_mem_darts hp).mpr he).isBetween_src)
    (fun he => ((h.isAcyclic.crosses_iff_mem_darts hq).mpr he).isBetween_src)

private theorem IsTree.isBetween_trans_left (h : Γ.IsTree) {u w : Γ.V} (hu : Γ.IsBetween a u b)
    (hw : Γ.IsBetween a w u) : Γ.IsBetween a w b := by
  have h₁ := dist_triangle (h.nonempty_path a w) (h.nonempty_path w b)
  have h₂ := dist_triangle (h.nonempty_path w u) (h.nonempty_path u b)
  rw [isBetween_iff] at hu hw ⊢
  lia

private theorem IsTree.isConvex_setOf_isBetween (h : Γ.IsTree) (a b : Γ.V) :
    Γ.IsConvex {x | Γ.IsBetween a x b} := by
  refine isConvex_iff.mpr fun u hu v hv p hp e he => ?_
  rcases h.isBetween_or_isBetween ((h.isAcyclic.crosses_iff_mem_darts hp).mpr he).isBetween_src a
    with hw | hw
  · exact h.isBetween_trans_left hu (isBetween_comm.mp hw)
  · exact h.isBetween_trans_left hv hw

private theorem IsTree.eq_of_isBetween_of_dist_eq (h : Γ.IsTree) {y : Γ.V} (hx : Γ.IsBetween a x b)
    (hy : Γ.IsBetween a y b) (hxy : Γ.dist a x = Γ.dist a y) : x = y := by
  -- `x` lies between `a` and `y`, or between `y` and `b`; either way `dist y x = 0`.
  have hyx := dist_eq_zero_iff (h.nonempty_path y x)
  have := Γ.dist_comm x y
  rcases h.isBetween_or_isBetween hx y with h' | h' <;> rw [isBetween_iff] at hx hy h' <;>
    exact (hyx.mp (by lia)).symm

/-- Three vertices of a tree have a unique median: a vertex lying between any two of them. -/
theorem IsTree.existsUnique_isBetween (h : Γ.IsTree) (a b c : Γ.V) :
    ∃! m : Γ.V, Γ.IsBetween a m b ∧ Γ.IsBetween b m c ∧ Γ.IsBetween a m c := by
  -- The three sets of vertices between two of `a`, `b`, `c` are convex and pairwise meet.
  obtain ⟨m, ⟨hab, hbc⟩, hac⟩ := h.inter_inter_nonempty (h.isConvex_setOf_isBetween a b)
    (h.isConvex_setOf_isBetween b c) (h.isConvex_setOf_isBetween a c)
    ⟨b, isBetween_right a b, isBetween_left b c⟩ ⟨a, isBetween_left a b, isBetween_left a c⟩
    ⟨c, isBetween_right b c, isBetween_right a c⟩
  refine ⟨m, ⟨hab, hbc, hac⟩, fun m' ⟨hab', hbc', hac'⟩ =>
    h.eq_of_isBetween_of_dist_eq hab' hab ?_⟩
  -- The distance from `a` to a median is determined by the distances between `a`, `b` and `c`.
  have := Γ.dist_comm b m
  have := Γ.dist_comm b m'
  simp only [Set.mem_ofPred_eq, isBetween_iff] at hab hbc hac hab' hbc' hac'
  lia

end SerreGraph

end TauCeti
