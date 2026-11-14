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

A vertex `x` of a Serre graph lies *between* the vertices `a` and `b` when it is joined to `a` and
to `b` by paths and `dist a x + dist x b = dist a b`, that is, when `x` is a vertex of a shortest
path from `a` to `b`. A dart `e` is *crossed* from `a` to `b` when its two ends lie between `a`
and `b` and its target is one step farther from `a` than its source, that is, when `e` is a dart
of a shortest path from `a` to `b`. Since betweenness asks for paths, `a`, `x` and `b` then lie in
one component: the distance `0` between vertices of different components plays no role, and a
dart can only be crossed between vertices at positive distance.

These notions describe maps to trees, as in Dunwoody's patterns. If a simplicial complex is
mapped to a tree so that each edge goes injectively onto the geodesic between the images of its
ends, or to a point when they coincide, the preimage of the midpoints of the edges of the tree
meets an edge whose ends go to `a` and `b` once for each dart crossed from `a` to `b`, so
`dist a b` times. Three vertices `a`, `b`, `c` of a
tree have a unique *median* `m`, the vertex lying between any two of them, and the darts crossed
from `a` to `b` are those crossed from `a` to `m` or from `m` to `b`: on a triangle whose corners
go to `a`, `b` and `c`, each dart crossed from `a` to `m` is crossed along both sides at `a`.

In an acyclic graph the darts crossed from `a` to `b` and the vertices between them are those of
a reduced path from `a` to `b`, when there is one, since it is a shortest path. The vertices
between two vertices then form a convex set, so in a tree Helly's theorem for subtrees gives a
vertex between any two of three given vertices. It is unique because a vertex between `a` and `b`
is determined by its distance from `a`, and for a median `m` the three equations of betweenness
force `2 dist a m = dist a b + dist a c - dist b c`.

## Main definitions

* `TauCeti.SerreGraph.IsBetween`: the vertex `x` lies between `a` and `b`.
* `TauCeti.SerreGraph.Crosses`: the dart `e` is crossed from `a` to `b`.

## Main results

* `TauCeti.SerreGraph.isBetween_iff_exists_length_eq_dist`,
  `TauCeti.SerreGraph.crosses_iff_exists_length_eq_dist`: the vertices between `a` and `b` and
  the darts crossed from `a` to `b` are those of the shortest paths from `a` to `b`.
* `TauCeti.SerreGraph.IsAcyclic.crosses_iff_mem_darts`: in an acyclic graph, the darts crossed
  from `a` to `b` are the darts of a reduced path `p` from `a` to `b`.
* `TauCeti.SerreGraph.IsAcyclic.natCard_crosses`: in an acyclic graph, `dist a b` darts are
  crossed from `a` to `b`.
* `TauCeti.SerreGraph.IsAcyclic.crosses_iff_crosses_or_crosses`: in an acyclic graph, the darts
  crossed from `a` to `b` are those crossed from `a` to `m` or from `m` to `b`, for `m` between
  `a` and `b`.
* `TauCeti.SerreGraph.IsTree.existsUnique_isBetween`: three vertices of a tree have a unique
  median.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2.
* M. J. Dunwoody, *The accessibility of finitely presented groups*, Invent. Math. 81 (1985),
  Proposition 2.3 (the number of lines of a pattern in a two-simplex).
* V. Guirardel, G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.4 (arcs
  and alignment in trees) and the proof of Proposition 2.24 (maps sending each edge to a point
  or injectively onto a segment).
-/

public section

namespace TauCeti

namespace SerreGraph

variable (Γ : SerreGraph)

/-- The vertex `x` lies between `a` and `b`: it is joined to `a` and to `b` by paths, and the
distances from `a` to `x` and from `x` to `b` add up to the distance from `a` to `b`. -/
def IsBetween (a x b : Γ.V) : Prop :=
  Nonempty (Γ.Path a x) ∧ Nonempty (Γ.Path x b) ∧ Γ.dist a x + Γ.dist x b = Γ.dist a b

/-- The dart `e` is crossed from `a` to `b`: both ends of `e` lie between `a` and `b`, and its
target is one step farther from `a` than its source. -/
def Crosses (a b : Γ.V) (e : Γ.E) : Prop :=
  Γ.IsBetween a (Γ.src e) b ∧ Γ.IsBetween a (Γ.tgt e) b ∧
    Γ.dist a (Γ.tgt e) = Γ.dist a (Γ.src e) + 1

variable {Γ} {a b c m x : Γ.V} {e : Γ.E}

/-- Unfold betweenness. -/
theorem isBetween_iff : Γ.IsBetween a x b ↔
    Nonempty (Γ.Path a x) ∧ Nonempty (Γ.Path x b) ∧ Γ.dist a x + Γ.dist x b = Γ.dist a b :=
  Iff.rfl

/-- Unfold crossing. -/
theorem crosses_iff : Γ.Crosses a b e ↔ Γ.IsBetween a (Γ.src e) b ∧ Γ.IsBetween a (Γ.tgt e) b ∧
    Γ.dist a (Γ.tgt e) = Γ.dist a (Γ.src e) + 1 := Iff.rfl

/-- A vertex between `a` and `b` is joined to `a` by a path. -/
theorem IsBetween.nonempty_path_left (h : Γ.IsBetween a x b) : Nonempty (Γ.Path a x) := h.1

/-- A vertex between `a` and `b` is joined to `b` by a path. -/
theorem IsBetween.nonempty_path_right (h : Γ.IsBetween a x b) : Nonempty (Γ.Path x b) := h.2.1

/-- Two vertices with a vertex between them are joined by a path. -/
theorem IsBetween.nonempty_path (h : Γ.IsBetween a x b) : Nonempty (Γ.Path a b) :=
  let ⟨⟨p⟩, ⟨q⟩, _⟩ := h
  ⟨p.comp q⟩

/-- The distances from `a` and from `b` to a vertex between them add up to their distance. -/
theorem IsBetween.dist_add_dist (h : Γ.IsBetween a x b) :
    Γ.dist a x + Γ.dist x b = Γ.dist a b := h.2.2

/-- Betweenness is symmetric in the two ends. -/
theorem IsBetween.symm (h : Γ.IsBetween a x b) : Γ.IsBetween b x a := by
  refine ⟨h.2.1.map Quiver.Path.reverse, h.1.map Quiver.Path.reverse, ?_⟩
  rw [dist_comm b x, dist_comm x a, dist_comm b a, add_comm]
  exact h.dist_add_dist

/-- Betweenness is symmetric in the two ends. -/
theorem isBetween_comm : Γ.IsBetween a x b ↔ Γ.IsBetween b x a := ⟨.symm, .symm⟩

/-- A vertex lies between itself and any vertex joined to it. -/
theorem isBetween_left (h : Nonempty (Γ.Path a b)) : Γ.IsBetween a a b := ⟨⟨.nil⟩, h, by simp⟩

/-- A vertex lies between any vertex joined to it and itself. -/
theorem isBetween_right (h : Nonempty (Γ.Path a b)) : Γ.IsBetween a b b := ⟨h, ⟨.nil⟩, by simp⟩

/-- A vertex lies between itself and itself. -/
theorem isBetween_self (a : Γ.V) : Γ.IsBetween a a a := isBetween_left ⟨.nil⟩

/-- Only `a` lies between `a` and itself. -/
@[simp] theorem isBetween_self_iff : Γ.IsBetween a x a ↔ x = a := by
  refine ⟨fun hx => ?_, fun hx => hx ▸ isBetween_self a⟩
  have := hx.dist_add_dist
  rw [dist_self, Nat.add_eq_zero_iff] at this
  exact ((dist_eq_zero_iff hx.nonempty_path_left).mp this.1).symm

/-- If `m` lies between `a` and `b`, then every vertex between `m` and `b` lies between `a` and
`b`. -/
theorem IsBetween.trans_right (h₁ : Γ.IsBetween a m b) (h₂ : Γ.IsBetween m x b) :
    Γ.IsBetween a x b := by
  obtain ⟨⟨p⟩, -, h₁⟩ := h₁
  obtain ⟨⟨q⟩, hxb, h₂⟩ := h₂
  have := dist_triangle ⟨p⟩ ⟨q⟩
  have := dist_triangle ⟨p.comp q⟩ hxb
  exact ⟨⟨p.comp q⟩, hxb, by lia⟩

/-- If `m` lies between `a` and `b`, then every vertex between `a` and `m` lies between `a` and
`b`. -/
theorem IsBetween.trans_left (h₁ : Γ.IsBetween a m b) (h₂ : Γ.IsBetween a x m) :
    Γ.IsBetween a x b :=
  (h₁.symm.trans_right h₂.symm).symm

/-- A vertex at which a shortest path splits lies between the endpoints of the path. -/
theorem isBetween_of_length_comp_eq_dist {p : Γ.Path a x} {q : Γ.Path x b}
    (h : (p.comp q).length = Γ.dist a b) : Γ.IsBetween a x b := by
  refine ⟨⟨p⟩, ⟨q⟩, ?_⟩
  rw [← length_eq_dist_of_comp_left h, ← length_eq_dist_of_comp_right h, ← h,
    Quiver.Path.length_comp]

/-- Every vertex of a shortest path lies between the start and the end of the path. -/
theorem Path.isBetween_of_length_eq_dist {p : Γ.Path a b} (hp : p.length = Γ.dist a b)
    (hx : x ∈ p.vertices) : Γ.IsBetween a x b := by
  obtain ⟨q, r, rfl⟩ := p.exists_eq_comp_of_mem_vertices hx
  exact isBetween_of_length_comp_eq_dist hp

/-- A vertex lies between `a` and `b` exactly when it is a vertex of a shortest path from `a` to
`b`. -/
theorem isBetween_iff_exists_length_eq_dist :
    Γ.IsBetween a x b ↔ ∃ p : Γ.Path a b, p.length = Γ.dist a b ∧ x ∈ p.vertices := by
  refine ⟨fun hx => ?_, fun ⟨p, hp, hx⟩ => Path.isBetween_of_length_eq_dist hp hx⟩
  obtain ⟨p, hp⟩ := exists_length_eq_dist hx.nonempty_path_left
  obtain ⟨q, hq⟩ := exists_length_eq_dist hx.nonempty_path_right
  refine ⟨p.comp q, by rw [Quiver.Path.length_comp, hp, hq, hx.dist_add_dist], ?_⟩
  simp [Quiver.Path.start_mem_vertices]

/-- The source of a dart crossed from `a` to `b` lies between `a` and `b`. -/
theorem Crosses.isBetween_src (h : Γ.Crosses a b e) : Γ.IsBetween a (Γ.src e) b := h.1

/-- The target of a dart crossed from `a` to `b` lies between `a` and `b`. -/
theorem Crosses.isBetween_tgt (h : Γ.Crosses a b e) : Γ.IsBetween a (Γ.tgt e) b := h.2.1

/-- The target of a crossed dart is one step farther from `a` than its source. -/
theorem Crosses.dist_tgt (h : Γ.Crosses a b e) : Γ.dist a (Γ.tgt e) = Γ.dist a (Γ.src e) + 1 :=
  h.2.2

/-- If a dart is crossed from `a` to `b`, then `a` and `b` are at positive distance. -/
theorem Crosses.dist_pos (h : Γ.Crosses a b e) : 0 < Γ.dist a b := by
  have := h.isBetween_tgt.dist_add_dist
  have := h.dist_tgt
  lia

/-- A dart is crossed from `a` to `b` exactly when its reverse is crossed from `b` to `a`. -/
@[simp] theorem crosses_rev : Γ.Crosses b a (Γ.rev e) ↔ Γ.Crosses a b e := by
  simp only [crosses_iff, src_rev, tgt_rev, isBetween_comm (a := b), isBetween_iff]
  grind [dist_comm]

/-- No dart is crossed from a vertex to itself. -/
@[simp] theorem not_crosses_self (a : Γ.V) (e : Γ.E) : ¬Γ.Crosses a a e :=
  fun h => h.dist_pos.ne' (dist_self a)

/-- A dart and its reverse are not both crossed from `a` to `b`. -/
theorem Crosses.not_crosses_rev (h : Γ.Crosses a b e) : ¬Γ.Crosses a b (Γ.rev e) := fun h' => by
  have := h.dist_tgt
  have := h'.dist_tgt
  rw [src_rev, tgt_rev] at this
  lia

/-- A dart crossed from `a` to `m` is not crossed from `m` to any vertex: it leads towards `m`. -/
theorem Crosses.not_crosses_right (h : Γ.Crosses a m e) : ¬Γ.Crosses m b e := fun h' => by
  simp only [crosses_iff, isBetween_iff] at h h'
  grind [dist_comm]

/-- If `m` lies between `a` and `b`, then a dart crossed from `a` to `m` is crossed from `a` to
`b`. -/
theorem IsBetween.crosses_of_crosses_left (hm : Γ.IsBetween a m b) (h : Γ.Crosses a m e) :
    Γ.Crosses a b e :=
  ⟨hm.trans_left h.isBetween_src, hm.trans_left h.isBetween_tgt, h.dist_tgt⟩

/-- If `m` lies between `a` and `b`, then a dart crossed from `m` to `b` is crossed from `a` to
`b`. -/
theorem IsBetween.crosses_of_crosses_right (hm : Γ.IsBetween a m b) (h : Γ.Crosses m b e) :
    Γ.Crosses a b e := by
  rw [← crosses_rev] at h ⊢
  exact hm.symm.crosses_of_crosses_left h

/-- Every dart of a shortest path is crossed from the start to the end of the path. -/
theorem Path.crosses_of_length_eq_dist {p : Γ.Path a b} (hp : p.length = Γ.dist a b)
    (he : e ∈ Path.darts Γ p) : Γ.Crosses a b e := by
  obtain ⟨q, r, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
  have hsrc : (q.comp ((Γ.dart e).toPath.comp r)).length = Γ.dist a b := by
    rwa [← Quiver.Path.comp_assoc, Quiver.Path.comp_toPath_eq_cons]
  refine ⟨isBetween_of_length_comp_eq_dist hsrc, isBetween_of_length_comp_eq_dist hp, ?_⟩
  rw [← length_eq_dist_of_comp_left hp, ← length_eq_dist_of_comp_left hsrc,
    Quiver.Path.length_cons]

private theorem Crosses.exists_cons_comp_length_eq_dist (h : Γ.Crosses a b e) :
    ∃ (q : Γ.Path a (Γ.src e)) (r : Γ.Path (Γ.tgt e) b),
      q.length = Γ.dist a (Γ.src e) ∧ ((q.cons (Γ.dart e)).comp r).length = Γ.dist a b := by
  -- A shortest path to the source, the dart, and a shortest path from its target.
  obtain ⟨q, hq⟩ := exists_length_eq_dist h.isBetween_src.nonempty_path_left
  obtain ⟨r, hr⟩ := exists_length_eq_dist h.isBetween_tgt.nonempty_path_right
  refine ⟨q, r, hq, ?_⟩
  have := h.isBetween_tgt.dist_add_dist
  have := h.dist_tgt
  simp only [Quiver.Path.length_comp, Quiver.Path.length_cons]
  lia

/-- A dart is crossed from `a` to `b` exactly when it is a dart of a shortest path from `a` to
`b`. -/
theorem crosses_iff_exists_length_eq_dist :
    Γ.Crosses a b e ↔ ∃ p : Γ.Path a b, p.length = Γ.dist a b ∧ e ∈ Path.darts Γ p := by
  refine ⟨fun h => ?_, fun ⟨p, hp, he⟩ => Path.crosses_of_length_eq_dist hp he⟩
  obtain ⟨q, r, -, h⟩ := h.exists_cons_comp_length_eq_dist
  exact ⟨_, h, by simp⟩

/-- A vertex `x ≠ b` between `a` and `b` is the source of a dart crossed from `a` to `b`. -/
theorem exists_crosses_of_isBetween (hx : Γ.IsBetween a x b) (hxb : x ≠ b) :
    ∃ e : Γ.E, Γ.Crosses a b e ∧ Γ.src e = x := by
  have hpos : Γ.dist x b ≠ 0 := (dist_eq_zero_iff hx.nonempty_path_right).not.mpr hxb
  obtain ⟨p, hp⟩ := exists_length_eq_dist hx.nonempty_path_left
  obtain ⟨q, hq⟩ := exists_length_eq_dist hx.nonempty_path_right
  obtain ⟨y, f, q', -, rfl⟩ := q.eq_toPath_comp_of_length_eq_succ (n := q.length - 1) (by lia)
  exact ⟨f.1, Path.crosses_of_length_eq_dist
    (by rw [Quiver.Path.length_comp, hp, hq, hx.dist_add_dist]) (by simp), f.2.1⟩

/-! ### Acyclic graphs -/

/-- In an acyclic graph, the vertices between `a` and `b` are the vertices of a reduced path `p`
from `a` to `b`. -/
theorem IsAcyclic.isBetween_iff_mem_vertices (h : Γ.IsAcyclic) {p : Γ.Path a b}
    (hp : Path.IsReduced Γ p) : Γ.IsBetween a x b ↔ x ∈ p.vertices := by
  refine ⟨fun hx => ?_, Path.isBetween_of_length_eq_dist (h.dist_eq_length hp).symm⟩
  obtain ⟨q, hq, hxq⟩ := isBetween_iff_exists_length_eq_dist.mp hx
  rwa [h.eq_of_isReduced hp (Path.isReduced_of_length_le_dist hq.le)]

/-- In an acyclic graph, the darts crossed from `a` to `b` are the darts of a reduced path `p`
from `a` to `b`. -/
theorem IsAcyclic.crosses_iff_mem_darts (h : Γ.IsAcyclic) {p : Γ.Path a b}
    (hp : Path.IsReduced Γ p) : Γ.Crosses a b e ↔ e ∈ Path.darts Γ p := by
  refine ⟨fun he => ?_, Path.crosses_of_length_eq_dist (h.dist_eq_length hp).symm⟩
  obtain ⟨q, hq, heq⟩ := crosses_iff_exists_length_eq_dist.mp he
  rwa [h.eq_of_isReduced hp (Path.isReduced_of_length_le_dist hq.le)]

/-- In an acyclic graph, if `m` lies between `a` and `b`, then a dart is crossed from `a` to `b`
exactly when it is crossed from `a` to `m` or from `m` to `b`. -/
theorem IsAcyclic.crosses_iff_crosses_or_crosses (h : Γ.IsAcyclic) (hm : Γ.IsBetween a m b) :
    Γ.Crosses a b e ↔ Γ.Crosses a m e ∨ Γ.Crosses m b e := by
  refine ⟨fun he => ?_, fun he => he.elim hm.crosses_of_crosses_left hm.crosses_of_crosses_right⟩
  obtain ⟨p, hp, hmp⟩ := isBetween_iff_exists_length_eq_dist.mp hm
  obtain ⟨q, r, rfl⟩ := p.exists_eq_comp_of_mem_vertices hmp
  have := (h.crosses_iff_mem_darts (Path.isReduced_of_length_le_dist hp.le)).mp he
  rw [Path.darts_comp, List.mem_append] at this
  exact this.imp (Path.crosses_of_length_eq_dist (length_eq_dist_of_comp_left hp))
    (Path.crosses_of_length_eq_dist (length_eq_dist_of_comp_right hp))

/-- In an acyclic graph, a dart crossed from `a` to `b` is determined by its source. -/
theorem IsAcyclic.eq_of_crosses_of_src_eq (h : Γ.IsAcyclic) {e e' : Γ.E} (he : Γ.Crosses a b e)
    (he' : Γ.Crosses a b e') (hs : Γ.src e = Γ.src e') : e = e' := by
  -- The two shortest paths through `e` and through `e'` coincide, and so do their prefixes.
  obtain ⟨q, r, hq, hqr⟩ := he.exists_cons_comp_length_eq_dist
  obtain ⟨q', r', hq', hqr'⟩ := he'.exists_cons_comp_length_eq_dist
  have := congrArg (Path.darts Γ) (h.eq_of_isReduced (Path.isReduced_of_length_le_dist hqr.le)
    (Path.isReduced_of_length_le_dist hqr'.le))
  simp only [Path.darts_comp, Path.darts_cons, dart_val, List.append_assoc,
    List.singleton_append] at this
  have hlen : (Path.darts Γ q).length = (Path.darts Γ q').length := by
    rw [Path.length_darts, Path.length_darts, hq, hq', hs]
  exact (List.cons.inj (List.append_inj this hlen).2).1

/-- In an acyclic graph, only finitely many darts are crossed from `a` to `b`. -/
theorem IsAcyclic.finite_setOf_crosses (h : Γ.IsAcyclic) (a b : Γ.V) :
    {e | Γ.Crosses a b e}.Finite := by
  rcases eq_or_ne (Γ.dist a b) 0 with h0 | h0
  · exact Set.finite_empty.subset fun e he => he.dist_pos.ne' h0
  obtain ⟨p⟩ := nonempty_path_of_dist_ne_zero h0
  exact (List.finite_toSet _).subset fun e he =>
    (h.crosses_iff_mem_darts (Path.isReduced_reduce Γ p)).mp he

/-- In an acyclic graph, exactly `dist a b` darts are crossed from `a` to `b`. -/
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

/-- In an acyclic graph, a vertex between `a` and `b` lies between `a` and `c` or between `c` and
`b`, for every vertex `c` joined to `a`. -/
theorem IsAcyclic.isBetween_or_isBetween (h : Γ.IsAcyclic) (hx : Γ.IsBetween a x b)
    (hc : Nonempty (Γ.Path a c)) : Γ.IsBetween a x c ∨ Γ.IsBetween c x b := by
  obtain ⟨p⟩ := hc
  obtain ⟨q⟩ := hx.nonempty_path
  rcases eq_or_ne x b with rfl | hxb
  · exact .inr (isBetween_right ⟨p.reverse.comp q⟩)
  obtain ⟨e, he, rfl⟩ := exists_crosses_of_isBetween hx hxb
  -- The reduced path from `a` to `b` is the reduction of the reduced paths through `c`.
  have hp := Path.isReduced_reduce Γ p
  have hq := Path.isReduced_reduce Γ (p.reverse.comp q)
  have hr := (Path.darts_reduce_sublist Γ
    ((Path.reduce Γ p).comp (Path.reduce Γ (p.reverse.comp q)))).subset
    ((h.crosses_iff_mem_darts (Path.isReduced_reduce Γ _)).mp he)
  rw [Path.darts_comp, List.mem_append] at hr
  exact hr.imp (fun he => ((h.crosses_iff_mem_darts hp).mpr he).isBetween_src)
    (fun he => ((h.crosses_iff_mem_darts hq).mpr he).isBetween_src)

/-- In an acyclic graph, the vertices between two vertices form a convex set. -/
theorem IsAcyclic.isConvex_setOf_isBetween (h : Γ.IsAcyclic) (a b : Γ.V) :
    Γ.IsConvex {x | Γ.IsBetween a x b} := by
  refine isConvex_iff.mpr fun u hu v hv p hp e he => ?_
  rcases h.isBetween_or_isBetween ((h.crosses_iff_mem_darts hp).mpr he).isBetween_src
    hu.symm.nonempty_path_right with hw | hw
  · exact hu.trans_left hw.symm
  · exact hv.trans_left hw

/-- In an acyclic graph, a vertex between `a` and `b` is determined by its distance from `a`. -/
theorem IsAcyclic.eq_of_isBetween_of_dist_eq (h : Γ.IsAcyclic) {y : Γ.V}
    (hx : Γ.IsBetween a x b) (hy : Γ.IsBetween a y b) (hxy : Γ.dist a x = Γ.dist a y) : x = y := by
  -- `x` lies between `a` and `y`, or between `y` and `b`; either way it is at distance 0 from `y`.
  rcases h.isBetween_or_isBetween hx hy.nonempty_path_left with h' | h' <;>
    simp only [isBetween_iff] at hx hy h'
  · exact (dist_eq_zero_iff h'.2.1).mp (by lia)
  · exact ((dist_eq_zero_iff h'.1).mp (by lia)).symm

/-! ### Trees -/

/-- Three vertices of a tree have a unique median: a vertex lying between any two of them. -/
theorem IsTree.existsUnique_isBetween (h : Γ.IsTree) (a b c : Γ.V) :
    ∃! m : Γ.V, Γ.IsBetween a m b ∧ Γ.IsBetween b m c ∧ Γ.IsBetween a m c := by
  -- The three sets of vertices between two of `a`, `b`, `c` are convex and pairwise meet.
  have hp := h.nonempty_path
  obtain ⟨m, ⟨hab, hbc⟩, hac⟩ := h.inter_inter_nonempty (h.isAcyclic.isConvex_setOf_isBetween a b)
    (h.isAcyclic.isConvex_setOf_isBetween b c) (h.isAcyclic.isConvex_setOf_isBetween a c)
    ⟨b, isBetween_right (hp a b), isBetween_left (hp b c)⟩
    ⟨a, isBetween_left (hp a b), isBetween_left (hp a c)⟩
    ⟨c, isBetween_right (hp b c), isBetween_right (hp a c)⟩
  refine ⟨m, ⟨hab, hbc, hac⟩, fun m' ⟨hab', hbc', hac'⟩ =>
    h.isAcyclic.eq_of_isBetween_of_dist_eq hab' hab ?_⟩
  -- The distance from `a` to a median is determined by the distances between `a`, `b` and `c`.
  have := Γ.dist_comm b m
  have := Γ.dist_comm b m'
  simp only [Set.mem_ofPred_eq, isBetween_iff] at hab hbc hac hab' hbc' hac'
  lia

end SerreGraph

end TauCeti
