/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Convex.Basic
public import TauCeti.Combinatorics.Graph.Serre.Dist
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

A convex set contains every vertex between two of its vertices. Reduced paths from a vertex `v`
outside a convex set `C` into `C` all start with the same dart, so a vertex `m` of `C` nearest to
`v` is a *gate*: it lies between `v` and every vertex of `C` (in the same component).

In an acyclic graph the darts crossed from `a` to `b` and the vertices between them are those of
a reduced path from `a` to `b`, when there is one, since it is a shortest path. A set of vertices
is then convex exactly when it contains the vertices between any two of its vertices. So the
vertices between `a` and `b` form a convex set, and the image of a convex set whose vertices are
joined by paths, under a map sending each dart to a dart or to a vertex, is convex.
For a third vertex `c` in the same component, a vertex between `a` and `b` nearest to `c` is a
gate, so it lies between any two of `a`, `b` and `c`. This median is unique because a vertex
between `a` and `b` is determined by its distance from `a`, and for a median `m` the three
equations of betweenness force `2 dist a m = dist a b + dist a c - dist b c`.

## Main definitions

* `TauCeti.SerreGraph.IsBetween`: the vertex `x` lies between `a` and `b`.
* `TauCeti.SerreGraph.Crosses`: the dart `e` is crossed from `a` to `b`.

## Main results

* `TauCeti.SerreGraph.isBetween_iff_exists_length_eq_dist`,
  `TauCeti.SerreGraph.crosses_iff_exists_length_eq_dist`: the vertices between `a` and `b` and
  the darts crossed from `a` to `b` are those of the shortest paths from `a` to `b`.
* `TauCeti.SerreGraph.IsConvex.isBetween_of_forall_dist_le`: a vertex of a convex set nearest to
  `v` lies between `v` and every vertex of the set.
* `TauCeti.SerreGraph.IsAcyclic.crosses_iff_mem_darts`: in an acyclic graph, the darts crossed
  from `a` to `b` are the darts of a reduced path `p` from `a` to `b`.
* `TauCeti.SerreGraph.IsAcyclic.natCard_crosses`: in an acyclic graph, `dist a b` darts are
  crossed from `a` to `b`.
* `TauCeti.SerreGraph.IsAcyclic.crosses_or_crosses`: in an acyclic graph, a dart crossed from `a`
  to `b` is crossed from `a` to `c` or from `c` to `b`, for every vertex `c` joined to `a`.
* `TauCeti.SerreGraph.IsAcyclic.crosses_iff_crosses_or_crosses`: in an acyclic graph, the darts
  crossed from `a` to `b` are those crossed from `a` to `m` or from `m` to `b`, for `m` between
  `a` and `b`.
* `TauCeti.SerreGraph.IsAcyclic.isConvex_iff_forall_isBetween`: in an acyclic graph, the convex
  sets are the sets containing the vertices between any two of their vertices.
* `TauCeti.SerreGraph.IsAcyclic.isConvex_image`: in an acyclic graph, the image of a convex set
  whose vertices are joined by paths, under a map sending each dart to a dart or to a vertex, is
  convex.
* `TauCeti.SerreGraph.IsAcyclic.existsUnique_isBetween`: in an acyclic graph, three vertices joined
  by paths have a unique median.

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

variable {Γ} {a b c m v x : Γ.V} {e : Γ.E}

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

/-- A vertex between two vertices at distance at most one is one of them. -/
theorem IsBetween.eq_or_eq_of_dist_le_one (hx : Γ.IsBetween a x b) (hab : Γ.dist a b ≤ 1) :
    x = a ∨ x = b := by
  have := hx.dist_add_dist
  rcases Nat.eq_zero_or_pos (Γ.dist a x) with h0 | h0
  · exact .inl ((dist_eq_zero_iff hx.nonempty_path_left).mp h0).symm
  · exact .inr ((dist_eq_zero_iff hx.nonempty_path_right).mp (by lia))

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

/-- If a dart is crossed from `a` to some vertex, then its reverse is not crossed from `a` to any
vertex: the dart leads away from `a`. -/
theorem Crosses.not_crosses_rev (h : Γ.Crosses a b e) : ¬Γ.Crosses a c (Γ.rev e) := fun h' => by
  have := h.dist_tgt
  have := h'.dist_tgt
  rw [src_rev, tgt_rev] at this
  lia

/-- A dart crossed from `a` to `m` is not crossed from `m` to any vertex: it leads towards `m`. -/
theorem Crosses.not_crosses_right (h : Γ.Crosses a m e) : ¬Γ.Crosses m b e := by
  simpa using (crosses_rev.mpr h).not_crosses_rev

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

/-- A dart crossed from `a` to `b` is crossed from its source to `b`. -/
theorem Crosses.crosses_src (h : Γ.Crosses a b e) : Γ.Crosses (Γ.src e) b e := by
  obtain ⟨q, r, -, hqr⟩ := h.exists_cons_comp_length_eq_dist
  rw [← Quiver.Path.comp_toPath_eq_cons, Quiver.Path.comp_assoc] at hqr
  exact Path.crosses_of_length_eq_dist (length_eq_dist_of_comp_right hqr) (by simp)

/-- A vertex `x ≠ b` between `a` and `b` is the source of a dart crossed from `a` to `b`. -/
theorem exists_crosses_of_isBetween (hx : Γ.IsBetween a x b) (hxb : x ≠ b) :
    ∃ e : Γ.E, Γ.Crosses a b e ∧ Γ.src e = x := by
  have hpos : Γ.dist x b ≠ 0 := (dist_eq_zero_iff hx.nonempty_path_right).not.mpr hxb
  obtain ⟨p, hp⟩ := exists_length_eq_dist hx.nonempty_path_left
  obtain ⟨q, hq⟩ := exists_length_eq_dist hx.nonempty_path_right
  obtain ⟨y, f, q', -, rfl⟩ := q.eq_toPath_comp_of_length_eq_succ (n := q.length - 1) (by lia)
  exact ⟨f.val, Path.crosses_of_length_eq_dist
    (by rw [Quiver.Path.length_comp, hp, hq, hx.dist_add_dist]) (by simp), f.property.1⟩

/-- A convex set contains every vertex between two of its vertices. -/
theorem IsConvex.mem_of_isBetween {C : Set Γ.V} (hC : Γ.IsConvex C) (ha : a ∈ C) (hb : b ∈ C)
    (hx : Γ.IsBetween a x b) : x ∈ C := by
  -- Unless `x = b`, the vertex `x` is the source of a dart of a shortest, hence reduced, path.
  rcases eq_or_ne x b with rfl | hxb
  · exact hb
  obtain ⟨e, he, rfl⟩ := exists_crosses_of_isBetween hx hxb
  obtain ⟨p, hp, hep⟩ := crosses_iff_exists_length_eq_dist.mp he
  exact hC.src_mem ha hb (Path.isReduced_of_length_le_dist hp.le) hep

/-- Two reduced paths from a vertex outside a convex set `C` to vertices of `C` start with the same
dart. -/
theorem IsConvex.head?_darts_eq {C : Set Γ.V} (hC : Γ.IsConvex C) (hv : v ∉ C) (hm : m ∈ C)
    (hx : x ∈ C) {p : Γ.Path v m} {q : Γ.Path v x} (hp : Path.IsReduced Γ p)
    (hq : Path.IsReduced Γ q) : (Path.darts Γ p).head? = (Path.darts Γ q).head? := by
  -- Otherwise the reverse of `p` followed by `q` is a reduced path from `m` to `x`, and its dart
  -- following `v` starts outside `C`.
  by_contra hne
  obtain ⟨e, he⟩ : ∃ e, (Path.darts Γ q).head? = some e := by
    cases hq' : Path.darts Γ q with
    | nil => exact absurd ((Path.eq_of_darts_eq_nil Γ q hq') ▸ hx) hv
    | cons e _ => exact ⟨e, rfl⟩
  refine hv (Path.src_eq_of_mem_head?_darts Γ q (Option.mem_def.mpr he) ▸ hC.src_mem hm hx
    ((Path.isReduced_comp_iff Γ p.reverse q).mpr ⟨(Path.isReduced_reverse Γ p).mpr hp, hq, ?_⟩)
    (e := e) (by simp [List.mem_of_mem_head? (Option.mem_def.mpr he)]))
  intro e₀ he₀ f hf hfe
  simp only [Path.darts_reverse, List.getLast?_map, List.getLast?_reverse, Option.mem_def,
    Option.map_eq_some_iff] at he₀
  obtain ⟨d, hd, rfl⟩ := he₀
  rw [Γ.rev_rev] at hfe
  exact hne (by rw [hd, ← hfe, Option.mem_def.mp hf])

/-- A vertex `m` of a convex set `C` nearest to a vertex `v` lies between `v` and every vertex of
`C` joined to `m`, provided `v` is joined to `m`. -/
theorem IsConvex.isBetween_of_forall_dist_le {C : Set Γ.V} (hC : Γ.IsConvex C) (hm : m ∈ C)
    (hmin : ∀ b ∈ C, Γ.dist v m ≤ Γ.dist v b) (hx : x ∈ C) (hvm : Nonempty (Γ.Path v m))
    (hmx : Nonempty (Γ.Path m x)) : Γ.IsBetween v m x := by
  -- Induction on `dist v m`: shortest paths from `v ∉ C` to `m` and to `x` start with the same
  -- dart, and `m` is also a vertex of `C` nearest to its target.
  induction hd : Γ.dist v m generalizing v with
  | zero =>
    obtain rfl := (dist_eq_zero_iff hvm).mp hd
    exact isBetween_left hmx
  | succ n ih =>
    have hvx : Nonempty (Γ.Path v x) := hvm.elim fun p => hmx.elim fun r => ⟨p.comp r⟩
    have hvC : v ∉ C := fun hv => by simpa [hd] using hmin v hv
    obtain ⟨q, hq⟩ := exists_length_eq_dist hvm
    obtain ⟨s, hs⟩ := exists_length_eq_dist hvx
    have hqs := hC.head?_darts_eq hvC hm hx (Path.isReduced_of_length_le_dist hq.le)
      (Path.isReduced_of_length_le_dist hs.le)
    have hs0 : Γ.dist v x ≠ 0 := fun h0 => hvC ((dist_eq_zero_iff hvx).mp h0 ▸ hx)
    obtain ⟨v₁, d, q₁, -, rfl⟩ := q.eq_toPath_comp_of_length_eq_succ (hq.trans hd)
    obtain ⟨w₁, d', s₁, -, rfl⟩ :=
      s.eq_toPath_comp_of_length_eq_succ (n := Γ.dist v x - 1) (by lia)
    obtain rfl : v₁ = w₁ := by
      simpa [d.property.2, d'.property.2] using congrArg (Option.map Γ.tgt) hqs
    have h₁ := length_eq_dist_of_comp_right hq
    have h₂ := length_eq_dist_of_comp_right hs
    have hd₁ : Γ.dist v v₁ ≤ 1 := by simpa using dist_le_length d.toPath
    simp only [Quiver.Path.length_comp, Quiver.Path.length_toPath] at hq hs h₁ h₂
    have hb := ih (v := v₁) (fun b hb => by
      have hvb := hmin b hb
      obtain ⟨t⟩ := nonempty_path_of_dist_ne_zero (by lia : Γ.dist v b ≠ 0)
      have := dist_triangle ⟨d.toPath⟩ ⟨d.toPath.reverse.comp t⟩
      lia) ⟨q₁⟩ (by lia)
    exact ⟨hvm, hmx, by have := hb.dist_add_dist; lia⟩

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

/-- In an acyclic graph, a dart crossed from `a` to `b` is crossed from `a` to `c` or from `c` to
`b`, for every vertex `c` joined to `a`. -/
theorem IsAcyclic.crosses_or_crosses (h : Γ.IsAcyclic) (he : Γ.Crosses a b e)
    (hc : Nonempty (Γ.Path a c)) : Γ.Crosses a c e ∨ Γ.Crosses c b e := by
  obtain ⟨p⟩ := hc
  obtain ⟨q⟩ := he.isBetween_src.nonempty_path
  -- The reduced path from `a` to `b` only uses darts of the reduced paths through `c`.
  have hp := Path.isReduced_reduce Γ p
  have hq := Path.isReduced_reduce Γ (p.reverse.comp q)
  have hr := (h.darts_sublist (Path.isReduced_reduce Γ q) ((Path.reduce Γ p).comp
    (Path.reduce Γ (p.reverse.comp q)))).subset
    ((h.crosses_iff_mem_darts (Path.isReduced_reduce Γ q)).mp he)
  rw [Path.darts_comp, List.mem_append] at hr
  exact hr.imp (h.crosses_iff_mem_darts hp).mpr (h.crosses_iff_mem_darts hq).mpr

/-- In an acyclic graph, if `m` lies between `a` and `b`, then a dart is crossed from `a` to `b`
exactly when it is crossed from `a` to `m` or from `m` to `b`. -/
theorem IsAcyclic.crosses_iff_crosses_or_crosses (h : Γ.IsAcyclic) (hm : Γ.IsBetween a m b) :
    Γ.Crosses a b e ↔ Γ.Crosses a m e ∨ Γ.Crosses m b e :=
  ⟨fun he => h.crosses_or_crosses he hm.nonempty_path_left,
    fun he => he.elim hm.crosses_of_crosses_left hm.crosses_of_crosses_right⟩

/-- In an acyclic graph, a dart crossed to `b`, from any vertex, is determined by its source. -/
theorem IsAcyclic.eq_of_crosses_of_src_eq (h : Γ.IsAcyclic) {a' : Γ.V} {e e' : Γ.E}
    (he : Γ.Crosses a b e) (he' : Γ.Crosses a' b e') (hs : Γ.src e = Γ.src e') : e = e' := by
  -- Both darts are crossed from their common source to `b`; the shortest paths through them
  -- coincide, and so do their prefixes.
  replace he' : Γ.Crosses (Γ.src e) b e' := hs ▸ he'.crosses_src
  obtain ⟨q, r, hq, hqr⟩ := he.crosses_src.exists_cons_comp_length_eq_dist
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
    exact .inl ⟨fun e => e.property.dist_pos.ne' h0⟩
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
  rcases eq_or_ne x b with rfl | hxb
  · obtain ⟨p⟩ := hc
    obtain ⟨q⟩ := hx.nonempty_path_left
    exact .inr (isBetween_right ⟨p.reverse.comp q⟩)
  obtain ⟨e, he, rfl⟩ := exists_crosses_of_isBetween hx hxb
  exact (h.crosses_or_crosses he hc).imp Crosses.isBetween_src Crosses.isBetween_src

/-- In an acyclic graph, the vertices between two vertices form a convex set. -/
theorem IsAcyclic.isConvex_setOf_isBetween (h : Γ.IsAcyclic) (a b : Γ.V) :
    Γ.IsConvex {x | Γ.IsBetween a x b} := by
  -- They are the vertices of a reduced path from `a` to `b`.
  refine isConvex_iff.mpr fun u (hu : Γ.IsBetween a u b) v hv => ?_
  obtain ⟨p⟩ := hu.nonempty_path
  simp only [Set.mem_ofPred_eq, h.isBetween_iff_mem_vertices (Path.isReduced_reduce Γ p)] at hu hv ⊢
  exact isConvex_iff.mp (h.isConvex_setOf_mem_vertices _) u hu v hv

/-- In an acyclic graph, a set of vertices is convex exactly when it contains every vertex between
two of its vertices. -/
theorem IsAcyclic.isConvex_iff_forall_isBetween (h : Γ.IsAcyclic) {C : Set Γ.V} :
    Γ.IsConvex C ↔ ∀ a ∈ C, ∀ b ∈ C, ∀ x, Γ.IsBetween a x b → x ∈ C :=
  ⟨fun hC _ ha _ hb _ hx => hC.mem_of_isBetween ha hb hx, fun hC => isConvex_iff.mpr
    fun a ha b hb p hp _ he => hC a ha b hb _
      ((h.isBetween_iff_mem_vertices hp).mpr (Path.src_mem_vertices_of_mem_darts Γ p he))⟩

private theorem mem_image_of_isBetween {Δ : SerreGraph} (hΔ : Δ.IsAcyclic) {C : Set Γ.V}
    (hC : Γ.IsConvex C) (hpath : ∀ y ∈ C, ∀ y' ∈ C, Nonempty (Γ.Path y y')) {φ : Γ.V → Δ.V}
    (hφ : ∀ e : Γ.E, Γ.src e ∈ C → Γ.tgt e ∈ C → φ (Γ.src e) = φ (Γ.tgt e) ∨
      ∃ e' : Δ.E, Δ.src e' = φ (Γ.src e) ∧ Δ.tgt e' = φ (Γ.tgt e)) {y y' : Γ.V}
    (hy : y ∈ C) (hy' : y' ∈ C) {u : Δ.V} (hu : Δ.IsBetween (φ y) u (φ y')) : u ∈ φ '' C := by
  -- Induction on `dist y y'`: step from `y` to the next vertex `z` of a shortest path to `y'`,
  -- whose image is `φ y` or a neighbour of it.
  induction hd : Γ.dist y y' generalizing y u with
  | zero =>
    obtain rfl := (dist_eq_zero_iff (hpath y hy y' hy')).mp hd
    exact ⟨y, hy, (isBetween_self_iff.mp hu).symm⟩
  | succ n ih =>
    obtain ⟨e, he, rfl⟩ := exists_crosses_of_isBetween
      (isBetween_left (hpath y hy y' hy')) fun h => by simp [h] at hd
    have hz := hC.mem_of_isBetween hy hy' he.isBetween_tgt
    have hd' : Γ.dist (Γ.tgt e) y' = n := by
      have := he.isBetween_tgt.dist_add_dist
      have := he.dist_tgt
      simp only [dist_self] at *
      lia
    obtain ⟨hpath, hle⟩ : Nonempty (Δ.Path (φ (Γ.src e)) (φ (Γ.tgt e))) ∧
        Δ.dist (φ (Γ.src e)) (φ (Γ.tgt e)) ≤ 1 := by
      rcases hφ e hy hz with h' | ⟨e', hs, ht⟩
      · exact ⟨⟨h' ▸ .nil⟩, by simp [h']⟩
      · exact ⟨⟨hs ▸ ht ▸ (Δ.dart e').toPath⟩, hs ▸ ht ▸ Δ.dist_src_tgt_le_one e'⟩
    rcases hΔ.isBetween_or_isBetween hu hpath with hu' | hu'
    · rcases hu'.eq_or_eq_of_dist_le_one hle with rfl | rfl
      exacts [⟨_, hy, rfl⟩, ⟨_, hz, rfl⟩]
    · exact ih hz hu' hd'

/-- Let `C` be a convex set of vertices any two of which are joined by a path. The image of `C`
under a map of vertices to an acyclic graph `Δ` is convex, when the map sends the two ends of
every dart joining vertices of `C` to one vertex or to the two ends of a dart of `Δ`. -/
theorem IsAcyclic.isConvex_image {Δ : SerreGraph} (hΔ : Δ.IsAcyclic) {C : Set Γ.V}
    (hC : Γ.IsConvex C) (hpath : ∀ y ∈ C, ∀ y' ∈ C, Nonempty (Γ.Path y y')) {φ : Γ.V → Δ.V}
    (hφ : ∀ e : Γ.E, Γ.src e ∈ C → Γ.tgt e ∈ C → φ (Γ.src e) = φ (Γ.tgt e) ∨
      ∃ e' : Δ.E, Δ.src e' = φ (Γ.src e) ∧ Δ.tgt e' = φ (Γ.tgt e)) : Δ.IsConvex (φ '' C) := by
  rw [hΔ.isConvex_iff_forall_isBetween]
  rintro _ ⟨y, hy, rfl⟩ _ ⟨y', hy', rfl⟩ u hu
  exact mem_image_of_isBetween hΔ hC hpath hφ hy hy' hu

/-- In an acyclic graph, a vertex between `a` and `b` is determined by its distance from `a`. -/
theorem IsAcyclic.eq_of_isBetween_of_dist_eq (h : Γ.IsAcyclic) {y : Γ.V}
    (hx : Γ.IsBetween a x b) (hy : Γ.IsBetween a y b) (hxy : Γ.dist a x = Γ.dist a y) : x = y := by
  -- `x` lies between `a` and `y`, or between `y` and `b`; either way it is at distance 0 from `y`.
  rcases h.isBetween_or_isBetween hx hy.nonempty_path_left with h' | h' <;>
    simp only [isBetween_iff] at hx hy h'
  · exact (dist_eq_zero_iff h'.2.1).mp (by lia)
  · exact ((dist_eq_zero_iff h'.1).mp (by lia)).symm

/-- In an acyclic graph, three vertices joined by paths have a unique median: a vertex lying
between any two of them. -/
theorem IsAcyclic.existsUnique_isBetween (h : Γ.IsAcyclic) (hab : Nonempty (Γ.Path a b))
    (hac : Nonempty (Γ.Path a c)) :
    ∃! m : Γ.V, Γ.IsBetween a m b ∧ Γ.IsBetween b m c ∧ Γ.IsBetween a m c := by
  -- A vertex `m` between `a` and `b` nearest to `c` is a median: it lies between `c` and every
  -- vertex of the convex set of vertices between `a` and `b`.
  obtain ⟨m, hm : Γ.IsBetween a m b, hmin⟩ :=
    exists_forall_dist_le (C := {x | Γ.IsBetween a x b}) ⟨a, isBetween_left hab⟩ c
  obtain ⟨p⟩ := hac
  obtain ⟨q⟩ := hm.nonempty_path_left
  have key (x : Γ.V) (hx : Γ.IsBetween a x b) : Γ.IsBetween x m c := by
    obtain ⟨r⟩ := hx.nonempty_path_left
    exact ((h.isConvex_setOf_isBetween a b).isBetween_of_forall_dist_le hm hmin hx
      ⟨p.reverse.comp q⟩ ⟨q.reverse.comp r⟩).symm
  have hma := key a (isBetween_left hab)
  have hmb := key b (isBetween_right hab)
  refine ⟨m, ⟨hm, hmb, hma⟩, fun m' ⟨hab', hbc', hac'⟩ => h.eq_of_isBetween_of_dist_eq hab' hm ?_⟩
  -- The distance from `a` to a median is determined by the distances between `a`, `b` and `c`.
  have := Γ.dist_comm b m
  have := Γ.dist_comm b m'
  simp only [isBetween_iff] at hm hmb hma hab' hbc' hac'
  lia

/-! ### Trees -/

/-- Three vertices of a tree have a unique median: a vertex lying between any two of them. -/
theorem IsTree.existsUnique_isBetween (h : Γ.IsTree) (a b c : Γ.V) :
    ∃! m : Γ.V, Γ.IsBetween a m b ∧ Γ.IsBetween b m c ∧ Γ.IsBetween a m c :=
  h.isAcyclic.existsUnique_isBetween (h.nonempty_path a b) (h.nonempty_path a c)

end SerreGraph

end TauCeti
