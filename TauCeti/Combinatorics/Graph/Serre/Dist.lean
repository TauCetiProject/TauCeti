/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Tree
public import TauCeti.Combinatorics.Quiver.Prefunctor
public import TauCeti.Combinatorics.Quiver.Symmetric
public import Mathlib.Combinatorics.Quiver.Path.Vertices
public import Mathlib.Order.Lattice.Nat

/-!
# The path distance of a Serre graph

The distance between two vertices of a Serre graph is the least length of a path joining them,
and `0` when there is no such path, following Mathlib's `SimpleGraph.dist`. Between joined
vertices it vanishes exactly on the diagonal, is symmetric, and satisfies the triangle
inequality. Graph morphisms do not increase it. Every piece of a shortest path is a shortest path,
so that along a shortest path the distance between two vertices is the difference of their
positions.

A path no longer than the distance between its endpoints is reduced. In an acyclic graph the
unique reduced path between two vertices realizes their distance, since free reduction never
lengthens a path. In a preconnected graph, a pair of vertices at minimal distance between two
nonempty sets of vertices is joined by a reduced path meeting the first set only at its start and
the second only at its end. The distance from a vertex attains a minimum on every nonempty set
of vertices, and a shortest path from the vertex to a minimizer meets the set only at its end; in
an acyclic graph this applies to the reduced path.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2.
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- The distance between two vertices of a Serre graph: the least length of a path from the
first to the second, or `0` when there is none. -/
noncomputable def dist (a b : Γ.V) : ℕ :=
  sInf (Set.range (Quiver.Path.length : Γ.Path a b → ℕ))

variable {Γ}

/-- Every path is at least as long as the distance between its endpoints. -/
theorem dist_le_length {a b : Γ.V} (p : Γ.Path a b) : Γ.dist a b ≤ p.length :=
  Nat.sInf_le ⟨p, rfl⟩

/-- Joined vertices are joined by a path whose length is their distance. -/
theorem exists_length_eq_dist {a b : Γ.V} (h : Nonempty (Γ.Path a b)) :
    ∃ p : Γ.Path a b, p.length = Γ.dist a b :=
  Nat.sInf_mem (Set.range_nonempty_iff_nonempty.mpr h)

/-- Vertices joined by no path are at distance zero. -/
theorem dist_of_isEmpty {a b : Γ.V} (h : IsEmpty (Γ.Path a b)) : Γ.dist a b = 0 := by
  rw [dist, Set.range_eq_empty_iff.mpr h, Nat.sInf_empty]

@[simp] theorem dist_self (a : Γ.V) : Γ.dist a a = 0 :=
  Nat.le_zero.mp (dist_le_length (Quiver.Path.nil : Γ.Path a a))

/-- Joined vertices are at distance zero exactly when they are equal. -/
theorem dist_eq_zero_iff {a b : Γ.V} (h : Nonempty (Γ.Path a b)) : Γ.dist a b = 0 ↔ a = b := by
  refine ⟨fun hd => ?_, fun hab => hab ▸ dist_self a⟩
  obtain ⟨p, hp⟩ := exists_length_eq_dist h
  exact p.eq_of_length_zero (hp.trans hd)

theorem dist_comm (a b : Γ.V) : Γ.dist a b = Γ.dist b a := by
  -- Reversal is a length-preserving bijection between the paths in the two directions.
  suffices h : ∀ a b : Γ.V, Γ.dist b a ≤ Γ.dist a b from (h b a).antisymm (h a b)
  intro a b
  rcases isEmpty_or_nonempty (Γ.Path a b) with hab | hab
  · have hba : IsEmpty (Γ.Path b a) := ⟨fun p => hab.false p.reverse⟩
    rw [dist_of_isEmpty hab, dist_of_isEmpty hba]
  · obtain ⟨p, hp⟩ := exists_length_eq_dist hab
    calc Γ.dist b a ≤ p.reverse.length := dist_le_length p.reverse
      _ = Γ.dist a b := by rw [Quiver.Path.length_reverse, hp]

/-- The triangle inequality, for vertices joined in sequence. -/
theorem dist_triangle {a b c : Γ.V} (hab : Nonempty (Γ.Path a b))
    (hbc : Nonempty (Γ.Path b c)) : Γ.dist a c ≤ Γ.dist a b + Γ.dist b c := by
  obtain ⟨p, hp⟩ := exists_length_eq_dist hab
  obtain ⟨q, hq⟩ := exists_length_eq_dist hbc
  rw [← hp, ← hq, ← Quiver.Path.length_comp]
  exact dist_le_length (p.comp q)

/-- A dart joins vertices at distance at most one. -/
theorem dist_src_tgt_le_one (e : Γ.E) : Γ.dist (Γ.src e) (Γ.tgt e) ≤ 1 :=
  dist_le_length (Γ.dart e).toPath

/-- Vertices at distance one are the endpoints of a dart. -/
theorem exists_src_eq_and_tgt_eq_of_dist_eq_one {a b : Γ.V} (h : Γ.dist a b = 1) :
    ∃ e : Γ.E, Γ.src e = a ∧ Γ.tgt e = b := by
  have hab : Nonempty (Γ.Path a b) := by
    by_contra hne
    rw [dist_of_isEmpty (not_nonempty_iff.mp hne)] at h
    exact absurd h (by decide)
  obtain ⟨p, hp⟩ := exists_length_eq_dist hab
  obtain ⟨c, e, q, hq, rfl⟩ := p.eq_toPath_comp_of_length_eq_succ (hp.trans h)
  obtain rfl := q.eq_of_length_zero hq
  exact ⟨e.1, e.2.1, e.2.2⟩

/-- Joined vertices are joined by a sequence of vertices, each joined to the next by a path and at
distance at most one from it, that reaches the second vertex after as many steps as their
distance. -/
theorem exists_forall_dist_succ_le_one {a b : Γ.V} (h : Nonempty (Γ.Path a b)) :
    ∃ u : ℕ → Γ.V, u 0 = a ∧ u (Γ.dist a b) = b ∧
      ∀ i, Nonempty (Γ.Path (u i) (u (i + 1))) ∧ Γ.dist (u i) (u (i + 1)) ≤ 1 := by
  have key : ∀ {b : Γ.V} (p : Γ.Path a b), ∃ u : ℕ → Γ.V, u 0 = a ∧ u p.length = b ∧
      ∀ i, Nonempty (Γ.Path (u i) (u (i + 1))) ∧ Γ.dist (u i) (u (i + 1)) ≤ 1 := by
    intro b p
    induction p with
    | nil => exact ⟨fun _ => a, rfl, rfl, fun _ => ⟨⟨.nil⟩, by simp⟩⟩
    | @cons b c p e ih =>
      obtain ⟨u, hu₀, hu, hstep⟩ := ih
      refine ⟨fun i => if i ≤ p.length then u i else c, by simp [hu₀], by simp, fun i => ?_⟩
      rcases Nat.lt_trichotomy i p.length with hi | rfl | hi
      · simpa [hi.le, Nat.succ_le_of_lt hi] using hstep i
      · simpa [hu] using And.intro (Nonempty.intro e.toPath) (dist_le_length e.toPath)
      · simpa [Nat.not_le.mpr hi, Nat.not_le.mpr (Nat.lt_succ_of_lt hi)] using
          Nonempty.intro (Quiver.Path.nil : Γ.Path c c)
  obtain ⟨p, hp⟩ := exists_length_eq_dist h
  exact hp ▸ key p

/-! ### Shortest paths -/

/-- An initial piece of a shortest path is a shortest path. -/
theorem length_eq_dist_of_comp_left {a b c : Γ.V} {p : Γ.Path a b} {q : Γ.Path b c}
    (h : (p.comp q).length = Γ.dist a c) : p.length = Γ.dist a b := by
  have := dist_triangle ⟨p⟩ ⟨q⟩
  have := dist_le_length p
  have := dist_le_length q
  rw [Quiver.Path.length_comp] at h
  omega

/-- A final piece of a shortest path is a shortest path. -/
theorem length_eq_dist_of_comp_right {a b c : Γ.V} {p : Γ.Path a b} {q : Γ.Path b c}
    (h : (p.comp q).length = Γ.dist a c) : q.length = Γ.dist b c := by
  have := dist_triangle ⟨p⟩ ⟨q⟩
  have := dist_le_length p
  have := dist_le_length q
  rw [Quiver.Path.length_comp] at h
  omega

/-- Along a shortest path, the distance between two vertices is the difference of their
positions. -/
theorem dist_getElem_vertices {a b : Γ.V} {p : Γ.Path a b} (hp : p.length = Γ.dist a b)
    {i j : ℕ} (hij : i ≤ j) (hj : j < p.vertices.length) :
    Γ.dist p.vertices[i] p.vertices[j] = j - i := by
  obtain ⟨y, p₁, p₂, rfl, rfl, hy⟩ := p.exists_eq_comp_and_length_eq_of_lt_length j hj
  obtain ⟨x, q, r, rfl, rfl⟩ := p₁.exists_eq_comp_of_le_length hij
  have hx : ((q.comp r).comp p₂).vertices[q.length] = x := by
    simpa only [Quiver.Path.comp_assoc, List.get_eq_getElem] using
      q.vertices_comp_get_length_eq (r.comp p₂)
  have h₁ := length_eq_dist_of_comp_left hp
  rw [hx, ← hy, ← length_eq_dist_of_comp_right h₁, Quiver.Path.length_comp,
    Nat.add_sub_cancel_left]

/-- A graph morphism does not increase the distance between joined vertices. -/
theorem Hom.dist_le {Δ : SerreGraph} (f : Γ.Hom Δ) {a b : Γ.V} (h : Nonempty (Γ.Path a b)) :
    Δ.dist (f.mapV a) (f.mapV b) ≤ Γ.dist a b := by
  obtain ⟨p, hp⟩ := exists_length_eq_dist h
  calc Δ.dist (f.mapV a) (f.mapV b) ≤ (f.toPrefunctor.mapPath p).length :=
        dist_le_length (f.toPrefunctor.mapPath p)
    _ = Γ.dist a b := by rw [Prefunctor.length_mapPath, hp]

/-- In a path with at least two darts, the target of the first dart `f` and the source of the
last dart `e` are at distance at most the length of the path minus two. -/
theorem Path.dist_tgt_src_add_two_le {a b : Γ.V} (p : Γ.Path a b) {e f : Γ.E}
    (hf : f ∈ (Path.darts Γ p).head?) (he : e ∈ (Path.darts Γ p).getLast?)
    (h : 2 ≤ p.length) : Γ.dist (Γ.tgt f) (Γ.src e) + 2 ≤ p.length := by
  obtain ⟨c, f', q, hq, rfl⟩ := p.eq_toPath_comp_of_length_eq_succ (n := p.length - 1) (by omega)
  cases q with
  | nil => simp [Quiver.Path.length_toPath] at h
  | cons q e' =>
    simp only [Quiver.Path.comp_cons, Path.darts_cons, Path.darts_comp, Path.darts_toPath,
      List.cons_append, List.nil_append, List.head?_cons, Option.mem_def,
      Option.some.injEq] at hf
    rw [Quiver.Path.comp_cons, Path.darts_cons, List.getLast?_concat, Option.mem_def,
      Option.some.injEq] at he
    subst hf he
    have := dist_le_length q
    rw [f'.2.2, e'.2.1, Quiver.Path.length_comp, Quiver.Path.length_toPath,
      Quiver.Path.length_cons]
    omega

/-- A path no longer than the distance between its endpoints is reduced. -/
theorem Path.isReduced_of_length_le_dist {a b : Γ.V} {p : Γ.Path a b}
    (hp : p.length ≤ Γ.dist a b) : Path.IsReduced Γ p := by
  have hlen : (Path.darts Γ (Path.reduce Γ p)).length = (Path.darts Γ p).length := by
    have := dist_le_length (Path.reduce Γ p)
    have := Path.length_reduce_le Γ p
    rw [Path.length_darts, Path.length_darts]
    omega
  have hdarts := (Path.darts_reduce_sublist Γ p).eq_of_length hlen
  rw [Path.isReduced_iff_isChain, ← hdarts, ← Path.isReduced_iff_isChain]
  exact Path.isReduced_reduce Γ p

/-! ### Distances in acyclic graphs -/

/-- In an acyclic graph, a reduced path realizes the distance between its endpoints. -/
theorem IsAcyclic.dist_eq_length (h : Γ.IsAcyclic) {a b : Γ.V} {p : Γ.Path a b}
    (hp : Path.IsReduced Γ p) : Γ.dist a b = p.length := by
  refine (dist_le_length p).antisymm ?_
  obtain ⟨q, hq⟩ := exists_length_eq_dist ⟨p⟩
  rw [← hq, h.eq_of_isReduced hp (Path.isReduced_reduce Γ q)]
  exact Path.length_reduce_le Γ q

/-! ### Shortest paths between sets of vertices -/

/-- In a preconnected graph, two nonempty sets of vertices are joined by a reduced path whose darts
end outside the first set and start outside the second: it meets the first set only at its start
and the second only at its end. -/
theorem Preconnected.exists_isReduced_path (h : Γ.Preconnected) {A B : Set Γ.V}
    (hA : A.Nonempty) (hB : B.Nonempty) : ∃ a ∈ A, ∃ b ∈ B, ∃ p : Γ.Path a b,
      Path.IsReduced Γ p ∧ ∀ e ∈ Path.darts Γ p, Γ.tgt e ∉ A ∧ Γ.src e ∉ B := by
  classical
  -- Choose `a ∈ A` and `b ∈ B` at minimal distance, and reduce a shortest path between them.
  have hex : ∃ n, ∃ a ∈ A, ∃ b ∈ B, Γ.dist a b = n :=
    ⟨_, hA.some, hA.some_mem, hB.some, hB.some_mem, rfl⟩
  obtain ⟨a, ha, b, hb, hab⟩ := Nat.find_spec hex
  have hmin : ∀ a' ∈ A, ∀ b' ∈ B, Nat.find hex ≤ Γ.dist a' b' := fun a' ha' b' hb' =>
    Nat.find_min' hex ⟨a', ha', b', hb', rfl⟩
  obtain ⟨s, hs⟩ := exists_length_eq_dist ((preconnected_iff Γ).1 h a b)
  have hlen : (Path.reduce Γ s).length = Nat.find hex := by
    have := dist_le_length (Path.reduce Γ s)
    have := Path.length_reduce_le Γ s
    omega
  refine ⟨a, ha, b, hb, Path.reduce Γ s, Path.isReduced_reduce Γ s, fun e he => ?_⟩
  -- A dart of the path cuts it into two pieces, each strictly shorter than the path.
  obtain ⟨q, r, hqr⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ _ he
  have hlen' : q.length + 1 + r.length = Nat.find hex := by
    rw [← hlen, hqr, Quiver.Path.length_comp, Quiver.Path.length_cons]
  refine ⟨fun hA' => ?_, fun hB' => ?_⟩
  · have := (hmin _ hA' b hb).trans (dist_le_length r)
    omega
  · have := (hmin a ha _ hB').trans (dist_le_length q)
    omega

/-- The distance from a vertex attains a minimum on every nonempty set of vertices. When the vertex
is joined to every vertex of the set, as in a preconnected graph, the minimizer is a nearest
vertex of the set. -/
theorem exists_forall_dist_le {C : Set Γ.V} (hC : C.Nonempty) (v : Γ.V) :
    ∃ a ∈ C, ∀ b ∈ C, Γ.dist v a ≤ Γ.dist v b := by
  obtain ⟨a, ha, hmin⟩ := exists_minimalFor_of_wellFoundedLT (· ∈ C) (Γ.dist v) hC
  exact ⟨a, ha, fun b hb => (le_total _ _).elim id (hmin hb)⟩

/-- If `a` minimizes the distance from `v` on a set `C` of vertices, then no dart of a shortest
path from `v` to `a` starts in `C`. -/
theorem Path.src_notMem_of_forall_dist_le {C : Set Γ.V} {v a : Γ.V}
    (hmin : ∀ b ∈ C, Γ.dist v a ≤ Γ.dist v b) {q : Γ.Path v a} (hq : q.length ≤ Γ.dist v a)
    {e : Γ.E} (he : e ∈ Path.darts Γ q) : Γ.src e ∉ C := by
  intro hC
  obtain ⟨q₁, r, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ q he
  have h₁ := (hmin _ hC).trans (dist_le_length q₁)
  rw [Quiver.Path.length_comp, Quiver.Path.length_cons] at hq
  omega

/-- In an acyclic graph, if `a` minimizes the distance from `v` on a set `C` of vertices, then no
dart of the reduced path from `v` to `a` starts in `C`. -/
theorem IsAcyclic.src_notMem_of_forall_dist_le (h : Γ.IsAcyclic) {C : Set Γ.V} {v a : Γ.V}
    (hmin : ∀ b ∈ C, Γ.dist v a ≤ Γ.dist v b) {q : Γ.Path v a} (hq : Path.IsReduced Γ q)
    {e : Γ.E} (he : e ∈ Path.darts Γ q) : Γ.src e ∉ C :=
  Path.src_notMem_of_forall_dist_le hmin (h.dist_eq_length hq).ge he

end SerreGraph
end TauCeti
