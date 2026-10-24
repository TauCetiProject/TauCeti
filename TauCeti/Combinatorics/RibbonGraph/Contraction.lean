/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ChordDiagram

/-!
# Spanning-tree contraction of ribbon graphs

A ribbon graph, or graph with a rotation system, on a finite set `X` of darts (half-edges) is
given by two permutations: the rotation `ρ`, whose cycles are the vertices together with the
cyclic order of the darts around each of them, and an involution `α` exchanging the two darts of
each edge. Fixed points of `α` are darts on no edge. The boundary cycles of the graph, the faces
of the closed oriented surface on which it is cellularly embedded, are the cycles of `α * ρ`.
With `V = orbitCount ρ` vertices, `E = card X - orbitCount α` edges and
`F = orbitCount (α * ρ)` faces, a connected ribbon graph has `V - E + F ≤ 2`, with equality
exactly when the surface is a sphere.

Contracting an edge `{x, α x}` whose two ends lie at different vertices merges these vertices,
splicing their cyclic orders at the edge: the new rotation is `swap x (α x) * ρ`, and the new
involution `swap x (α x) * α` deletes the edge, whose two darts remain as fixed points. The
product `α * ρ` does not change, so the boundary cycles are retained exactly. Contracting the
`V - 1` edges of a spanning tree of a connected ribbon graph leaves a single vertex, that is, a
one-vertex chord diagram in the sense of `TauCeti/Combinatorics/ChordDiagram.lean`: a disc whose
bands are the `E - V + 1` edges outside the tree. Its boundary cycles are those of the original
graph.

A `TauCeti.SpanningTreeContraction ρ α` records the result: a rotation with one orbit, and an
involution obtained from `α` by deleting `V - 1` edges, whose product is `α * ρ`. The deleted
edges then form a spanning tree. The original rotation is recovered by the vertex expansion
`ρ = α * matching * rotation` (`TauCeti.SpanningTreeContraction.mul_matching_mul_rotation`), as
`α * matching` is the product of the transpositions of the contracted edges.

## Main definitions

* `TauCeti.SpanningTreeContraction ρ α`: a one-vertex chord diagram obtained from the ribbon
  graph `(ρ, α)` by contracting a spanning tree.
* `TauCeti.SpanningTreeContraction.ofOrbitCountEqOne`: a one-vertex ribbon graph is its own
  contraction.
* `TauCeti.SpanningTreeContraction.ofContractEdge`: a contraction of the ribbon graph obtained by
  contracting one edge is a contraction of the original graph.

## Main results

* `TauCeti.isPretransitive_closure_swap_mul_swap_mul`: contracting an edge between distinct
  vertices preserves connectedness.
* `TauCeti.nonempty_spanningTreeContraction`: every connected ribbon graph on a nonempty set of
  darts has a spanning-tree contraction.
* `TauCeti.SpanningTreeContraction.isNoncrossingMatching_permCongr_matching_iff`: the Euler
  equality `V - E + F = 2` holds exactly when the bands of a spanning-tree contraction do not
  interleave, in the cyclic order of its single vertex. In particular, whether the bands
  interleave depends neither on the spanning tree nor on the numbering of the darts.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 (rotation systems and their faces).
* B. Mohar, C. Thomassen, *Graphs on Surfaces*, Johns Hopkins University Press 2001 (embedding
  schemes and the contraction of edges).
-/

public section

open Equiv Equiv.Perm MulAction

namespace TauCeti

variable {X : Type*} {ρ α : Perm X}

/-- A **spanning-tree contraction** of the ribbon graph with rotation `ρ` and edge involution `α`:
the one-vertex chord diagram left after contracting the edges of a spanning tree. Its `rotation`
is the cyclic order of all darts around the single vertex, and its `matching` is `α` with the
`V - 1` edges of the tree deleted, where `V = orbitCount ρ` is the number of vertices; their darts
become fixed points. Contraction keeps the boundary cycles: `matching * rotation = α * ρ`. -/
@[ext]
structure SpanningTreeContraction (ρ α : Perm X) where
  /-- The cyclic order of the darts around the single vertex left after contraction. -/
  rotation : Perm X
  /-- The bands of the chord diagram: the edges of `α` outside the spanning tree. -/
  matching : Perm X
  /-- The bands pair up the darts they use. -/
  involutive_matching : Function.Involutive matching
  /-- Every band is an edge of the original graph; the darts of the tree edges are fixed. -/
  matching_apply_eq_or (x : X) : matching x = x ∨ matching x = α x
  /-- Contraction keeps the boundary cycles. -/
  matching_mul_rotation : matching * rotation = α * ρ
  /-- A single vertex is left. -/
  orbitCount_rotation : orbitCount rotation = 1
  /-- Exactly one edge fewer than the number of vertices has been contracted. -/
  orbitCount_matching : orbitCount matching + 1 = orbitCount α + orbitCount ρ

namespace SpanningTreeContraction

/-- **Vertex expansion.** The original rotation is recovered from the contraction, since
`α * matching` is the product of the transpositions of the contracted edges. -/
theorem mul_matching_mul_rotation (c : SpanningTreeContraction ρ α)
    (hα : Function.Involutive α) : α * c.matching * c.rotation = ρ := by
  have hαα : α * α = 1 := Equiv.ext hα
  rw [mul_assoc, c.matching_mul_rotation, ← mul_assoc, hαα, one_mul]

/-- A ribbon graph with a single vertex is its own spanning-tree contraction, along the empty
tree. -/
def ofOrbitCountEqOne (hα : Function.Involutive α) (hρ : orbitCount ρ = 1) :
    SpanningTreeContraction ρ α where
  rotation := ρ
  matching := α
  involutive_matching := hα
  matching_apply_eq_or _ := Or.inr rfl
  matching_mul_rotation := rfl
  orbitCount_rotation := hρ
  orbitCount_matching := by rw [hρ]

/-- A one-vertex ribbon graph keeps its rotation. -/
@[simp]
theorem ofOrbitCountEqOne_rotation (hα : Function.Involutive α) (hρ : orbitCount ρ = 1) :
    (ofOrbitCountEqOne hα hρ).rotation = ρ :=
  (rfl)

/-- A one-vertex ribbon graph keeps all of its edges as bands. -/
@[simp]
theorem ofOrbitCountEqOne_matching (hα : Function.Involutive α) (hρ : orbitCount ρ = 1) :
    (ofOrbitCountEqOne hα hρ).matching = α :=
  (rfl)

variable [DecidableEq X] [Finite X]

/-- Adding an edge to the tree. A spanning-tree contraction of the ribbon graph obtained by
contracting the edge `{x, α x}`, whose ends lie at different vertices, is a spanning-tree
contraction of the original graph, with the same single vertex and the same bands. -/
def ofContractEdge (hα : Function.Involutive α) {x : X} (hx : ¬ ρ.SameCycle x (α x))
    (c : SpanningTreeContraction (swap x (α x) * ρ) (swap x (α x) * α)) :
    SpanningTreeContraction ρ α where
  rotation := c.rotation
  matching := c.matching
  involutive_matching := c.involutive_matching
  matching_apply_eq_or y := by
    rcases c.matching_apply_eq_or y with h | h
    · exact Or.inl h
    · rcases hα.swap_mul_apply_eq_self_or x y with ⟨-, hy⟩ | ⟨-, -, hy⟩
      · exact Or.inl (h.trans hy)
      · exact Or.inr (h.trans hy)
  matching_mul_rotation := by
    rw [c.matching_mul_rotation, ← mul_assoc, hα.swap_mul_mul_swap]
  orbitCount_rotation := c.orbitCount_rotation
  orbitCount_matching := by
    have hne : x ≠ α x := fun h ↦ hx (h ▸ SameCycle.refl ρ x)
    have hc := c.orbitCount_matching
    have hα' := orbitCount_swap_mul_of_sameCycle hne (⟨1, rfl⟩ : α.SameCycle x (α x))
    have hρ' := orbitCount_swap_mul_add_one_of_not_sameCycle hx
    omega

/-- Adding an edge to the tree keeps the single vertex. -/
@[simp]
theorem ofContractEdge_rotation (hα : Function.Involutive α) {x : X}
    (hx : ¬ ρ.SameCycle x (α x))
    (c : SpanningTreeContraction (swap x (α x) * ρ) (swap x (α x) * α)) :
    (ofContractEdge hα hx c).rotation = c.rotation :=
  (rfl)

/-- Adding an edge to the tree keeps the bands. -/
@[simp]
theorem ofContractEdge_matching (hα : Function.Involutive α) {x : X}
    (hx : ¬ ρ.SameCycle x (α x))
    (c : SpanningTreeContraction (swap x (α x) * ρ) (swap x (α x) * α)) :
    (ofContractEdge hα hx c).matching = c.matching :=
  (rfl)

end SpanningTreeContraction

/-- A function constant along the vertices and the edges of a connected ribbon graph is
constant. -/
private theorem apply_eq_apply_of_isPretransitive {Y : Type*} {f : X → Y}
    (hconn : IsPretransitive (Subgroup.closure {ρ, α}) X) (hρ : ∀ x, f (ρ x) = f x)
    (hα : ∀ x, f (α x) = f x) (x y : X) : f x = f y := by
  obtain ⟨g, rfl⟩ := hconn.exists_smul_eq x y
  rw [Subgroup.smul_def, Perm.smul_def]
  exact (apply_eq_of_mem_closure (by rintro g (rfl | rfl) <;> assumption) g.2 x).symm

/-- **Contraction preserves connectedness.** Contracting an edge `{x, α x}` whose ends lie at
different vertices of a connected ribbon graph leaves a connected ribbon graph. -/
theorem isPretransitive_closure_swap_mul_swap_mul [DecidableEq X] [Finite X] {x : X}
    (hx : ¬ ρ.SameCycle x (α x)) (hconn : IsPretransitive (Subgroup.closure {ρ, α}) X) :
    IsPretransitive (Subgroup.closure {swap x (α x) * ρ, swap x (α x) * α}) X := by
  set H := Subgroup.closure {swap x (α x) * ρ, swap x (α x) * α}
  have hgen : ∀ g ∈ ({swap x (α x) * ρ, swap x (α x) * α} : Set (Perm X)), g ∈ H :=
    fun g hg ↦ Subgroup.subset_closure hg
  have hmk (g : Perm X) (hg : g ∈ H) (y : X) :
      (Quotient.mk (orbitRel H X) (g y) : orbitRel.Quotient H X) = Quotient.mk _ y :=
    Quotient.sound (mem_orbit_iff.mpr ⟨⟨g, hg⟩, rfl⟩ : g y ∈ orbit H y)
  -- After the contraction, both darts of the contracted edge lie at the merged vertex.
  obtain ⟨k, hk⟩ := sameCycle_swap_mul_of_mem_periodicPts_of_not_sameCycle
    (ρ.injective.mem_periodicPts (α x)) hx
  have hxα : (Quotient.mk (orbitRel H X) (α x) : orbitRel.Quotient H X) = Quotient.mk _ x := by
    rw [← hk]
    exact hmk _ (zpow_mem (hgen _ (Set.mem_insert _ _)) k) x
  have hswap (y : X) : (Quotient.mk (orbitRel H X) (swap x (α x) y) : orbitRel.Quotient H X) =
      Quotient.mk _ y := by
    rcases eq_or_ne y x with rfl | hyx
    · rw [swap_apply_left, hxα]
    rcases eq_or_ne y (α x) with rfl | hyα
    · rw [swap_apply_right, hxα]
    · rw [swap_apply_of_ne_of_ne hyx hyα]
  -- Both generators of the original group move every dart within its orbit after contraction,
  -- since `ρ` and `α` are recovered from the new generators by applying the transposition.
  have hstep (g : Perm X) (hg : g ∈ ({swap x (α x) * ρ, swap x (α x) * α} : Set (Perm X)))
      (y : X) : (Quotient.mk (orbitRel H X) (swap x (α x) (g y)) : orbitRel.Quotient H X) =
        Quotient.mk _ y :=
    (hswap (g y)).trans (hmk g (hgen g hg) y)
  refine ⟨fun y z ↦ ?_⟩
  have hyz := apply_eq_apply_of_isPretransitive (f := Quotient.mk (orbitRel H X)) hconn
    (fun y ↦ by simpa using hstep _ (Set.mem_insert _ _) y)
    (fun y ↦ by simpa using hstep _ (Set.mem_insert_of_mem _ rfl) y) z y
  obtain ⟨g, hg⟩ := Quotient.exact hyz
  exact ⟨g, hg⟩

/-- In a connected ribbon graph with more than one vertex, some edge joins two different
vertices. -/
private theorem exists_not_sameCycle_apply [Nonempty X]
    (hconn : IsPretransitive (Subgroup.closure {ρ, α}) X) (hρ : orbitCount ρ ≠ 1) :
    ∃ x, ¬ ρ.SameCycle x (α x) := by
  by_contra! h
  refine hρ (orbitCount_eq_one_of_forall_sameCycle fun x y ↦ Quotient.exact
    (apply_eq_apply_of_isPretransitive (f := Quotient.mk (SameCycle.setoid ρ)) hconn
      (fun z ↦ Quotient.sound ⟨-1, by simp⟩) (fun z ↦ (Quotient.sound (h z)).symm) x y))

/-- **Spanning trees exist.** Every connected ribbon graph on a nonempty finite set of darts has
a spanning-tree contraction: contract edges between distinct vertices, one at a time, until a
single vertex is left. -/
theorem nonempty_spanningTreeContraction [Finite X] [Nonempty X] (hα : Function.Involutive α)
    (hconn : IsPretransitive (Subgroup.closure {ρ, α}) X) :
    Nonempty (SpanningTreeContraction ρ α) := by
  classical
  induction hk : orbitCount ρ using Nat.strong_induction_on generalizing ρ α with
  | _ k ih =>
  by_cases hρ : orbitCount ρ = 1
  · exact ⟨.ofOrbitCountEqOne hα hρ⟩
  obtain ⟨x, hx⟩ := exists_not_sameCycle_apply hconn hρ
  have hcount := orbitCount_swap_mul_add_one_of_not_sameCycle hx
  obtain ⟨c⟩ := ih _ (by omega) (hα.swap_mul x)
    (isPretransitive_closure_swap_mul_swap_mul hx hconn) rfl
  exact ⟨.ofContractEdge hα hx c⟩

namespace SpanningTreeContraction

/-- **The noninterleaving criterion for a spanning-tree contraction.** Number the darts so that
the single vertex left by the contraction is cyclic rotation, as
`TauCeti.exists_equiv_permCongr_eq_finRotate` allows. The bands of the contraction then
do not interleave exactly when the ribbon graph satisfies Euler's equality `V - E + F = 2`, that
is, when it is a sphere. -/
theorem isNoncrossingMatching_permCongr_matching_iff (c : SpanningTreeContraction ρ α) {n : ℕ}
    (e : X ≃ Fin n) (he : e.permCongr c.rotation = finRotate n) :
    (e.permCongr c.matching).IsNoncrossingMatching ↔
      orbitCount (α * ρ) + orbitCount ρ + orbitCount α = n + 2 := by
  have : NeZero n := ⟨fun hn ↦ by
    subst hn
    have h := c.orbitCount_rotation
    rw [← orbitCount_permCongr e, he, orbitCount_finRotate] at h
    simp at h⟩
  have hinv : Function.Involutive (e.permCongr c.matching) := fun y ↦ by
    simp [c.involutive_matching _]
  have hm := c.orbitCount_matching
  rw [← hinv.orbitCount_finRotate_mul_add_orbitCount_eq_iff, ← he, ← permCongr_mul,
    orbitCount_permCongr, orbitCount_permCongr, orbitCount_mul_comm, c.matching_mul_rotation]
  omega

end SpanningTreeContraction

end TauCeti
