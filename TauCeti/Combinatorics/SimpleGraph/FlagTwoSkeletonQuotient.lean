/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Finite quotients of the two-skeleton of the flag complex of a simple graph

The *flag complex* of a simple graph `Γ` is the simplicial complex whose simplices are the finite
cliques of `Γ`; its two-skeleton consists of the vertices, edges and triangles of `Γ`. For `G`
with a scalar action on the vertices, `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient` asks for a
finite set of vertices containing a `G`-translate of every vertex, of every edge and of every
triangle of `Γ`. When `G` is a group acting on `Γ` by automorphisms, this says that the quotient
of the two-skeleton of the flag complex by `G` is finite.

## Main definitions

* `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient`: a finite set of vertices contains a translate
  of every vertex, edge and triangle.

## Main results

* `SimpleGraph.hasFiniteFlagTwoSkeletonQuotient_iff_adj`: the same condition, with edges and
  triangles given by adjacency.
* `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient.of_finite`: it holds on finitely many vertices,
  for the scalar action of any nonempty type.
* `SimpleGraph.hasFiniteFlagTwoSkeletonQuotient_iff_of_finite_neighborSet`: for a locally finite
  graph on which `G` acts by graph homomorphisms, it holds exactly when a finite set of vertices
  contains a translate of every vertex.
* `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient.finite_neighborSet`: for a left-cancellative scalar
  action, it forces every vertex whose orbit map has finite fibres to have finitely many
  neighbours.
* `SimpleGraph.not_hasFiniteFlagTwoSkeletonQuotient_top`: it fails for the complete graph on an
  infinite set with a cancellative scalar action, for instance a free action of a group.

## References

* M. J. Dunwoody, *The accessibility of finitely presented groups*, Invent. Math. 81 (1985),
  449–457, §1 (almost finitely presented groups).
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017),
  Proposition 2.24 and its proof.
-/

public section

namespace SimpleGraph

variable {V : Type*} (Γ : SimpleGraph V) (G : Type*) [SMul G V]

/-- There is a finite set `A` of vertices such that every vertex, every edge and every triangle
of `Γ` has a `G`-translate all of whose vertices lie in `A`. For a group `G` acting on `Γ` by
graph automorphisms, this says that the quotient by `G` of the two-skeleton of the flag complex of
`Γ` is finite. -/
def HasFiniteFlagTwoSkeletonQuotient : Prop :=
  ∃ A : Set V, A.Finite ∧ ∀ a b c : V, Γ.IsClique {a, b, c} →
    ∃ g : G, g • a ∈ A ∧ g • b ∈ A ∧ g • c ∈ A

variable {Γ G}

/-- Unfolding `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient`: a finite set of vertices contains
a translate of every vertex, edge and triangle. -/
theorem hasFiniteFlagTwoSkeletonQuotient_iff : Γ.HasFiniteFlagTwoSkeletonQuotient G ↔
    ∃ A : Set V, A.Finite ∧ ∀ a b c : V, Γ.IsClique {a, b, c} →
      ∃ g : G, g • a ∈ A ∧ g • b ∈ A ∧ g • c ∈ A := Iff.rfl

/-- `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient` with edges and triangles given by adjacency:
a finite set of vertices contains a translate of every vertex, of the two ends of every edge and
of the three vertices of every triangle. -/
theorem hasFiniteFlagTwoSkeletonQuotient_iff_adj : Γ.HasFiniteFlagTwoSkeletonQuotient G ↔
    ∃ A : Set V, A.Finite ∧ (∀ a, ∃ g : G, g • a ∈ A) ∧
      (∀ a b, Γ.Adj a b → ∃ g : G, g • a ∈ A ∧ g • b ∈ A) ∧
      ∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj a c → ∃ g : G, g • a ∈ A ∧ g • b ∈ A ∧ g • c ∈ A := by
  refine exists_congr fun A ↦ and_congr_right fun _ ↦ ⟨fun h ↦ ⟨fun a ↦ ?_, fun a b hab ↦ ?_,
    fun a b c hab hbc hac ↦ h a b c ?_⟩, fun ⟨h₁, h₂, h₃⟩ a b c habc ↦ ?_⟩
  · exact (h a a a (by simp)).imp fun _ ↦ And.left
  · exact (h a b b (by simp [hab])).imp fun _ ↦ And.imp_right And.left
  · simp [isClique_insert, hab, hbc, hac]
  · simp only [isClique_insert, isClique_singleton, Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, forall_eq, true_and] at habc
    obtain ⟨hbc', hab', hac'⟩ := habc
    rcases eq_or_ne b c with rfl | hbc
    · rcases eq_or_ne a b with rfl | hab
      · exact (h₁ a).imp fun _ h ↦ ⟨h, h, h⟩
      · exact (h₂ a b (hab' hab)).imp fun _ h ↦ ⟨h.1, h.2, h.2⟩
    rcases eq_or_ne a b with rfl | hab
    · exact (h₂ a c (hac' hbc)).imp fun _ h ↦ ⟨h.1, h.1, h.2⟩
    rcases eq_or_ne a c with rfl | hac
    · exact (h₂ a b (hab' hab)).imp fun _ h ↦ ⟨h.1, h.2, h.1⟩
    · exact h₃ a b c (hab' hab) (hbc' hbc) (hac' hac)

/-- On a finite vertex type, `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient` holds for the scalar
action of any nonempty type. -/
@[simp]
theorem HasFiniteFlagTwoSkeletonQuotient.of_finite [Nonempty G] [Finite V] :
    Γ.HasFiniteFlagTwoSkeletonQuotient G :=
  ⟨Set.univ, Set.finite_univ, fun _ _ _ _ ↦ ⟨Classical.arbitrary G, by simp⟩⟩

/-- On the empty vertex type, `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient` holds for every
scalar action. -/
@[simp]
theorem HasFiniteFlagTwoSkeletonQuotient.of_isEmpty [IsEmpty V] :
    Γ.HasFiniteFlagTwoSkeletonQuotient G :=
  ⟨∅, Set.finite_empty, fun a ↦ isEmptyElim a⟩

/-- If `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient` holds, then some finite set of vertices
contains a `G`-translate of every vertex. -/
theorem HasFiniteFlagTwoSkeletonQuotient.exists_finite_forall_exists_smul_mem
    (h : Γ.HasFiniteFlagTwoSkeletonQuotient G) :
    ∃ A : Set V, A.Finite ∧ ∀ a : V, ∃ g : G, g • a ∈ A :=
  h.imp fun _ ↦ And.imp_right fun hA a ↦ (hA a a a (by simp)).imp fun _ ↦ And.left

/-- `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient` passes from a graph to its subgraphs. -/
@[gcongr]
theorem HasFiniteFlagTwoSkeletonQuotient.anti {Γ₁ Γ₂ : SimpleGraph V} (hle : Γ₁ ≤ Γ₂)
    (h : Γ₂.HasFiniteFlagTwoSkeletonQuotient G) : Γ₁.HasFiniteFlagTwoSkeletonQuotient G :=
  h.imp fun _ ↦ And.imp_right fun hA a b c habc ↦ hA a b c (habc.mono hle)

/-- For a locally finite graph on whose vertices every element of `G` acts by a graph
homomorphism, some finite set of vertices contains a `G`-translate of every vertex, edge and
triangle exactly when some finite set of vertices contains a `G`-translate of every vertex. -/
theorem hasFiniteFlagTwoSkeletonQuotient_iff_of_finite_neighborSet
    (hfin : ∀ a, (Γ.neighborSet a).Finite)
    (hΓ : ∀ (g : G) (a b : V), Γ.Adj a b → Γ.Adj (g • a) (g • b)) :
    Γ.HasFiniteFlagTwoSkeletonQuotient G ↔ ∃ A : Set V, A.Finite ∧ ∀ a : V, ∃ g : G, g • a ∈ A := by
  refine ⟨HasFiniteFlagTwoSkeletonQuotient.exists_finite_forall_exists_smul_mem,
    fun ⟨A, hA, h⟩ ↦ ⟨A ∪ ⋃ a ∈ A, Γ.neighborSet a, hA.union (hA.biUnion fun a _ ↦ hfin a),
      fun a b c habc ↦ ?_⟩⟩
  obtain ⟨g, hg⟩ := h a
  -- every vertex of the clique is `a` or a neighbour of `a`, so its translate lies near `A`
  have key : ∀ x ∈ ({a, b, c} : Set V), g • x ∈ A ∪ ⋃ a ∈ A, Γ.neighborSet a := fun x hx ↦ by
    rcases eq_or_ne a x with rfl | hne
    · exact Or.inl hg
    · exact Or.inr (Set.mem_biUnion hg (hΓ g a x (habc (by simp) hx hne)))
  exact ⟨g, key a (by simp), key b (by simp), key c (by simp)⟩

/-- For a graph without edges, `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient` holds exactly
when a finite set of vertices contains a `G`-translate of every vertex. -/
theorem hasFiniteFlagTwoSkeletonQuotient_bot_iff :
    (⊥ : SimpleGraph V).HasFiniteFlagTwoSkeletonQuotient G ↔
      ∃ A : Set V, A.Finite ∧ ∀ a : V, ∃ g : G, g • a ∈ A :=
  hasFiniteFlagTwoSkeletonQuotient_iff_of_finite_neighborSet (by simp) fun _ _ _ h ↦ h.elim

/-- If `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient` holds for a left-cancellative scalar action,
then a vertex `a₀` for which every fibre of the orbit map `g ↦ g • a₀` is finite has finitely many
neighbours. -/
theorem HasFiniteFlagTwoSkeletonQuotient.finite_neighborSet [IsLeftCancelSMul G V]
    (h : Γ.HasFiniteFlagTwoSkeletonQuotient G) {a₀ : V}
    (ha₀ : ∀ y : V, ((· • a₀ : G → V) ⁻¹' {y}).Finite) : (Γ.neighborSet a₀).Finite := by
  obtain ⟨A, hA, h⟩ := h
  -- an edge `{a₀, b}` is moved into `A` by some `g` with `g • a₀ ∈ A`; then `g • b ∈ A`
  refine ((hA.preimage' fun y _ ↦ ha₀ y).biUnion fun g _ ↦ hA.preimage
    (Set.injOn_of_injective fun _ _ ↦ IsLeftCancelSMul.left_cancel g _ _)).subset fun b hb ↦ ?_
  obtain ⟨g, hg₀, hgb, -⟩ := h a₀ b b (by simp [(mem_neighborSet ..).1 hb])
  exact Set.mem_biUnion hg₀ hgb

/-- If `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient` holds for a cancellative scalar action, such
as a free action of a group, then every vertex has finitely many neighbours. -/
theorem HasFiniteFlagTwoSkeletonQuotient.finite_neighborSet_of_isCancelSMul [IsCancelSMul G V]
    (h : Γ.HasFiniteFlagTwoSkeletonQuotient G) (a : V) : (Γ.neighborSet a).Finite :=
  h.finite_neighborSet fun _ ↦ Set.Subsingleton.finite fun _ hg _ hg' ↦
    IsCancelSMul.right_cancel _ _ _ (hg.trans hg'.symm)

/-- `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient` fails for the complete graph on an infinite
vertex type with a left-cancellative scalar action of `G` for which every fibre of `g ↦ g • a₀` is
finite for some vertex `a₀`. -/
theorem not_hasFiniteFlagTwoSkeletonQuotient_top_of_finite_preimage_singleton
    [IsLeftCancelSMul G V] [Infinite V] {a₀ : V}
    (ha₀ : ∀ y : V, ((· • a₀ : G → V) ⁻¹' {y}).Finite) :
    ¬(⊤ : SimpleGraph V).HasFiniteFlagTwoSkeletonQuotient G := fun h ↦
  (Set.finite_singleton a₀).infinite_compl <| by simpa using h.finite_neighborSet ha₀

/-- `SimpleGraph.HasFiniteFlagTwoSkeletonQuotient` fails for the complete graph on an infinite
vertex type with a cancellative scalar action of `G`, for instance a free action of a group. -/
theorem not_hasFiniteFlagTwoSkeletonQuotient_top [IsCancelSMul G V] [Infinite V] :
    ¬(⊤ : SimpleGraph V).HasFiniteFlagTwoSkeletonQuotient G := fun h ↦
  (Set.finite_singleton (Classical.arbitrary V)).infinite_compl <| by
    simpa using h.finite_neighborSet_of_isCancelSMul (Classical.arbitrary V)

end SimpleGraph
