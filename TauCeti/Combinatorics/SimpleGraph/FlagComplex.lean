/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.ZMod.Defs

/-!
# The flag complex of a simple graph: cocycles modulo two and cocompact actions

The *flag complex* of a simple graph `Γ` is the simplicial complex whose simplices are the finite
cliques of `Γ`. Its two-skeleton has the vertices of `Γ` as vertices, the edges of `Γ` as edges
and the triangles of `Γ` as two-simplices; it is determined by `Γ`, so statements about
two-dimensional simplicial complexes can be made about simple graphs. Every two-dimensional
simplicial complex has a subdivision of this form.

A one-cochain modulo two is a symmetric function on adjacent pairs with values in `ZMod 2`; it is
a cocycle when its values on the three sides of every triangle add up to zero, and a coboundary
when it is `(a, b) ↦ c a + c b` for a function `c` on the vertices. The graph `Γ` is *flag
acyclic modulo two* (`SimpleGraph.IsFlagAcyclicModTwo`) when every cocycle is a coboundary: the
first cohomology of the flag complex with coefficients in `ZMod 2` vanishes. For a connected
complex this is the hypothesis under which every track separates it (Dunwoody). Unlike
`SimpleGraph.FirstCohomology`, which treats a graph as a one-dimensional complex, the triangles
of `Γ` are two-cells here.

An action of a group on the vertices *has finitely many orbits of flags*
(`SimpleGraph.HasFiniteFlagQuotient`) when finitely many vertices carry a translate of every
vertex, edge and triangle. For an action by automorphisms of `Γ` this says that the quotient of
the two-skeleton of the flag complex is finite.

## Main definitions

* `SimpleGraph.IsFlagAcyclicModTwo`: every cocycle modulo two of the flag complex is a
  coboundary.
* `SimpleGraph.HasFiniteFlagQuotient`: finitely many orbits of vertices, edges and triangles.

## Main results

* `SimpleGraph.isFlagAcyclicModTwo_top`: a complete graph is flag acyclic modulo two.
* `SimpleGraph.not_isFlagAcyclicModTwo_cycleGraph_four`: the square is not.
* `SimpleGraph.HasFiniteFlagQuotient.of_finite`: a graph on finitely many vertices has finitely
  many orbits of flags under every action of a nonempty type.

## References

* M. J. Dunwoody, *The accessibility of finitely presented groups*, Invent. Math. 81 (1985),
  449–457, §1 (almost finitely presented groups) and §2 (the cocycle of a track).
-/

public section

namespace SimpleGraph

variable {V : Type*} (Γ : SimpleGraph V)

/-- A simple graph is *flag acyclic modulo two* when the first cohomology of its flag complex
with coefficients in `ZMod 2` vanishes: every symmetric function `z` on adjacent pairs whose
values on the three sides of each triangle add up to zero is of the form `z a b = c a + c b` for
a function `c` on the vertices. -/
def IsFlagAcyclicModTwo : Prop :=
  ∀ z : V → V → ZMod 2, (∀ a b, Γ.Adj a b → z a b = z b a) →
    (∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj a c → z a b + z b c + z a c = 0) →
    ∃ c : V → ZMod 2, ∀ a b, Γ.Adj a b → z a b = c a + c b

/-- Unfolding `SimpleGraph.IsFlagAcyclicModTwo`: every cocycle modulo two is a coboundary. -/
theorem isFlagAcyclicModTwo_iff : Γ.IsFlagAcyclicModTwo ↔
    ∀ z : V → V → ZMod 2, (∀ a b, Γ.Adj a b → z a b = z b a) →
      (∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj a c → z a b + z b c + z a c = 0) →
      ∃ c : V → ZMod 2, ∀ a b, Γ.Adj a b → z a b = c a + c b := Iff.rfl

/-- A complete graph is flag acyclic modulo two: its flag complex is a simplex. -/
theorem isFlagAcyclicModTwo_top : (⊤ : SimpleGraph V).IsFlagAcyclicModTwo := by
  intro z hsymm hcoc
  simp only [top_adj] at hsymm hcoc ⊢
  rcases isEmpty_or_nonempty V with _ | ⟨⟨a₀⟩⟩
  · exact ⟨0, isEmptyElim⟩
  classical
  -- `a₀` is a cone point: it gets the value `0`, and any other `a` the value of `z` on `{a₀, a}`
  refine ⟨fun a ↦ if a = a₀ then 0 else z a₀ a, fun a b hab ↦ ?_⟩
  have key : ∀ x y w : ZMod 2, x + y + w = 0 → y = x + w := by decide
  by_cases ha : a = a₀
  · subst ha
    simp [hab.symm]
  by_cases hb : b = a₀
  · subst hb
    simp [ha, hsymm _ _ hab]
  · simpa [ha, hb] using key _ _ _ (hcoc a₀ a b (Ne.symm ha) hab (Ne.symm hb))

/-- The square is not flag acyclic modulo two: it has no triangle, so the cochain supported on
one edge is a cocycle, and it is not a coboundary. -/
theorem not_isFlagAcyclicModTwo_cycleGraph_four : ¬(cycleGraph 4).IsFlagAcyclicModTwo := by
  intro h
  -- the cochain supported on the edge `{0, 1}` is a cocycle, the square having no triangle
  obtain ⟨c, hc⟩ := h (fun a b ↦ if a.val + b.val = 1 then 1 else 0)
    (fun _ _ _ ↦ by rw [add_comm]) (by decide)
  -- its sum around the square is `1`, while that of a coboundary is `0`
  have h01 := hc 0 1 (by decide)
  have h12 := hc 1 2 (by decide)
  have h23 := hc 2 3 (by decide)
  have h30 := hc 3 0 (by decide)
  revert h01 h12 h23 h30
  generalize c 0 = x₀, c 1 = x₁, c 2 = x₂, c 3 = x₃
  revert x₀ x₁ x₂ x₃
  decide

/-- An action of `G` on the vertices of `Γ` *has finitely many orbits of flags* when there is a
finite set `A` of vertices such that every vertex, every edge and every triangle of `Γ` has a
translate all of whose vertices lie in `A`. -/
def HasFiniteFlagQuotient (G : Type*) [SMul G V] : Prop :=
  ∃ A : Set V, A.Finite ∧ ∀ a b c : V, Γ.IsClique {a, b, c} →
    ∃ g : G, g • a ∈ A ∧ g • b ∈ A ∧ g • c ∈ A

/-- Unfolding `SimpleGraph.HasFiniteFlagQuotient`: a finite set of vertices contains a translate
of every vertex, edge and triangle. -/
theorem hasFiniteFlagQuotient_iff {G : Type*} [SMul G V] : Γ.HasFiniteFlagQuotient G ↔
    ∃ A : Set V, A.Finite ∧ ∀ a b c : V, Γ.IsClique {a, b, c} →
      ∃ g : G, g • a ∈ A ∧ g • b ∈ A ∧ g • c ∈ A := Iff.rfl

/-- A graph on finitely many vertices has finitely many orbits of flags under every action of a
nonempty type. -/
theorem HasFiniteFlagQuotient.of_finite (G : Type*) [SMul G V] [Nonempty G] [Finite V] :
    Γ.HasFiniteFlagQuotient G :=
  ⟨Set.univ, Set.finite_univ, fun _ _ _ _ ↦ ⟨Classical.arbitrary G, by simp⟩⟩

/-- Finitely many orbits of flags give finitely many orbits of vertices: finitely many vertices
meet every orbit. -/
theorem HasFiniteFlagQuotient.exists_finite_forall_smul_mem {G : Type*} [SMul G V]
    (h : Γ.HasFiniteFlagQuotient G) : ∃ A : Set V, A.Finite ∧ ∀ a : V, ∃ g : G, g • a ∈ A :=
  h.imp fun _ ↦ And.imp_right fun hA a ↦ (hA a a a (by simp)).imp fun _ ↦ And.left

end SimpleGraph
