/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.ZMod.Defs

/-!
# The first cohomology modulo two of the flag complex of a simple graph

The *flag complex* of a simple graph `Γ` is the simplicial complex whose simplices are the finite
cliques of `Γ`. Its two-skeleton has the vertices of `Γ` as vertices, the edges of `Γ` as edges
and the triangles of `Γ` as two-simplices, so its first cohomology is determined by `Γ`.

A one-cochain modulo two is a symmetric function on adjacent pairs with values in `ZMod 2`; it is
a cocycle when its values on the three sides of every triangle add up to zero, and a coboundary
when it is `(a, b) ↦ c a + c b` for a function `c` on the vertices. The first cohomology of the
flag complex with coefficients in `ZMod 2` vanishes when every cocycle is a coboundary. For a
connected complex this is the hypothesis under which every track separates it (Dunwoody). Unlike
`SimpleGraph.FirstCohomology`, which treats a graph as a one-dimensional complex, the triangles
of `Γ` are two-cells here.

## Main definitions

* `SimpleGraph.HasTrivialFlagFirstCohomologyModTwo`: every cocycle modulo two of the flag complex
  is a coboundary.

## Main results

* `SimpleGraph.IsUniversal.hasTrivialFlagFirstCohomologyModTwo`: a graph with a vertex adjacent
  to every other vertex (a cone) has trivial first cohomology modulo two.
* `SimpleGraph.hasTrivialFlagFirstCohomologyModTwo_top`: so has a complete graph.
* `SimpleGraph.Iso.hasTrivialFlagFirstCohomologyModTwo_iff`: the property is invariant under
  graph isomorphisms.
* `SimpleGraph.not_hasTrivialFlagFirstCohomologyModTwo_cycleGraph_four`: the four-cycle has
  nontrivial first cohomology modulo two.

## References

* M. J. Dunwoody, *The accessibility of finitely presented groups*, Invent. Math. 81 (1985),
  449–457, §1 (almost finitely presented groups) and §2 (the cocycle of a track).
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017),
  Proposition 2.24 and its proof.
-/

public section

namespace SimpleGraph

variable {V W : Type*} (Γ : SimpleGraph V) {Γ' : SimpleGraph W}

/-- The first cohomology of the flag complex of a simple graph with coefficients in `ZMod 2` is
trivial: every symmetric function `z` on adjacent pairs whose values on the three sides of each
triangle add up to zero is of the form `z a b = c a + c b` for a function `c` on the vertices. -/
def HasTrivialFlagFirstCohomologyModTwo : Prop :=
  ∀ z : V → V → ZMod 2, (∀ a b, Γ.Adj a b → z a b = z b a) →
    (∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj a c → z a b + z b c + z a c = 0) →
    ∃ c : V → ZMod 2, ∀ a b, Γ.Adj a b → z a b = c a + c b

variable {Γ}

/-- Unfolding `SimpleGraph.HasTrivialFlagFirstCohomologyModTwo`: every cocycle modulo two is a
coboundary. -/
theorem hasTrivialFlagFirstCohomologyModTwo_iff : Γ.HasTrivialFlagFirstCohomologyModTwo ↔
    ∀ z : V → V → ZMod 2, (∀ a b, Γ.Adj a b → z a b = z b a) →
      (∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj a c → z a b + z b c + z a c = 0) →
      ∃ c : V → ZMod 2, ∀ a b, Γ.Adj a b → z a b = c a + c b := Iff.rfl

/-- If the first cohomology modulo two of the flag complex is trivial, then every cocycle modulo
two is a coboundary. -/
theorem HasTrivialFlagFirstCohomologyModTwo.exists_eq_add
    (h : Γ.HasTrivialFlagFirstCohomologyModTwo) {z : V → V → ZMod 2}
    (hsymm : ∀ a b, Γ.Adj a b → z a b = z b a)
    (hcoc : ∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj a c → z a b + z b c + z a c = 0) :
    ∃ c : V → ZMod 2, ∀ a b, Γ.Adj a b → z a b = c a + c b :=
  h z hsymm hcoc

/-- A graph with a vertex adjacent to every other vertex has trivial first cohomology modulo two
of its flag complex. -/
theorem IsUniversal.hasTrivialFlagFirstCohomologyModTwo {a₀ : V} (h₀ : Γ.IsUniversal a₀) :
    Γ.HasTrivialFlagFirstCohomologyModTwo := by
  classical
  intro z hsymm hcoc
  -- `a₀` gets the value `0`, and any other `a` the value of `z` on the edge `{a₀, a}`
  refine ⟨fun a ↦ if a = a₀ then 0 else z a₀ a, fun a b hab ↦ ?_⟩
  have key : ∀ x y w : ZMod 2, x + y + w = 0 → y = x + w := by decide
  by_cases ha : a = a₀
  · subst ha
    simp [hab.ne']
  by_cases hb : b = a₀
  · subst hb
    simp [ha, hsymm _ _ hab]
  · simpa [ha, hb] using key _ _ _ (hcoc a₀ a b (h₀ (Ne.symm ha)) hab (h₀ (Ne.symm hb)))

/-- A graph without edges has trivial first cohomology modulo two of its flag complex. -/
@[simp]
theorem hasTrivialFlagFirstCohomologyModTwo_bot :
    (⊥ : SimpleGraph V).HasTrivialFlagFirstCohomologyModTwo :=
  fun _ _ _ ↦ ⟨0, fun _ _ hab ↦ hab.elim⟩

/-- A graph on at most one vertex has trivial first cohomology modulo two of its flag
complex. -/
@[simp]
theorem HasTrivialFlagFirstCohomologyModTwo.of_subsingleton [Subsingleton V] :
    Γ.HasTrivialFlagFirstCohomologyModTwo :=
  Subsingleton.elim (⊥ : SimpleGraph V) Γ ▸ hasTrivialFlagFirstCohomologyModTwo_bot

/-- A complete graph has trivial first cohomology modulo two of its flag complex. -/
@[simp]
theorem hasTrivialFlagFirstCohomologyModTwo_top :
    (⊤ : SimpleGraph V).HasTrivialFlagFirstCohomologyModTwo := by
  rcases isEmpty_or_nonempty V with _ | ⟨⟨a₀⟩⟩
  · exact .of_subsingleton
  · exact (IsUniversal.top (v := a₀)).hasTrivialFlagFirstCohomologyModTwo

/-- Trivial first cohomology modulo two of the flag complex is transported along a graph
isomorphism. -/
theorem HasTrivialFlagFirstCohomologyModTwo.of_iso (h : Γ.HasTrivialFlagFirstCohomologyModTwo)
    (e : Γ ≃g Γ') : Γ'.HasTrivialFlagFirstCohomologyModTwo := by
  intro z hsymm hcoc
  obtain ⟨c, hc⟩ := h (fun a b ↦ z (e a) (e b)) (fun a b hab ↦ hsymm _ _ (e.map_adj_iff.2 hab))
    fun a b c hab hbc hac ↦
      hcoc _ _ _ (e.map_adj_iff.2 hab) (e.map_adj_iff.2 hbc) (e.map_adj_iff.2 hac)
  refine ⟨c ∘ e.symm, fun a b hab ↦ ?_⟩
  simpa using hc (e.symm a) (e.symm b) (e.symm.map_adj_iff.2 hab)

/-- Isomorphic graphs have trivial first cohomology modulo two of their flag complexes
simultaneously. -/
theorem Iso.hasTrivialFlagFirstCohomologyModTwo_iff (e : Γ ≃g Γ') :
    Γ.HasTrivialFlagFirstCohomologyModTwo ↔ Γ'.HasTrivialFlagFirstCohomologyModTwo :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- The four-cycle has nontrivial first cohomology modulo two of its flag complex. -/
@[simp]
theorem not_hasTrivialFlagFirstCohomologyModTwo_cycleGraph_four :
    ¬(cycleGraph 4).HasTrivialFlagFirstCohomologyModTwo := by
  intro h
  -- the cochain supported on the edge `{0, 1}` is a cocycle, the four-cycle having no triangle
  obtain ⟨c, hc⟩ := h (fun a b ↦ if a.val + b.val = 1 then 1 else 0)
    (fun _ _ _ ↦ by rw [add_comm]) (by decide)
  -- its sum around the four-cycle is `1`, while that of a coboundary is `0`
  have h01 := hc 0 1 (by decide)
  have h12 := hc 1 2 (by decide)
  have h23 := hc 2 3 (by decide)
  have h30 := hc 3 0 (by decide)
  revert h01 h12 h23 h30
  generalize c 0 = x₀, c 1 = x₁, c 2 = x₂, c 3 = x₃
  revert x₀ x₁ x₂ x₃
  decide

end SimpleGraph
