/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Data.ZMod.Defs

/-!
# The first cohomology of the flag complex of a simple graph

The *flag complex* of a simple graph `Γ` is the simplicial complex whose simplices are the finite
cliques of `Γ`. Its two-skeleton has the vertices of `Γ` as vertices, the edges of `Γ` as edges
and the triangles of `Γ` as two-simplices, so its first cohomology is determined by `Γ`.

With coefficients in an additive commutative group `A`, a one-cochain is a function `z` on
adjacent pairs with `z b a = -z a b`; it is a cocycle when `z a b + z b c = z a c` for every
triangle, and a coboundary when it is `(a, b) ↦ c b - c a` for a function `c` on the vertices.
The first cohomology of the flag complex with coefficients in `A` vanishes when every cocycle is a
coboundary. With coefficients in `ZMod 2` the signs disappear: a cochain is a symmetric function
on adjacent pairs, it is a cocycle when its values on the three sides of every triangle add up to
zero, and a coboundary is `(a, b) ↦ c a + c b`. For a connected complex, vanishing of the first
cohomology with coefficients in `ZMod 2` is the hypothesis under which every track separates it
(Dunwoody). Unlike `SimpleGraph.FirstCohomology`, which treats a graph as a one-dimensional
complex, the triangles of `Γ` are two-cells here.

## Main definitions

* `SimpleGraph.HasTrivialFlagFirstCohomology`: every cocycle of the flag complex with coefficients
  in `A` is a coboundary.

## Main results

* `SimpleGraph.hasTrivialFlagFirstCohomology_zmod_two_iff`: with coefficients in `ZMod 2`, the
  condition in terms of symmetric functions on adjacent pairs.
* `SimpleGraph.IsUniversal.hasTrivialFlagFirstCohomology`: a graph with a vertex adjacent to every
  other vertex (a cone) has trivial first cohomology.
* `SimpleGraph.hasTrivialFlagFirstCohomology_top`: so has a complete graph.
* `SimpleGraph.Iso.hasTrivialFlagFirstCohomology_iff`: the property is invariant under graph
  isomorphisms.
* `SimpleGraph.hasTrivialFlagFirstCohomology_cycleGraph_iff`: with nontrivial coefficients, the
  cycle graph on `n` vertices has trivial first cohomology exactly when `n ≤ 3`.

## References

* M. J. Dunwoody, *The accessibility of finitely presented groups*, Invent. Math. 81 (1985),
  449–457, §1 (almost finitely presented groups) and §2 (the cocycle of a track).
* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017),
  Proposition 2.24 and its proof.
-/

public section

namespace SimpleGraph

variable {V W : Type*} (Γ : SimpleGraph V) {Γ' : SimpleGraph W} (A : Type*) [AddCommGroup A]

/-- The first cohomology of the flag complex of a simple graph with coefficients in `A` is
trivial: every function `z` on adjacent pairs with `z b a = -z a b`, and with
`z a b + z b c = z a c` for each triangle, is of the form `z a b = c b - c a` for a function `c`
on the vertices. -/
def HasTrivialFlagFirstCohomology : Prop :=
  ∀ z : V → V → A, (∀ a b, Γ.Adj a b → z b a = -z a b) →
    (∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj a c → z a b + z b c = z a c) →
    ∃ c : V → A, ∀ a b, Γ.Adj a b → z a b = c b - c a

variable {Γ A}

/-- Unfolding `SimpleGraph.HasTrivialFlagFirstCohomology`: every cocycle is a coboundary. -/
theorem hasTrivialFlagFirstCohomology_iff : Γ.HasTrivialFlagFirstCohomology A ↔
    ∀ z : V → V → A, (∀ a b, Γ.Adj a b → z b a = -z a b) →
      (∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj a c → z a b + z b c = z a c) →
      ∃ c : V → A, ∀ a b, Γ.Adj a b → z a b = c b - c a := Iff.rfl

/-- If the first cohomology of the flag complex with coefficients in `A` is trivial, then every
cocycle is a coboundary. -/
theorem HasTrivialFlagFirstCohomology.exists_eq_sub (h : Γ.HasTrivialFlagFirstCohomology A)
    {z : V → V → A} (hanti : ∀ a b, Γ.Adj a b → z b a = -z a b)
    (hcoc : ∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj a c → z a b + z b c = z a c) :
    ∃ c : V → A, ∀ a b, Γ.Adj a b → z a b = c b - c a :=
  h z hanti hcoc

/-- The first cohomology of the flag complex with coefficients in `ZMod 2` is trivial exactly when
every symmetric function on adjacent pairs whose values on the three sides of each triangle add up
to zero is of the form `(a, b) ↦ c a + c b` for a function `c` on the vertices. -/
theorem hasTrivialFlagFirstCohomology_zmod_two_iff :
    Γ.HasTrivialFlagFirstCohomology (ZMod 2) ↔
    ∀ z : V → V → ZMod 2, (∀ a b, Γ.Adj a b → z b a = z a b) →
      (∀ a b c, Γ.Adj a b → Γ.Adj b c → Γ.Adj a c → z a b + z b c + z a c = 0) →
      ∃ c : V → ZMod 2, ∀ a b, Γ.Adj a b → z a b = c a + c b := by
  have hneg (x : ZMod 2) : -x = x := by revert x; decide
  have hsub (x y : ZMod 2) : x - y = y + x := by revert x y; decide
  have hcoc (x y w : ZMod 2) : x + y + w = 0 ↔ x + y = w := by revert x y w; decide
  simp only [hasTrivialFlagFirstCohomology_iff, hneg, hsub, hcoc]

/-- A graph with a vertex adjacent to every other vertex has trivial first cohomology of its flag
complex. -/
theorem IsUniversal.hasTrivialFlagFirstCohomology {a₀ : V} (h₀ : Γ.IsUniversal a₀) :
    Γ.HasTrivialFlagFirstCohomology A := by
  classical
  intro z hanti hcoc
  -- `a₀` gets the value `0`, and any other `a` the value of `z` on the edge `(a₀, a)`
  refine ⟨fun a ↦ if a = a₀ then 0 else z a₀ a, fun a b hab ↦ ?_⟩
  by_cases ha : a = a₀
  · subst ha
    simp [hab.ne']
  by_cases hb : b = a₀
  · subst hb
    simp [ha, hanti _ _ hab]
  · simpa [ha, hb] using eq_sub_of_add_eq' (hcoc a₀ a b (h₀ (Ne.symm ha)) hab (h₀ (Ne.symm hb)))

/-- A graph without edges has trivial first cohomology of its flag complex. -/
@[simp]
theorem hasTrivialFlagFirstCohomology_bot :
    (⊥ : SimpleGraph V).HasTrivialFlagFirstCohomology A :=
  fun _ _ _ ↦ ⟨0, fun _ _ hab ↦ hab.elim⟩

/-- A graph on at most one vertex has trivial first cohomology of its flag complex. -/
@[simp]
theorem HasTrivialFlagFirstCohomology.of_subsingleton [Subsingleton V] :
    Γ.HasTrivialFlagFirstCohomology A :=
  Subsingleton.elim (⊥ : SimpleGraph V) Γ ▸ hasTrivialFlagFirstCohomology_bot

/-- A complete graph has trivial first cohomology of its flag complex. -/
@[simp]
theorem hasTrivialFlagFirstCohomology_top :
    (⊤ : SimpleGraph V).HasTrivialFlagFirstCohomology A := by
  rcases isEmpty_or_nonempty V with _ | ⟨⟨a₀⟩⟩
  · exact .of_subsingleton
  · exact (IsUniversal.top (v := a₀)).hasTrivialFlagFirstCohomology

/-- Trivial first cohomology of the flag complex is transported along a graph isomorphism. -/
theorem HasTrivialFlagFirstCohomology.of_iso (h : Γ.HasTrivialFlagFirstCohomology A)
    (e : Γ ≃g Γ') : Γ'.HasTrivialFlagFirstCohomology A := by
  intro z hanti hcoc
  obtain ⟨c, hc⟩ := h (fun a b ↦ z (e a) (e b)) (fun a b hab ↦ hanti _ _ (e.map_adj_iff.2 hab))
    fun a b c hab hbc hac ↦
      hcoc _ _ _ (e.map_adj_iff.2 hab) (e.map_adj_iff.2 hbc) (e.map_adj_iff.2 hac)
  refine ⟨c ∘ e.symm, fun a b hab ↦ ?_⟩
  simpa using hc (e.symm a) (e.symm b) (e.symm.map_adj_iff.2 hab)

/-- Isomorphic graphs have trivial first cohomology of their flag complexes simultaneously. -/
theorem Iso.hasTrivialFlagFirstCohomology_iff (e : Γ ≃g Γ') :
    Γ.HasTrivialFlagFirstCohomology A ↔ Γ'.HasTrivialFlagFirstCohomology A :=
  ⟨fun h ↦ h.of_iso e, fun h ↦ h.of_iso e.symm⟩

/-- With nontrivial coefficients, the cycle graph on `n` vertices has trivial first cohomology of
its flag complex exactly when `n ≤ 3`. -/
@[simp]
theorem hasTrivialFlagFirstCohomology_cycleGraph_iff [Nontrivial A] {n : ℕ} :
    (cycleGraph n).HasTrivialFlagFirstCohomology A ↔ n ≤ 3 := by
  refine ⟨fun h ↦ ?_, fun h ↦ cycleGraph_eq_top_iff.2 h ▸ hasTrivialFlagFirstCohomology_top⟩
  by_contra! hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : A)
  -- there is no triangle, so the cochain with values `x` on `(0, 1)`, `-x` on `(1, 0)` and `0`
  -- elsewhere is a cocycle
  obtain ⟨c, hc⟩ := h (fun a b ↦ if a.val + b.val = 1 then if a.val = 0 then x else -x else 0)
    (fun a b _ ↦ by grind) fun a b c hab hbc hac ↦ by
      exfalso
      grind [cycleGraph_adj', Fin.coe_int_sub_eq_ite]
  -- summed over the edges `(i, i + 1)`, it gives `x`, while a coboundary gives `0`
  have hsum := Fintype.sum_congr _ _ fun i : Fin (m + 4) ↦ hc i (i + 1) (by simp [cycleGraph_adj])
  have h0 (i : Fin (m + 4)) : i.val + (i + 1).val = 1 ↔ i = 0 := by grind [Fin.val_add_one]
  simp only [h0, Fintype.sum_ite_eq', Finset.sum_sub_distrib,
    Fintype.sum_equiv (Equiv.addRight 1) (fun i ↦ c (i + 1)) c fun _ ↦ rfl, sub_self] at hsum
  exact hx (by simpa using hsum)

end SimpleGraph
