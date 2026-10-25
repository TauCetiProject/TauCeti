/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.ExtensionProperty
public import TauCeti.ModelTheory.BackAndForth.Countable
public import TauCeti.ModelTheory.BackAndForth.ExtensionPair
public import TauCeti.ModelTheory.BackAndForth.Graph
public import TauCeti.ModelTheory.BackAndForth.Karp
public import TauCeti.ModelTheory.Scott.ExtensionPair
public import TauCeti.ModelTheory.Scott.PotentialIso

/-!
# Scott analysis of the random graph

A simple graph has the *extension property* (`SimpleGraph.HasExtensionProperty`) when, for any
two disjoint finite sets of vertices `s` and `t`, some vertex outside `t` is adjacent to every
vertex of `s` and to no vertex of `t`. Graphs with this property are the models of the theory of
the random graph. Back-and-forth for them works just as Cantor's argument does for dense linear
orders: a finite partial isomorphism into such a graph extends to any new vertex. For graphs of
every cardinality this gives:

* between two graphs with the extension property, tuples are back-and-forth equivalent at every
  level exactly when they have the same atomic type, and the two graphs are potentially
  isomorphic;
* any two countable graphs with the extension property are isomorphic (`ℵ₀`-categoricity);
* every graph with the extension property has internal Scott rank one;
* the extension property is invariant under potential isomorphism, and the Scott sentence of a
  countable graph with the extension property holds in a graph of any cardinality exactly when
  that graph has the extension property.

The Rado graph `TauCeti.radoGraph` on `ℕ` has the extension property
(`TauCeti.hasExtensionProperty_radoGraph`). So up to isomorphism it is the unique countable graph
with the extension property, the countable random graph.

## Main results

* `SimpleGraph.HasExtensionProperty.isExtensionPair`: every graph forms an extension pair with a
  graph with the extension property.
* `SimpleGraph.HasExtensionProperty.potentialIso` and
  `SimpleGraph.HasExtensionProperty.nonempty_iso`.
* `SimpleGraph.HasExtensionProperty.internalScottRank_eq_one`.
* `SimpleGraph.HasExtensionProperty.realize_scottSentence_iff`.
* `TauCeti.nonempty_iso_radoGraph_iff`.

## References

* Richard Rado, *Universal graphs and universal functions*, Acta Arith. 9 (1964), 331–340.
* Peter J. Cameron, *The random graph*, in *The Mathematics of Paul Erdős II*, Springer, 1997.
* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, 1965.
-/

public section

universe u u' o

open FirstOrder FirstOrder.Language Fin TauCeti

variable {V : Type u} {W : Type u'}

namespace SimpleGraph

variable {G : SimpleGraph V} {H : SimpleGraph W}

namespace HasExtensionProperty

variable (G) in
/-- If `H` has the extension property, tuples of vertices of `G` and `H` with the same atomic type
have matching one-point extensions on the `G` side. -/
theorem exists_sameAtomicType_snoc (hH : H.HasExtensionProperty) {n : ℕ} {a : Fin n → V}
    {b : Fin n → W}
    (h : letI := G.structure; letI := H.structure; SameAtomicType (L := Language.graph) a b)
    (x : V) :
    ∃ y : W, letI := G.structure; letI := H.structure
      SameAtomicType (L := Language.graph) (snoc a x) (snoc b y) := by
  let := G.structure
  let := H.structure
  by_cases hx : ∃ i, a i = x
  · -- An old vertex is answered by the matching old vertex.
    obtain ⟨i, rfl⟩ := hx
    refine ⟨b i, ?_⟩
    simpa only [comp_snoc, Function.comp_id] using h.comp (snoc id i)
  push Not at hx
  obtain ⟨heq, hadj⟩ := (sameAtomicType_iff G H a b).mp h
  obtain ⟨y, hyne, hyadj⟩ := hH.exists_adj_iff b (fun i => G.Adj x (a i))
    fun i j hij => by rw [(heq i j).mpr hij]
  refine ⟨y, (sameAtomicType_iff G H _ _).mpr ⟨fun i j => ?_, fun i j => ?_⟩⟩
  · induction i using lastCases <;> induction j using lastCases <;>
      simp [heq, hx, (hx _).symm, hyne, (hyne _).symm]
  · induction i using lastCases <;> induction j using lastCases <;>
      simp [hadj, hyadj, G.adj_comm _ x, H.adj_comm _ y]

variable (G) in
/-- Every graph `G` forms an extension pair with a graph `H` with the extension property: each
finite partial isomorphism from `G` to `H` extends to any further vertex of `G`. -/
theorem isExtensionPair (hH : H.HasExtensionProperty) :
    letI := G.structure; letI := H.structure; Language.graph.IsExtensionPair V W :=
  letI := G.structure
  letI := H.structure
  isExtensionPair_iff_forall_exists_snoc.mpr fun h x => hH.exists_sameAtomicType_snoc G h x

/-- Between graphs with the extension property, tuples are back-and-forth equivalent at any level
exactly when they have the same atomic type. -/
theorem bfEquiv_iff_sameAtomicType (hG : G.HasExtensionProperty) (hH : H.HasExtensionProperty)
    {α : Ordinal.{o}} {n : ℕ} {a : Fin n → V} {b : Fin n → W} :
    letI := G.structure; letI := H.structure
    BFEquiv (L := Language.graph) α n a b ↔ SameAtomicType (L := Language.graph) a b :=
  letI := G.structure
  letI := H.structure
  ⟨BFEquiv.sameAtomicType, fun h =>
    h.bfEquiv_of_isExtensionPair (hH.isExtensionPair G) (hG.isExtensionPair H) α⟩

/-- Any two graphs with the extension property are potentially isomorphic, whatever their
cardinalities. -/
theorem potentialIso (hG : G.HasExtensionProperty) (hH : H.HasExtensionProperty) :
    letI := G.structure; letI := H.structure; PotentialIso (L := Language.graph) V W :=
  letI := G.structure
  letI := H.structure
  (isTupleBFSystem_sameAtomicType (hH.isExtensionPair G) (hG.isExtensionPair H)
    ((sameAtomicType_iff G H _ _).mpr ⟨finZeroElim, finZeroElim⟩)).potentialIso

/-- Any two countable graphs with the extension property are isomorphic: the theory of the
random graph is `ℵ₀`-categorical. -/
theorem nonempty_iso [Countable V] [Countable W] (hG : G.HasExtensionProperty)
    (hH : H.HasExtensionProperty) : Nonempty (G ≃g H) := by
  let := G.structure
  let := H.structure
  obtain ⟨e⟩ := countable_potentialIso_iff_iso.mp (hG.potentialIso hH)
  -- In `SimpleGraph.structure` the adjacency symbol on `![a, b]` is interpreted as `Adj a b`.
  exact ⟨⟨e.toEquiv, fun {a b} => e.map_rel Language.adj ![a, b]⟩⟩

/-- Every graph with the extension property, of any cardinality, has internal Scott rank one. -/
theorem internalScottRank_eq_one (hG : G.HasExtensionProperty) :
    letI := G.structure; internalScottRank (L := Language.graph) V = 1 :=
  letI := G.structure
  (hG.isExtensionPair G).internalScottRank_eq_one

/-- The extension property is invariant under potential isomorphism: it passes from a graph to
every graph potentially isomorphic to it, whatever its cardinality. -/
theorem of_potentialIso (hG : G.HasExtensionProperty)
    (h : letI := G.structure; letI := H.structure; PotentialIso (L := Language.graph) V W) :
    H.HasExtensionProperty := by
  classical
  let := G.structure
  let := H.structure
  obtain ⟨S, hS⟩ := h.exists_isTupleBFSystem
  refine hasExtensionProperty_def.mpr fun s t hst => ?_
  -- Enumerate `s ∪ t` by a tuple `b`, match it, and solve the pattern in `G`.
  let b : Fin (s ∪ t).card → W := fun i => (s ∪ t).equivFin.symm i
  have hb {v : W} (hv : v ∈ s ∪ t) : ∃ i, b i = v := ⟨(s ∪ t).equivFin ⟨v, hv⟩, by simp [b]⟩
  obtain ⟨a, hab⟩ := hS.exists_fst_mem b
  obtain ⟨heq, -⟩ := (sameAtomicType_iff G H a b).mp (hS.sameAtomicType hab)
  obtain ⟨x, hxne, hxadj⟩ := hG.exists_adj_iff a (fun i => b i ∈ s)
    fun i j hij => by rw [(heq i j).mp hij]
  obtain ⟨y, hy⟩ := hS.forth hab x
  obtain ⟨heq', hadj'⟩ := (sameAtomicType_iff G H _ _).mp (hS.sameAtomicType hy)
  have hyadj (i) : H.Adj y (b i) ↔ b i ∈ s := by
    simpa [hxadj] using (hadj' (last _) i.castSucc).symm
  have hyne (i) : y ≠ b i := fun hyi => hxne i (by simpa [hyi] using heq' (last _) i.castSucc)
  refine ⟨y, fun hyt => ?_, fun u hu => ?_, fun w hw => ?_⟩
  · obtain ⟨i, hi⟩ := hb (Finset.mem_union_right s hyt)
    exact hyne i hi.symm
  · obtain ⟨i, rfl⟩ := hb (Finset.mem_union_left t hu)
    exact (hyadj i).mpr hu
  · obtain ⟨i, rfl⟩ := hb (Finset.mem_union_right s hw)
    exact fun hadj => Finset.disjoint_right.mp hst hw ((hyadj i).mp hadj)

variable (H) in
/-- The Scott sentence of a countable graph with the extension property holds in a graph of any
cardinality exactly when that graph has the extension property. -/
theorem realize_scottSentence_iff [Countable V] (hG : G.HasExtensionProperty) :
    letI := G.structure; letI := H.structure
    SentenceInf.Realize (scottSentence (L := Language.graph) V) W ↔ H.HasExtensionProperty := by
  let := G.structure
  let := H.structure
  refine ⟨fun h => hG.of_potentialIso (potentialIso_of_realize_scottSentence V h), fun hH => ?_⟩
  exact (infEquivAt_iff.mp ((hG.potentialIso hH).infEquivAt ℕ) _).mp (realize_scottSentence_self V)

end HasExtensionProperty

end SimpleGraph

namespace TauCeti

open SimpleGraph

/-- A countable graph is isomorphic to the Rado graph exactly when it has the extension
property. -/
theorem nonempty_iso_radoGraph_iff [Countable V] {G : SimpleGraph V} :
    Nonempty (G ≃g radoGraph) ↔ G.HasExtensionProperty := by
  let := G.structure
  let := radoGraph.structure
  exact ⟨fun ⟨e⟩ => hasExtensionProperty_radoGraph.of_potentialIso
      e.symm.toLanguageEquiv.potentialIso,
    fun hG => hG.nonempty_iso hasExtensionProperty_radoGraph⟩

end TauCeti
