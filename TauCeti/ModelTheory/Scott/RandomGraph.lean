/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.Rado
public import TauCeti.ModelTheory.BackAndForth.Countable
public import TauCeti.ModelTheory.BackAndForth.Graph
public import TauCeti.ModelTheory.BackAndForth.Karp
public import TauCeti.ModelTheory.Scott.ExtensionPair
public import TauCeti.ModelTheory.Scott.PotentialIso

/-!
# Scott analysis of the random graph

A simple graph with the extension property (`SimpleGraph.HasExtensionProperty`) is the graph
counterpart of a dense linear order without endpoints: every finite partial isomorphism from any
graph into it extends to any new vertex, so in the language of graphs every graph forms an
extension pair with it. For graphs of every cardinality this gives:

* any two graphs with the extension property are potentially isomorphic, and every graph with
  the extension property has internal Scott rank one;
* the extension property passes along potential isomorphisms, so the Scott sentence of a
  countable graph with the extension property, such as the Rado graph `SimpleGraph.radoGraph`,
  holds in a graph exactly when that graph has the extension property.

For countable graphs potential isomorphism is isomorphism
(`TauCeti.countable_potentialIso_iff_iso`), so the random graph is `ℵ₀`-categorical: any two
countable graphs with the extension property are isomorphic, and in particular every countable
graph with the extension property is isomorphic to the Rado graph.

## Main results

* `SimpleGraph.HasExtensionProperty.isExtensionPair`: every graph forms an extension pair with a
  graph with the extension property.
* `SimpleGraph.HasExtensionProperty.potentialIso` and
  `SimpleGraph.HasExtensionProperty.of_potentialIso`.
* `SimpleGraph.HasExtensionProperty.nonempty_iso`: `ℵ₀`-categoricity.
* `SimpleGraph.HasExtensionProperty.internalScottRank_eq_one`.
* `SimpleGraph.HasExtensionProperty.realize_scottSentence_iff`.

## References

* Paul Erdős and Alfréd Rényi, *Asymmetric graphs*, 1963.
* Richard Rado, *Universal graphs and universal functions*, 1964.
* Dana Scott, *Logic with denumerably long formulas and finite strings of quantifiers*, 1965.
-/

public section

universe u u'

open FirstOrder FirstOrder.Language Fin TauCeti

namespace SimpleGraph

variable {V : Type u} {W : Type u'} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Matching equality and adjacency patterns of two tuples extend by one vertex on the side of a
graph with the extension property. -/
private theorem HasExtensionProperty.exists_snoc (hH : H.HasExtensionProperty) {n : ℕ}
    {a : Fin n → V} {b : Fin n → W} (heq : ∀ i j, a i = a j ↔ b i = b j)
    (hadj : ∀ i j, G.Adj (a i) (a j) ↔ H.Adj (b i) (b j)) (x : V) :
    ∃ y : W, (∀ i, x = a i ↔ y = b i) ∧ ∀ i, G.Adj x (a i) ↔ H.Adj y (b i) := by
  classical
  by_cases hx : ∃ k, a k = x
  · obtain ⟨k, rfl⟩ := hx
    exact ⟨b k, fun i => heq k i, fun i => hadj k i⟩
  push Not at hx
  -- Prescribe the neighbours of the new vertex among the entries of `b` as those of `x` in `a`.
  let U := (Finset.univ.filter fun i => G.Adj x (a i)).image b
  let U' := (Finset.univ.filter fun i => ¬G.Adj x (a i)).image b
  have hUU' : Disjoint U U' := by
    simp only [U, U', Finset.disjoint_left, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rintro _ ⟨i, hi, rfl⟩ ⟨j, hj, hji⟩
    exact hj ((heq j i).mpr hji ▸ hi)
  obtain ⟨y, hyU', hyU, hyU''⟩ := (hasExtensionProperty_iff.mp hH) U U' hUU'
  have hy (i : Fin n) : y ≠ b i ∧ (G.Adj x (a i) ↔ H.Adj y (b i)) := by
    by_cases hi : G.Adj x (a i)
    · have := hyU (b i) (Finset.mem_image_of_mem b (by simp [hi]))
      exact ⟨this.ne, iff_of_true hi this⟩
    · have hbi : b i ∈ U' := Finset.mem_image_of_mem b (by simp [hi])
      exact ⟨fun h => hyU' (h ▸ hbi), iff_of_false hi (hyU'' _ hbi)⟩
  exact ⟨y, fun i => iff_of_false (hx i).symm (hy i).1, fun i => (hy i).2⟩

variable (G) in
/-- Every graph forms an extension pair, in the language of graphs, with a graph with the
extension property: each finite partial isomorphism extends to any further vertex. -/
theorem HasExtensionProperty.isExtensionPair (hH : H.HasExtensionProperty) :
    letI := G.structure
    letI := H.structure
    Language.graph.IsExtensionPair V W := by
  let := G.structure
  let := H.structure
  refine isExtensionPair_iff_exists_snoc.mpr fun {n a b} h x => ?_
  obtain ⟨heq, hadj⟩ := (sameAtomicType_iff G H a b).mp h
  obtain ⟨y, hyeq, hyadj⟩ := hH.exists_snoc heq hadj x
  have hyeq' (i : Fin n) : a i = x ↔ b i = y := eq_comm.trans ((hyeq i).trans eq_comm)
  refine ⟨y, (sameAtomicType_iff G H _ _).mpr ⟨fun i j => ?_, fun i j => ?_⟩⟩ <;>
    induction i using lastCases <;> induction j using lastCases <;>
    simp [heq, hadj, hyeq, hyeq', hyadj, G.adj_comm _ x, H.adj_comm _ y]

/-- Any two graphs with the extension property are potentially isomorphic, whatever their
cardinalities. -/
theorem HasExtensionProperty.potentialIso (hG : G.HasExtensionProperty)
    (hH : H.HasExtensionProperty) :
    letI := G.structure
    letI := H.structure
    PotentialIso (L := Language.graph) V W :=
  letI := G.structure
  letI := H.structure
  (isTupleBFSystem_sameAtomicType (hH.isExtensionPair G) (hG.isExtensionPair H)
    ((sameAtomicType_iff G H _ _).mpr ⟨fun i => i.elim0, fun i => i.elim0⟩)).potentialIso

/-- A graph potentially isomorphic to a graph with the extension property has the extension
property. -/
theorem HasExtensionProperty.of_potentialIso (hG : G.HasExtensionProperty)
    (h : letI := G.structure
      letI := H.structure
      PotentialIso (L := Language.graph) V W) :
    H.HasExtensionProperty := by
  classical
  let := G.structure
  let := H.structure
  obtain ⟨S, hS⟩ := h.exists_isTupleBFSystem
  refine hasExtensionProperty_iff.mpr fun U U' hUU' => ?_
  -- Enumerate `U ∪ U'`, match the enumeration in `G`, and extend there.
  let e := (U ∪ U').equivFin
  let b : Fin (U ∪ U').card → W := fun i => e.symm i
  have hb {w : W} (hw : w ∈ U ∪ U') : b (e ⟨w, hw⟩) = w := by simp [b]
  obtain ⟨a, hab⟩ := hS.exists_mem b
  obtain ⟨heq, hadj⟩ := (sameAtomicType_iff G H a b).mp (hS.sameAtomicType hab)
  let A := (Finset.univ.filter fun i => b i ∈ U).image a
  let A' := (Finset.univ.filter fun i => b i ∈ U').image a
  have hAA' : Disjoint A A' := by
    simp only [A, A', Finset.disjoint_left, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rintro _ ⟨i, hi, rfl⟩ ⟨j, hj, hji⟩
    exact Finset.disjoint_left.mp hUU' hi ((heq j i).mp hji ▸ hj)
  obtain ⟨x, hxA', hxA, hxA''⟩ := (hasExtensionProperty_iff.mp hG) A A' hAA'
  obtain ⟨y, hy⟩ := hS.forth hab x
  obtain ⟨heq', hadj'⟩ := (sameAtomicType_iff G H _ _).mp (hS.sameAtomicType hy)
  have hxy (i : Fin (U ∪ U').card) : (x = a i ↔ y = b i) ∧ (G.Adj x (a i) ↔ H.Adj y (b i)) := by
    simpa using And.intro (heq' (last _) i.castSucc) (hadj' (last _) i.castSucc)
  refine ⟨y, fun hy' => ?_, fun u hu => ?_, fun w hw => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, b i = y := ⟨_, hb (Finset.mem_union_right U hy')⟩
    exact hxA' (Finset.mem_image.mpr ⟨i, by simp [hi, hy'], ((hxy i).1.mpr hi.symm).symm⟩)
  · rw [← hb (Finset.mem_union_left U' hu)]
    exact (hxy _).2.mp (hxA _ (Finset.mem_image_of_mem a (by simp [hb, hu])))
  · rw [← hb (Finset.mem_union_right U hw)]
    exact fun h => hxA'' _ (Finset.mem_image_of_mem a (by simp [hb, hw])) ((hxy _).2.mpr h)

/-- **`ℵ₀`-categoricity of the random graph.** Any two countable graphs with the extension
property are isomorphic. -/
theorem HasExtensionProperty.nonempty_iso [Countable V] [Countable W]
    (hG : G.HasExtensionProperty) (hH : H.HasExtensionProperty) : Nonempty (G ≃g H) :=
  letI := G.structure
  letI := H.structure
  (countable_potentialIso_iff_iso.mp (hG.potentialIso hH)).map Equiv.toSimpleGraphIso

/-- Every graph with the extension property, of any cardinality, has internal Scott rank one. -/
theorem HasExtensionProperty.internalScottRank_eq_one (hG : G.HasExtensionProperty) :
    letI := G.structure
    internalScottRank (L := Language.graph) V = 1 :=
  letI := G.structure
  (hG.isExtensionPair G).internalScottRank_eq_one

/-- The Scott sentence of a countable graph with the extension property holds in a graph of any
cardinality exactly when that graph has the extension property. -/
theorem HasExtensionProperty.realize_scottSentence_iff [Countable V]
    (hG : G.HasExtensionProperty) (H : SimpleGraph W) :
    letI := G.structure
    letI := H.structure
    SentenceInf.Realize (scottSentence (L := Language.graph) V) W ↔ H.HasExtensionProperty := by
  let := G.structure
  let := H.structure
  refine ⟨fun h => hG.of_potentialIso (potentialIso_of_realize_scottSentence V h), fun hH => ?_⟩
  exact (infEquivAt_iff.mp ((hG.potentialIso hH).infEquivAt ℕ) _).mp
    (realize_scottSentence_self V)

end SimpleGraph
