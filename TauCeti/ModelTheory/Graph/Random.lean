/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Graph
public import TauCeti.Combinatorics.SimpleGraph.ExtensionProperty
public import TauCeti.ModelTheory.Infinitary.Semantics
import Mathlib.Data.Fin.Tuple.Basic
import TauCeti.ModelTheory.BackAndForth.Graph
import TauCeti.ModelTheory.Infinitary.Theory

/-!
# The first-order theory of the random graph

The extension axiom with parameters `m` and `n` asks for a vertex adjacent to the first `m`
vertices and distinct from and nonadjacent to the next `n`, whenever the two tuples have disjoint
ranges. Together with the simple-graph axioms these sentences axiomatize the extension property.
Their countable conjunction `randomGraphSentence` packages the theory as a single `L_{ω₁ω}`
sentence.
-/

public section

open FirstOrder

namespace FirstOrder.Language

/-- The extension axiom for a positive tuple of length `m` and a negative tuple of length `n`.
Whenever the two tuples are disjoint, some vertex has the prescribed adjacency pattern. -/
noncomputable def graphExtensionAxiom (m n : ℕ) : Language.graph.Sentence :=
  let disjoint : Language.graph.BoundedFormula Empty (m + n) :=
    BoundedFormula.iInf fun p : Fin m × Fin n =>
      ((&(p.1.castAdd n)).bdEqual (&(p.2.natAdd m))).not
  let z := Fin.last (m + n)
  let positive : Language.graph.BoundedFormula Empty (m + n + 1) :=
    BoundedFormula.iInf fun i : Fin m => adj.boundedFormula₂ (&z) (&(i.castAdd n).castSucc)
  let negative : Language.graph.BoundedFormula Empty (m + n + 1) :=
    BoundedFormula.iInf fun j : Fin n =>
      ((&z).bdEqual (&(j.natAdd m).castSucc)).not ⊓
        (adj.boundedFormula₂ (&z) (&(j.natAdd m).castSucc)).not
  (disjoint.imp (positive ⊓ negative).ex).alls

/-- A graph satisfies the extension axiom for tuple lengths `m` and `n` exactly when each
pair of disjoint tuples of those lengths has a vertex with the required adjacencies. -/
@[simp]
theorem _root_.SimpleGraph.realize_graphExtensionAxiom {V : Type*} (G : SimpleGraph V) (m n : ℕ) :
    @Sentence.Realize Language.graph V G.structure (graphExtensionAxiom m n) ↔
      ∀ a : Fin m → V, ∀ b : Fin n → V, (∀ i j, a i ≠ b j) →
        ∃ z, (∀ i, G.Adj z (a i)) ∧ ∀ j, z ≠ b j ∧ ¬G.Adj z (b j) := by
  let _ := G.structure
  have h : V ⊨ graphExtensionAxiom m n ↔
      ∀ v : Fin (m + n) → V, (∀ i : Fin m, ∀ j : Fin n, v (i.castAdd n) ≠ v (j.natAdd m)) →
        ∃ z, (∀ i : Fin m, G.Adj z (v (i.castAdd n))) ∧
          ∀ j : Fin n, z ≠ v (j.natAdd m) ∧ ¬G.Adj z (v (j.natAdd m)) := by
    rw [Sentence.Realize]
    -- Keep `castSucc` outermost on the negative tuple indices so `Fin.snoc_castSucc` applies.
    simp [graphExtensionAxiom, -Fin.castSucc_natAdd]
  rw [h]
  refine ⟨fun h a b hab => ?_, fun h v => h (v ∘ Fin.castAdd n) (v ∘ Fin.natAdd m)⟩
  simpa using h (Fin.append a b) (by simpa using hab)

/-- The simple-graph axioms and all finite adjacency extension axioms. -/
noncomputable def Theory.randomGraph : Language.graph.Theory :=
  Theory.simpleGraph ∪ Set.range (fun p : ℕ × ℕ => graphExtensionAxiom p.1 p.2)

/-- A sentence belongs to the random-graph theory if it is a simple-graph axiom or one of the
extension axioms. -/
@[simp]
theorem Theory.mem_randomGraph {φ : Language.graph.Sentence} :
    φ ∈ Theory.randomGraph ↔ φ ∈ Theory.simpleGraph ∨ ∃ m n, graphExtensionAxiom m n = φ := by
  simp only [Theory.randomGraph, Set.mem_union, Set.mem_range, Prod.exists]

/-- The random-graph theory includes the simple-graph axioms. -/
theorem Theory.simpleGraph_subset_randomGraph : Theory.simpleGraph ⊆ Theory.randomGraph :=
  Set.subset_union_left

/-- On a simple graph, the random-graph axioms hold exactly when the graph has the extension
property. -/
@[simp]
theorem _root_.SimpleGraph.randomGraph_model_iff {V : Type*} (G : SimpleGraph V) :
    @Theory.Model Language.graph V G.structure Theory.randomGraph ↔ G.HasExtensionProperty := by
  classical
  let _ := G.structure
  have hsimple : V ⊨ Theory.simpleGraph := inferInstance
  rw [Theory.randomGraph, Theory.model_union_iff, and_iff_right hsimple]
  simp only [Theory.model_iff, Set.forall_mem_range, Prod.forall,
    SimpleGraph.realize_graphExtensionAxiom, SimpleGraph.hasExtensionProperty_def]
  constructor
  · intro h s t hst
    let a i := ((s.equivFin).symm i : V)
    let b j := ((t.equivFin).symm j : V)
    obtain ⟨z, ha, hb⟩ := h s.card t.card a b fun i j hij => by
      have hi : a i ∈ s := (s.equivFin.symm i).property
      have hj : b j ∈ t := (t.equivFin.symm j).property
      exact Finset.disjoint_left.mp hst hi (hij.symm ▸ hj)
    refine ⟨z, fun hz => (hb (t.equivFin ⟨z, hz⟩)).1 (by simp [b]), ?_, ?_⟩
    · intro u hu
      simpa [a] using ha (s.equivFin ⟨u, hu⟩)
    · intro w hw
      simpa [b] using (hb (t.equivFin ⟨w, hw⟩)).2
  · intro h m n a b hab
    have hst : Disjoint (Finset.univ.image a) (Finset.univ.image b) := by
      simp only [Finset.disjoint_left, Finset.mem_image, Finset.mem_univ, true_and]
      rintro _ ⟨i, rfl⟩ ⟨j, hji⟩
      exact hab i j hji.symm
    obtain ⟨z, hz, ha, hb⟩ := h _ _ hst
    refine ⟨z, fun i => ha _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)), fun j => ?_⟩
    have hj := Finset.mem_image_of_mem b (Finset.mem_univ j)
    exact ⟨fun h => hz (h.symm ▸ hj), hb _ hj⟩

/-- The conjunction of the simple-graph axioms and all first-order extension axioms. -/
noncomputable def randomGraphSentence : Language.graph.Sentenceω :=
  Theoryω.conjunction (BoundedFormula.toOmega '' Theory.randomGraph) (by
    apply Set.Countable.image
    unfold Theory.randomGraph Theory.simpleGraph
    exact ((Set.countable_singleton _).insert _).union (Set.countable_range _))

/-- The random-graph sentence holds exactly in the models of the first-order random-graph theory. -/
@[simp]
theorem realize_randomGraphSentence_iff {V : Type*} [Language.graph.Structure V] :
    SentenceInf.Realize randomGraphSentence V ↔ V ⊨ Theory.randomGraph := by
  rw [randomGraphSentence, Theoryω.realize_conjunction_iff, Theoryω.model_image_toOmega_iff]

end FirstOrder.Language
