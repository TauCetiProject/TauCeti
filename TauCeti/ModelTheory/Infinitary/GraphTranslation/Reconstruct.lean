/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.GraphTranslation.Relationalize
public import TauCeti.ModelTheory.Infinitary.Theory

/-!
# Graph axioms and the reconstruction of functions from their graphs

A structure for the graph language `L.graphLanguage` interprets the graph symbol `G_f` of a
function symbol `f` of `L` as an arbitrary relation, which need not be the graph of a function.
The **graph axioms** of a set `F` of function symbols say that it is, for each `f ∈ F`:
**totality** `∀ xs, ∃ y, G_f(xs, y)` and **functionality**
`∀ xs y z, G_f(xs, y) → G_f(xs, z) → y = z`. The graph expansion of an `L`-structure satisfies
the graph axioms of every set of function symbols.

Conversely, on a nonempty carrier every graph-language structure has a **reconstruction**, the
`L`-structure `reconstructStructure L M` whose relation symbols are read off the base relations and
whose function symbol `f` sends `xs` to a chosen `y` with `G_f(xs, y)`, if there is one. On a model
of the graph axioms of `F` the value of `f ∈ F` at `xs` is the unique such `y`, so the graph
expansion of the reconstruction agrees with the given structure on every base relation and on the
graph relation of every `f ∈ F`. By symbol locality, a formula whose function symbols lie in `F`
therefore has a translation into the graph language that is realized in the given structure
exactly when the formula is realized in the reconstruction
(`BoundedFormulaInf.realize_relationalize_reconstructStructure`). This is the semantic step that
moves an entailment between graph-language translations back to the original language. In the
other direction, the reconstruction of the graph expansion of an `L`-structure is that structure
(`reconstructStructure_graphExpansion`).

## Main definitions

* `FirstOrder.Language.Functions.graphTotality`, `FirstOrder.Language.Functions.graphFunctionality`:
  totality and functionality of the graph relation of a function symbol.
* `FirstOrder.Language.graphAxioms`: the theory of totality and functionality of the graph
  relations of a set of function symbols.
* `FirstOrder.Language.reconstructStructure`: the `L`-structure read off a graph-language structure
  on a nonempty carrier.

## Main results

* `FirstOrder.Language.model_graphAxioms_iff`: a structure models the graph axioms of `F` exactly
  when the graph relation of each `f ∈ F` relates every argument tuple to exactly one value.
* `FirstOrder.Language.model_graphAxioms_graphExpansion`: the graph expansion of an `L`-structure
  models the graph axioms of every set of function symbols.
* `FirstOrder.Language.relationsIn_graphAxioms`: the graph axioms of `F` mention exactly the graph
  relations of the symbols in `F`.
* `FirstOrder.Language.relMap_graph_funMap_reconstructStructure`: where the graph relation of `f`
  relates `xs` to some value, the reconstruction sends `xs` to such a value.
* `FirstOrder.Language.funMap_reconstructStructure_eq_iff`: where the graph relation of `f` relates
  `xs` to exactly one value, the reconstruction sends `xs` to that value.
* `FirstOrder.Language.BoundedFormulaInf.realize_relationalize_reconstructStructure`: on a model of
  the graph axioms of `F`, the translation of a formula whose function symbols lie in `F` is
  realized exactly when the formula is realized in the reconstruction.
* `FirstOrder.Language.reconstructStructure_graphExpansion`: reconstructing the graph expansion of
  an `L`-structure gives back the structure.

## References

* The graph axioms and the reconstruction follow `graphTotality`, `graphFunctionality`,
  `graphAxioms`, `reconstructStructure` and `realize_relationalize_reconstruct` of
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, in
  `InfinitaryLogic/Methods/Interpolation/GraphAxioms.lean` and `GraphReconstruction.lean`.
  Divergences from that source: languages and structures live in arbitrary universes; the graph
  axioms form a theory, with no countability hypothesis, whose conjunction
  `Theoryω.conjunction` is the single sentence when `F` is countable; and the reconstruction
  chooses the value of every function symbol from its graph by `Classical.epsilon`, so that it
  depends neither on `F` nor on a proof of the graph axioms, and reconstructing a graph expansion
  recovers the whole structure.
-/

public section

universe u v w

namespace FirstOrder

namespace Language

open Structure

variable {L : Language.{u, v}}

namespace Functions

variable {k : ℕ} (f : L.Functions k)

/-- **Totality** of the graph relation of a function symbol `f`: the sentence
`∀ xs, ∃ y, G_f(xs, y)` of the graph language. -/
def graphTotality : L.graphLanguage.Sentenceω :=
  (BoundedFormulaInf.rel (GraphRelation.graph f) fun i => Term.var (Sum.inr i)).ex.alls

/-- **Functionality** of the graph relation of a function symbol `f`: the sentence
`∀ xs y z, G_f(xs, y) → G_f(xs, z) → y = z` of the graph language, with `xs` the first `k` bound
positions and `y`, `z` the last two. -/
def graphFunctionality : L.graphLanguage.Sentenceω :=
  ((BoundedFormulaInf.rel (GraphRelation.graph f) fun i =>
      Term.var (Sum.inr (Fin.snoc (α := fun _ => Fin (k + 2)) (fun j => j.castSucc.castSucc)
        (Fin.last k).castSucc i))).imp
    ((BoundedFormulaInf.rel (GraphRelation.graph f) fun i =>
        Term.var (Sum.inr (Fin.snoc (α := fun _ => Fin (k + 2)) (fun j => j.castSucc.castSucc)
          (Fin.last (k + 1)) i))).imp
      (BoundedFormulaInf.equal (Term.var (Sum.inr (Fin.last k).castSucc))
        (Term.var (Sum.inr (Fin.last (k + 1))))))).alls

variable {M : Type w} [L.graphLanguage.Structure M]

/-- Totality holds when the graph relation of `f` relates every argument tuple to some value. -/
@[simp]
theorem realize_graphTotality :
    SentenceInf.Realize f.graphTotality M ↔
      ∀ xs : Fin k → M, ∃ y, RelMap (L := L.graphLanguage) (GraphRelation.graph f)
        (Fin.snoc xs y) := by
  simp only [graphTotality, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_alls, BoundedFormulaInf.realize_ex, BoundedFormulaInf.realize_rel,
    Term.realize_var, Sum.elim_inr]

/-- Functionality holds when the graph relation of `f` relates every argument tuple to at most
one value. -/
@[simp]
theorem realize_graphFunctionality :
    SentenceInf.Realize f.graphFunctionality M ↔
      ∀ (xs : Fin k → M) (y z : M),
        RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y) →
        RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs z) → y = z := by
  simp only [graphFunctionality, SentenceInf.realize_def, FormulaInf.realize_def,
    BoundedFormulaInf.realize_alls, BoundedFormulaInf.realize_imp, BoundedFormulaInf.realize_rel,
    BoundedFormulaInf.realize_equal, Term.realize_var, Sum.elim_inr]
  constructor
  · intro h xs y z
    have := h (Fin.snoc (Fin.snoc xs y) z)
    simp only [← Function.comp_def (Fin.snoc _ _), Fin.comp_snoc] at this
    simpa [Function.comp_def] using this
  · intro h xs
    obtain ⟨ws, y, z, rfl⟩ : ∃ ws y z, Fin.snoc (Fin.snoc ws y) z = xs :=
      ⟨_, _, _, by rw [Fin.snoc_init_self, Fin.snoc_init_self]⟩
    simp only [← Function.comp_def (Fin.snoc _ _), Fin.comp_snoc]
    simpa [Function.comp_def] using h ws y z

/-- Totality mentions only the graph relation of `f`. -/
@[simp]
theorem relationsIn_graphTotality : f.graphTotality.relationsIn = {graphRelSym ⟨k, f⟩} := by
  simp [graphTotality]

/-- Functionality mentions only the graph relation of `f`. -/
@[simp]
theorem relationsIn_graphFunctionality :
    f.graphFunctionality.relationsIn = {graphRelSym ⟨k, f⟩} := by
  simp [graphFunctionality]

end Functions

/-! ### The graph axioms -/

/-- The **graph axioms** of a set `F` of function symbols of `L`: totality and functionality of
the graph relation of every `f ∈ F`. Their models are the graph-language structures in which the
graph relation of each `f ∈ F` is the graph of a function (`model_graphAxioms_iff`). -/
def graphAxioms (F : Set (Σ k, L.Functions k)) : L.graphLanguage.Theoryω :=
  (fun f => f.2.graphTotality) '' F ∪ (fun f => f.2.graphFunctionality) '' F

variable {F F₁ F₂ : Set (Σ k, L.Functions k)}

/-- The members of the graph axioms of `F` are the totality and functionality sentences of the
symbols in `F`. -/
@[simp]
theorem mem_graphAxioms_iff {φ : L.graphLanguage.Sentenceω} :
    φ ∈ graphAxioms F ↔ ∃ f ∈ F, f.2.graphTotality = φ ∨ f.2.graphFunctionality = φ := by
  simp only [graphAxioms, Set.mem_union, Set.mem_image, ← exists_or, and_or_left]

/-- The empty set of function symbols has no graph axioms. -/
@[simp]
theorem graphAxioms_empty : graphAxioms (∅ : Set (Σ k, L.Functions k)) = ∅ := by
  simp [graphAxioms]

/-- The graph axioms of a union of sets of function symbols are the union of their graph
axioms. -/
@[simp]
theorem graphAxioms_union : graphAxioms (F₁ ∪ F₂) = graphAxioms F₁ ∪ graphAxioms F₂ := by
  simp only [graphAxioms, Set.image_union]
  exact Set.union_union_union_comm _ _ _ _

/-- More function symbols have more graph axioms. -/
theorem graphAxioms_mono (h : F₁ ⊆ F₂) : graphAxioms F₁ ⊆ graphAxioms F₂ :=
  Set.union_subset_union (Set.image_mono h) (Set.image_mono h)

/-- The graph axioms of a countable set of function symbols are countable, so they form one
sentence, their conjunction `Theoryω.conjunction`. -/
theorem _root_.Set.Countable.graphAxioms (hF : F.Countable) : (graphAxioms F).Countable :=
  (hF.image _).union (hF.image _)

/-- **The occurrence identity**: the graph axioms of `F` mention exactly the graph relations of
the symbols in `F`. -/
theorem relationsIn_graphAxioms : ⋃ φ ∈ graphAxioms F, φ.relationsIn = relSym F ∅ := by
  ext S
  simp only [graphAxioms, Set.biUnion_union, Set.biUnion_image,
    Functions.relationsIn_graphTotality, Functions.relationsIn_graphFunctionality, Set.union_self,
    relSym_def, Set.image_empty, Set.empty_union]
  simp [Set.mem_iUnion, eq_comm]

section Model

variable {M : Type w} [L.graphLanguage.Structure M]

/-- A structure models the graph axioms of `F` exactly when the graph relation of each `f ∈ F`
relates every argument tuple to exactly one value. -/
theorem model_graphAxioms_iff :
    (graphAxioms F).Model M ↔ ∀ f ∈ F, ∀ xs : Fin f.1 → M,
      ∃! y, RelMap (L := L.graphLanguage) (GraphRelation.graph f.2) (Fin.snoc xs y) := by
  rw [graphAxioms, Theoryω.model_union_iff]
  simp only [Theoryω.model_iff, Set.forall_mem_image, Functions.realize_graphTotality,
    Functions.realize_graphFunctionality, ← forall_and]
  refine forall₂_congr fun f _ => forall_congr' fun xs => ?_
  exact ⟨fun ⟨⟨y, hy⟩, h⟩ => ⟨y, hy, fun z hz => h z y hz hy⟩,
    fun h => ⟨h.exists, fun _ _ => h.unique⟩⟩

end Model

variable (L) in
/-- The graph expansion of an `L`-structure models the graph axioms of every set of function
symbols. -/
theorem model_graphAxioms_graphExpansion (M : Type w) [L.Structure M]
    (F : Set (Σ k, L.Functions k)) :
    letI := graphExpansion L M
    (graphAxioms F).Model M := by
  let := graphExpansion L M
  rw [model_graphAxioms_iff]
  intro f _ xs
  refine ⟨funMap f.2 xs, by simp, fun y hy => ?_⟩
  simp only [graphExpansion_relMap_graph, Fin.init_snoc, Fin.snoc_last] at hy
  exact hy.symm

/-! ### Reconstruction -/

section Reconstruct

variable (L) (M : Type w) [L.graphLanguage.Structure M] [Nonempty M]

/-- The **reconstruction** of an `L`-structure from a structure for the graph language on a
nonempty carrier: a relation symbol of `L` is interpreted by its base relation, and a function
symbol `f` sends `xs` to a chosen `y` with `G_f(xs, y)`
(`relMap_graph_funMap_reconstructStructure`), or to an arbitrary element if there is none. Where
the graph relation of `f` is the graph of a function, the reconstruction interprets `f` by that
function (`funMap_reconstructStructure_eq_iff`). -/
@[instance_reducible]
noncomputable def reconstructStructure : L.Structure M where
  funMap f xs := Classical.epsilon fun y =>
    RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y)
  RelMap R xs := RelMap (L := L.graphLanguage) (GraphRelation.base R) xs

variable {L M}

/-- The reconstruction interprets a relation symbol of `L` by its base relation. -/
@[simp]
theorem relMap_reconstructStructure {k : ℕ} (R : L.Relations k) (xs : Fin k → M) :
    (reconstructStructure L M).RelMap R xs ↔
      RelMap (L := L.graphLanguage) (GraphRelation.base R) xs :=
  Iff.rfl

/-- Where the graph relation of `f` relates `xs` to some value, the reconstruction sends `xs` to
such a value. -/
theorem relMap_graph_funMap_reconstructStructure {k : ℕ} {f : L.Functions k} {xs : Fin k → M}
    (h : ∃ y, RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y)) :
    RelMap (L := L.graphLanguage) (GraphRelation.graph f)
      (Fin.snoc xs ((reconstructStructure L M).funMap f xs)) :=
  Classical.epsilon_spec h

/-- Where the graph relation of `f` relates `xs` to exactly one value, the reconstruction sends
`xs` to that value. -/
theorem funMap_reconstructStructure_eq_iff {k : ℕ} {f : L.Functions k} {xs : Fin k → M}
    (h : ∃! y, RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y))
    {y : M} :
    (reconstructStructure L M).funMap f xs = y ↔
      RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y) := by
  have hε := relMap_graph_funMap_reconstructStructure h.exists
  exact ⟨fun hy => hy ▸ hε, fun hy => h.unique hε hy⟩

/-- On a model of the graph axioms of `F`, the graph expansion of the reconstruction interprets
the graph relation of every `f ∈ F` as the given structure does. -/
theorem graphExpansion_reconstructStructure_relMap_graph (hM : (graphAxioms F).Model M) {k : ℕ}
    {f : L.Functions k} (hf : ⟨k, f⟩ ∈ F) (xs : Fin (k + 1) → M) :
    @RelMap L.graphLanguage M (@graphExpansion L M (reconstructStructure L M)) _
        (GraphRelation.graph f) xs ↔
      RelMap (L := L.graphLanguage) (GraphRelation.graph f) xs := by
  rw [@graphExpansion_relMap_graph,
    funMap_reconstructStructure_eq_iff (model_graphAxioms_iff.1 hM _ hf (Fin.init xs)),
    Fin.snoc_init_self]

/-- **Reconstruction preserves the translation.** On a model of the graph axioms of `F`, the
translation of a formula whose function symbols lie in `F` is realized exactly when the formula is
realized in the reconstruction. -/
theorem BoundedFormulaInf.realize_relationalize_reconstructStructure {α : Type*} {n : ℕ}
    (φ : L.BoundedFormulaω α n) (hM : (graphAxioms F).Model M) (hφ : φ.functionsIn ⊆ F)
    (v : α → M) (xs : Fin n → M) :
    φ.relationalize.Realize v xs ↔ @BoundedFormulaInf.Realize L ℕ α M
      (reconstructStructure L M) n φ v xs := by
  let := reconstructStructure L M
  refine (φ.relationalize.realize_congr_of_agreeOn _ (graphExpansion L M) (fun f => f.elim)
    ?_ v xs).trans (realize_relationalize φ v xs)
  intro k R hR ys
  rw [relationsIn_relationalize, relSym_def] at hR
  obtain ⟨⟨k, S⟩, -, hS⟩ | ⟨⟨k, g⟩, hg, hS⟩ := hR
  · rw [baseRelSym_mk] at hS
    cases hS
    exact ((graphExpansion_relMap_base S ys).trans (relMap_reconstructStructure S ys)).symm
  · rw [graphRelSym_mk] at hS
    cases hS
    exact (graphExpansion_reconstructStructure_relMap_graph hM (hφ hg) ys).symm

/-- **Round trip.** Reconstructing the graph expansion of an `L`-structure gives back the
structure. -/
@[simp]
theorem reconstructStructure_graphExpansion {M : Type w} [S : L.Structure M] [Nonempty M] :
    @reconstructStructure L M (graphExpansion L M) _ = S := by
  let := graphExpansion L M
  ext k f xs
  · rw [funMap_reconstructStructure_eq_iff (model_graphAxioms_iff.1
      (model_graphAxioms_graphExpansion L M Set.univ) ⟨k, f⟩ (Set.mem_univ _) xs)]
    simp
  · exact (relMap_reconstructStructure _ _).trans (graphExpansion_relMap_base _ _)

end Reconstruct

end Language

end FirstOrder
