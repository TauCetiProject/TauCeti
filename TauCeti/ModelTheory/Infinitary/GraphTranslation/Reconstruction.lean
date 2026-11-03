/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Infinitary.GraphTranslation.Relationalize
public import TauCeti.ModelTheory.Infinitary.Satisfiability

/-!
# Graph axioms and the reconstruction of a structure from its graph relations

A structure of the graph language `L.graphLanguage` interprets the graph relation `G_f` of each
function symbol `f` of `L` by an arbitrary relation. The **graph axioms** of a set `F` of function
symbols say that for `f ∈ F` this relation is the graph of a function: totality
`∀ xs ∃ y, G_f(xs, y)` (`graphTotality`) and functionality
`∀ xs y z, G_f(xs, y) → G_f(xs, z) → y = z` (`graphFunctionality`). For a countable `F` they form
one `L_{ω₁ω}` sentence `graphAxioms F hF`, the countable conjunction over `F`, and they hold in the
graph expansion of every `L`-structure.

Conversely, a nonempty structure of the graph language is read back as an `L`-structure
`reconstructStructure L M` on the same carrier: relation symbols of `L` are the base relations, and
`f(xs)` is a `y` with `G_f(xs, y)` when there is one (and an arbitrary element otherwise). When the
graph relations of the function symbols of a formula `φ` are graphs of functions, the translation
`φ.relationalize` holds in the graph structure exactly when `φ` holds in the reconstruction
(`BoundedFormulaInf.realize_relationalize_reconstructStructure`). The graph expansion of an
`L`-structure reconstructs to the structure itself (`reconstructStructure_graphExpansion`).

Together with the translation of `L`-structures into graph structures, this transfers entailment:
`φ ⊨ ψ` holds exactly when the graph axioms of the function symbols of `φ` together with the
translation of `φ` entail that the graph axioms of the function symbols of `ψ` imply the
translation of `ψ` (`Sentenceω.entails_iff_graphTranslation`). The graph language is relational,
so this is how entailments between sentences of an arbitrary language reach theorems proved for
relational languages, such as interpolation theorems.

## Main definitions

* `FirstOrder.Language.graphTotality`, `FirstOrder.Language.graphFunctionality`: totality and
  functionality of the graph relation of one function symbol.
* `FirstOrder.Language.graphAxioms`: the graph axioms of a countable set of function symbols.
* `FirstOrder.Language.reconstructStructure`: the `L`-structure read off a nonempty structure of
  the graph language.

## Main results

* `FirstOrder.Language.realize_graphAxioms`: the graph axioms of `F` hold exactly when, for every
  `f ∈ F`, the graph relation of `f` relates each argument tuple to exactly one value.
* `FirstOrder.Language.realize_graphAxioms_graphExpansion`: the graph expansion of an
  `L`-structure satisfies the graph axioms.
* `FirstOrder.Language.relationsIn_graphAxioms`: the graph axioms of `F` mention exactly the graph
  relations of the symbols in `F`.
* `FirstOrder.Language.BoundedFormulaInf.realize_relationalize_reconstructStructure`: on a graph
  structure whose graph relations for the function symbols of `φ` are graphs of functions, the
  translation of `φ` is realized exactly when `φ` is realized in the reconstruction.
* `FirstOrder.Language.Sentenceω.entails_iff_graphTranslation`: entailment between sentences of
  `L` is entailment between their translations into the graph language, relative to the graph
  axioms.

## References

* The graph axioms, the reconstruction and the transfer of entailment follow `graphTotality`,
  `graphFunctionality`, `graphAxioms`, `reconstructStructure`,
  `realize_relationalize_reconstruct` and `entails_graphTranslation` of
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`, in
  `InfinitaryLogic/Methods/Interpolation/GraphAxioms.lean`, `GraphReconstruction.lean` and
  `CraigArbitrary.lean`. Divergences from that source: languages and structures live in
  arbitrary universes; the reconstruction does not depend on `F` and needs only a nonempty
  carrier, while the realization theorem takes the semantic content of the graph axioms (each
  graph relation for a symbol of `φ` is the graph of a function) as its hypothesis, so it needs
  no countability of `F`; and the transfer of entailment is stated as an equivalence.
-/

public section

universe u v u' w

namespace FirstOrder

namespace Language

open BoundedFormulaInf Structure

variable {L : Language.{u, v}}

/-! ### The graph axioms -/

/-- **Totality** of the graph relation of a `k`-ary function symbol `f`:
`∀ x₀ … x_{k-1} ∃ y, G_f(x₀, …, x_{k-1}, y)`. -/
def graphTotality {k : ℕ} (f : L.Functions k) : L.graphLanguage.Sentenceω :=
  (BoundedFormulaInf.ex (rel (GraphRelation.graph f) fun i => Term.var (Sum.inr i))).alls

/-- **Functionality** of the graph relation of a `k`-ary function symbol `f`:
`∀ x₀ … x_{k-1} y z, G_f(x₀, …, x_{k-1}, y) → G_f(x₀, …, x_{k-1}, z) → y = z`. -/
def graphFunctionality {k : ℕ} (f : L.Functions k) : L.graphLanguage.Sentenceω :=
  let x : Fin k → L.graphLanguage.Term (Empty ⊕ Fin (k + 2)) := fun i =>
    Term.var (Sum.inr i.castSucc.castSucc)
  let y : L.graphLanguage.Term (Empty ⊕ Fin (k + 2)) := Term.var (Sum.inr (Fin.last k).castSucc)
  let z : L.graphLanguage.Term (Empty ⊕ Fin (k + 2)) := Term.var (Sum.inr (Fin.last (k + 1)))
  (((rel (GraphRelation.graph f) (Fin.snoc x y)).imp
      ((rel (GraphRelation.graph f) (Fin.snoc x z)).imp (equal y z))).all.all).alls

/-- The **graph axioms** of a countable set `F` of function symbols of `L`: totality and
functionality of the graph relation of every `f ∈ F`, joined by one countable conjunction along
`IndexCoding.ofEncodableWith`. For `F = ∅` it is the empty conjunction, which holds in every
structure. -/
noncomputable def graphAxioms (F : Set (Σ n, L.Functions n)) (hF : F.Countable) :
    L.graphLanguage.Sentenceω :=
  iInfAlong (TauCeti.IndexCoding.ofEncodableWith hF.toEncodable) fun f : F =>
    graphTotality f.1.2 ⊓ graphFunctionality f.1.2

/-- The graph axioms of `F` are the coded conjunction of totality and functionality of the graph
relations of the symbols in `F`. -/
theorem graphAxioms_def (F : Set (Σ n, L.Functions n)) (hF : F.Countable) :
    graphAxioms F hF = iInfAlong (TauCeti.IndexCoding.ofEncodableWith hF.toEncodable)
      fun f : F => graphTotality f.1.2 ⊓ graphFunctionality f.1.2 :=
  (rfl)

section Realize

variable {M : Type w} [L.graphLanguage.Structure M]

/-- Totality of the graph relation of `f` holds when every argument tuple is related to some
value. -/
@[simp]
theorem realize_graphTotality {k : ℕ} (f : L.Functions k) :
    SentenceInf.Realize (graphTotality f) M ↔
      ∀ xs : Fin k → M, ∃ y,
        RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y) := by
  simp only [graphTotality, SentenceInf.realize_def, FormulaInf.realize_def, realize_alls,
    realize_ex, realize_rel, Term.realize_var, Sum.elim_inr]

/-- Functionality of the graph relation of `f` holds when every argument tuple is related to at
most one value. -/
@[simp]
theorem realize_graphFunctionality {k : ℕ} (f : L.Functions k) :
    SentenceInf.Realize (graphFunctionality f) M ↔
      ∀ (xs : Fin k → M) (y z : M),
        RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y) →
        RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs z) → y = z := by
  simp only [graphFunctionality, SentenceInf.realize_def, FormulaInf.realize_def, realize_alls,
    realize_all, realize_imp, realize_rel, realize_equal, Term.realize_var, Sum.elim_inr]
  have h (xs : Fin k → M) (y z : M) (w : Fin (k + 2)) :
      (fun i => Term.realize
        (Sum.elim (Empty.elim : Empty → M) (Fin.snoc (Fin.snoc xs y) z : Fin (k + 2) → M))
        (Fin.snoc (α := fun _ => L.graphLanguage.Term (Empty ⊕ Fin (k + 2)))
          (fun i => Term.var (Sum.inr i.castSucc.castSucc)) (Term.var (Sum.inr w)) i)) =
        Fin.snoc xs ((Fin.snoc (Fin.snoc xs y) z : Fin (k + 2) → M) w) := by
    ext i
    induction i using Fin.lastCases <;> simp
  simp only [h, Fin.snoc_castSucc, Fin.snoc_last]

/-- **The graph axioms** of `F` hold exactly when, for every `f ∈ F`, the graph relation of `f`
relates each argument tuple to exactly one value. -/
@[simp]
theorem realize_graphAxioms (F : Set (Σ n, L.Functions n)) (hF : F.Countable) :
    SentenceInf.Realize (graphAxioms F hF) M ↔
      ∀ {k} (f : L.Functions k), ⟨k, f⟩ ∈ F → ∀ xs : Fin k → M,
        ∃! y, RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y) := by
  simp only [graphAxioms_def, SentenceInf.realize_def, FormulaInf.realize_def, realize_iInfAlong,
    realize_inf]
  simp only [← FormulaInf.realize_def, ← SentenceInf.realize_def, realize_graphTotality,
    realize_graphFunctionality, Subtype.forall, Sigma.forall]
  refine forall₂_congr fun k f => forall_congr' fun _ => ?_
  exact ⟨fun ⟨ht, hf⟩ xs => (ht xs).elim fun y hy => ⟨y, hy, fun z hz => hf xs z y hz hy⟩,
    fun h => ⟨fun xs => (h xs).exists, fun xs _ _ hy hz => (h xs).unique hy hz⟩⟩

end Realize

/-- The graph expansion of an `L`-structure satisfies the graph axioms of every countable set of
function symbols. -/
theorem realize_graphAxioms_graphExpansion (F : Set (Σ n, L.Functions n)) (hF : F.Countable)
    (M : Type w) [L.Structure M] :
    letI := graphExpansion L M
    SentenceInf.Realize (graphAxioms F hF) M := by
  let := graphExpansion L M
  rw [realize_graphAxioms]
  intro k f _ xs
  simp

/-- The graph axioms of `F` mention exactly the graph relations of the symbols in `F`. -/
@[simp]
theorem relationsIn_graphAxioms (F : Set (Σ n, L.Functions n)) (hF : F.Countable) :
    (graphAxioms F hF).relationsIn = graphRelSym '' F := by
  ext S
  simp [graphAxioms_def, graphTotality, graphFunctionality, eq_comm]

/-- No function symbol occurs in the graph axioms: the graph language has none. -/
@[simp]
theorem functionsIn_graphAxioms (F : Set (Σ n, L.Functions n)) (hF : F.Countable) :
    (graphAxioms F hF).functionsIn = ∅ :=
  Set.eq_empty_of_isEmpty _

/-! ### Reconstruction -/

section Reconstruct

variable (L) (M : Type w) [L.graphLanguage.Structure M] [Nonempty M]

/-- The `L`-structure **reconstructed** from a nonempty structure of the graph language: a relation
symbol of `L` is interpreted by its base relation, and a function symbol `f` sends `xs` to a `y`
with `G_f(xs, y)` when there is one (chosen by `Classical.epsilon`), and to an arbitrary element
otherwise. When the graph relation of `f` is the graph of a function, `f` is interpreted by that
function (`reconstructStructure_funMap_eq_iff`). -/
@[instance_reducible]
noncomputable def reconstructStructure : L.Structure M where
  funMap f xs := Classical.epsilon fun y =>
    RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y)
  RelMap R xs := RelMap (L := L.graphLanguage) (GraphRelation.base R) xs

variable {L M}

/-- A function symbol `f` is interpreted in the reconstruction by a value chosen, when one
exists, among those related to the arguments by the graph relation of `f`. -/
theorem reconstructStructure_funMap {k : ℕ} (f : L.Functions k) (xs : Fin k → M) :
    (reconstructStructure L M).funMap f xs =
      Classical.epsilon fun y =>
        RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y) :=
  (rfl)

/-- A relation symbol of `L` is interpreted in the reconstruction by its base relation. -/
@[simp]
theorem reconstructStructure_relMap {n : ℕ} (R : L.Relations n) (xs : Fin n → M) :
    (reconstructStructure L M).RelMap R xs ↔
      RelMap (L := L.graphLanguage) (GraphRelation.base R) xs :=
  Iff.rfl

/-- If the graph relation of `f` relates each argument tuple to exactly one value, the
reconstruction interprets `f` by this function. -/
theorem reconstructStructure_funMap_eq_iff {k : ℕ} {f : L.Functions k}
    (hf : ∀ xs : Fin k → M,
      ∃! y, RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y))
    (xs : Fin k → M) (y : M) :
    (reconstructStructure L M).funMap f xs = y ↔
      RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y) := by
  have h := Classical.epsilon_spec (hf xs).exists
  rw [reconstructStructure_funMap]
  exact ⟨fun hy => hy ▸ h, fun hy => (hf xs).unique h hy⟩

/-- The graph expansion of the reconstruction agrees with the graph structure on the graph relation
of every function symbol whose graph relation relates each argument tuple to exactly one value. -/
private theorem graphExpansion_reconstructStructure_relMap_graph {k : ℕ} {f : L.Functions k}
    (hf : ∀ xs : Fin k → M,
      ∃! y, RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y))
    (xs : Fin (k + 1) → M) :
    (@graphExpansion L M (reconstructStructure L M)).RelMap (GraphRelation.graph f) xs ↔
      RelMap (L := L.graphLanguage) (GraphRelation.graph f) xs := by
  let := reconstructStructure L M
  rw [graphExpansion_relMap_graph, reconstructStructure_funMap_eq_iff hf, Fin.snoc_init_self]

end Reconstruct

namespace BoundedFormulaInf

variable {α : Type u'} {M : Type w} [L.graphLanguage.Structure M] [Nonempty M] {n : ℕ}

/-- **Realization along the reconstruction**: if the graph relation of every function symbol of
`φ` relates each argument tuple to exactly one value, then the translation of `φ` into the graph
language is realized exactly when `φ` is realized in the reconstructed `L`-structure. -/
theorem realize_relationalize_reconstructStructure {F : Set (Σ n, L.Functions n)}
    (hF : ∀ {k} (f : L.Functions k), ⟨k, f⟩ ∈ F → ∀ xs : Fin k → M,
      ∃! y, RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y))
    (φ : L.BoundedFormulaω α n) (hφ : φ.functionsIn ⊆ F) (v : α → M) (xs : Fin n → M) :
    φ.relationalize.Realize v xs ↔ @Realize L ℕ α M (reconstructStructure L M) n φ v xs := by
  let := reconstructStructure L M
  refine Iff.trans ?_ (realize_relationalize φ v xs)
  refine realize_congr_of_agreeOn (L := L.graphLanguage) _ _ _ (fun f => PEmpty.elim f)
    (fun R hR xs => ?_) v xs
  rw [relationsIn_relationalize] at hR
  cases R with
  | base R => rw [graphExpansion_relMap_base, reconstructStructure_relMap]
  | graph f =>
    exact (graphExpansion_reconstructStructure_relMap_graph (hF f (hφ (by simpa using hR))) xs).symm

end BoundedFormulaInf

/-- The graph expansion of a nonempty `L`-structure reconstructs to the structure itself. -/
theorem reconstructStructure_graphExpansion (M : Type w) [S : L.Structure M] [Nonempty M] :
    @reconstructStructure L M (graphExpansion L M) _ = S := by
  let := graphExpansion L M
  ext k f xs
  · rw [reconstructStructure_funMap_eq_iff (fun xs => by simp), graphExpansion_relMap_graph,
      Fin.init_snoc, Fin.snoc_last]
  · rw [reconstructStructure_relMap, graphExpansion_relMap_base]

/-! ### Transfer of entailment -/

/-- **Entailment through the graph translation**: a sentence `φ` of `L` entails `ψ` exactly when,
in the graph language, the graph axioms of the function symbols of `φ` together with the
translation of `φ` entail that the graph axioms of the function symbols of `ψ` imply the
translation of `ψ`. -/
theorem Sentenceω.entails_iff_graphTranslation {φ ψ : L.Sentenceω} :
    φ.Entails ψ ↔
      Sentenceω.Entails (graphAxioms φ.functionsIn φ.functionsIn_countable ⊓ φ.relationalize)
        ((graphAxioms ψ.functionsIn ψ.functionsIn_countable).imp ψ.relationalize) := by
  simp only [Sentenceω.entails_iff, SentenceInf.realize_inf]
  constructor
  · intro h N _ _ ⟨hAφ, hφ⟩
    rw [realize_graphAxioms] at hAφ
    rw [SentenceInf.realize_def, FormulaInf.realize_def, realize_imp, ← FormulaInf.realize_def,
      ← SentenceInf.realize_def, realize_graphAxioms]
    intro hAψ
    have hU : ∀ {k} (f : L.Functions k), ⟨k, f⟩ ∈ φ.functionsIn ∪ ψ.functionsIn →
        ∀ xs : Fin k → N,
          ∃! y, RelMap (L := L.graphLanguage) (GraphRelation.graph f) (Fin.snoc xs y) :=
      fun f hf => hf.elim (hAφ f) (hAψ f)
    rw [SentenceInf.realize_def, FormulaInf.realize_def,
      realize_relationalize_reconstructStructure hU _ Set.subset_union_left] at hφ
    let := reconstructStructure L N
    have hψ := h N (by rwa [SentenceInf.realize_def, FormulaInf.realize_def])
    rwa [SentenceInf.realize_def, FormulaInf.realize_def,
      ← realize_relationalize_reconstructStructure hU _ Set.subset_union_right] at hψ
  · intro h M _ _ hφ
    let := graphExpansion L M
    have hA (F : Set (Σ n, L.Functions n)) (hF : F.Countable) :
        Realize (graphAxioms F hF) (Empty.elim : Empty → M) default := by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def] using
        realize_graphAxioms_graphExpansion F hF M
    have hψ := h M ⟨realize_graphAxioms_graphExpansion _ _ M, by
      simpa only [SentenceInf.realize_def, FormulaInf.realize_def, realize_relationalize] using hφ⟩
    simp only [SentenceInf.realize_def, FormulaInf.realize_def, realize_imp,
      realize_relationalize] at hψ ⊢
    exact hψ (hA _ _)

end Language

end FirstOrder
