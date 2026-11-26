/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.SimpleGraph
public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass
public import TauCeti.Order.RelCovBy

/-!
# Marked trees and the cover graph of a coded order

Trees are presented in two ways in the proof that trees are Borel complete: as partial orders
(`TauCeti.RelationalConfiguration.treeClass`), and as connected acyclic graphs with one marked
vertex, the root. This file sets up the second presentation, and defines the cover-graph map
from coded orders to codes of marked graphs. That this map sends `treeClass` into
`markedTreeClass` is not proved here.

The language `markedGraphLanguage` has a binary symbol `adj` and a unary symbol `mark`. A code
`c` on a carrier `V` gives the relation `codeRel .adj c` and the predicate `IsMarked c`. The
class `markedTreeClass` consists of the codes whose relation is symmetric and irreflexive, whose
graph `markedGraph c` is a tree (Mathlib's `SimpleGraph.IsTree`: connected and acyclic), and
which mark exactly one vertex. It is isomorphism invariant, and on a countable carrier it is
Borel: the graph depends measurably on the code (`measurable_markedGraph`), and being a tree is
a measurable set of graphs (`TauCeti.measurableSet_setOf_isTree`).

The cover graph of a coded order `c` (`coverGraphCode c`) joins `u` and `v` when one covers the
other, and marks the least elements. Each of its coordinates is the indicator of a closed set of
codes (a cover relation is a countable intersection of conditions on finitely many coordinates),
so the map is measurable. It commutes with relabelling, so it sends isomorphic codes to isomorphic
codes.

## Main definitions

* `TauCeti.RelationalConfiguration.markedGraphLanguage`: one binary and one unary symbol.
* `TauCeti.RelationalConfiguration.markedTreeClass`: the codes of connected acyclic graphs with
  exactly one marked vertex.
* `TauCeti.RelationalConfiguration.coverGraphCode`: the cover graph of a coded order, with its
  least elements marked.

## Main results

* `TauCeti.RelationalConfiguration.Atom.induction_markedGraph`,
  `TauCeti.RelationalConfiguration.ext_markedGraph`: atoms are adjacency or marking atoms, so a
  code is determined by its relation and its marked vertices.
* `TauCeti.RelationalConfiguration.isomorphismInvariant_markedTreeClass`,
  `TauCeti.RelationalConfiguration.measurableSet_markedTreeClass`: the class is invariant Borel.
* `TauCeti.RelationalConfiguration.measurable_coverGraphCode`: the cover-graph map is measurable.
* `TauCeti.RelationalConfiguration.coverGraphCode_perm_smul`,
  `TauCeti.RelationalConfiguration.isoSetoid_coverGraphCode`: it commutes with relabelling and
  preserves isomorphism.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), §2.
-/

public section

open FirstOrder FirstOrder.Language Set

namespace TauCeti

namespace RelationalConfiguration

variable {V : Type*}

/-! ### The language of marked graphs -/

/-- The relation symbols of the language of marked graphs: a binary symbol `adj` and a unary
symbol `mark`. -/
inductive MarkedGraphRel : ℕ → Type
  | adj : MarkedGraphRel 2
  | mark : MarkedGraphRel 1

/-- The relational language of marked graphs, with a binary symbol `adj` and a unary symbol
`mark`. -/
@[expose] def markedGraphLanguage : Language := ⟨fun _ => Empty, MarkedGraphRel⟩
  deriving IsRelational

/-- The language of marked graphs has finitely many relation symbols. -/
instance instCountableMarkedGraphLanguageRelations :
    Countable (Σ k, markedGraphLanguage.Relations k) := by
  refine Function.Surjective.countable
    (f := fun b : Bool => if b then (⟨2, .adj⟩ : Σ k, markedGraphLanguage.Relations k)
      else ⟨1, .mark⟩) ?_
  rintro ⟨_, ⟨⟩⟩
  exacts [⟨true, rfl⟩, ⟨false, rfl⟩]

/-- The adjacency symbol of the language of marked graphs. -/
abbrev adjSymb : markedGraphLanguage.Relations 2 := MarkedGraphRel.adj

/-- The marking symbol of the language of marked graphs. -/
abbrev markSymb : markedGraphLanguage.Relations 1 := MarkedGraphRel.mark

/-- A vertex is **marked** by a code of the language of marked graphs. -/
def IsMarked (c : RelationalConfiguration markedGraphLanguage V) (v : V) : Prop :=
  c.eval (atom markSymb ![v]) = true

/-- Unfolding lemma for `IsMarked`. -/
theorem isMarked_iff {c : RelationalConfiguration markedGraphLanguage V} {v : V} :
    IsMarked c v ↔ c.eval (atom markSymb ![v]) = true :=
  Iff.rfl

/-- The code of a structure marks the vertices that satisfy `mark` in that structure. -/
@[simp]
theorem isMarked_ofStructure [markedGraphLanguage.Structure V] (v : V) :
    IsMarked (ofStructure markedGraphLanguage V) v ↔ Structure.RelMap markSymb ![v] := by
  classical
  rw [isMarked_iff, eval_ofStructure, decide_eq_true_iff]

/-- Each instance of the marking predicate is a measurable condition on codes. -/
@[measurability]
theorem measurableSet_setOf_isMarked (v : V) :
    MeasurableSet {c : RelationalConfiguration markedGraphLanguage V | IsMarked c v} := by
  simpa only [isMarked_iff] using measurableSet_setOf_eval (atom markSymb ![v]) true

/-- Relabelling a code by `σ` transports its marked vertices along `σ`. -/
@[simp]
theorem isMarked_perm_smul (σ : Equiv.Perm V) (c : RelationalConfiguration markedGraphLanguage V)
    (v : V) : IsMarked (σ • c) v ↔ IsMarked c (σ.symm v) := by
  have h : (σ.symm ∘ ![v] : Fin 1 → V) = ![σ.symm v] := by
    ext i
    fin_cases i
    rfl
  rw [isMarked_iff, isMarked_iff, eval_perm_smul, Atom.map_atom, h]

/-- The simple graph of a code of the language of marked graphs: `u` and `v` are adjacent when
they are distinct and one is related to the other. On `markedTreeClass` the relation is already
symmetric and irreflexive, and this is its graph. -/
def markedGraph (c : RelationalConfiguration markedGraphLanguage V) : SimpleGraph V :=
  SimpleGraph.fromRel (codeRel adjSymb c)

/-- Adjacency in the graph of a code. -/
@[simp]
theorem markedGraph_adj {c : RelationalConfiguration markedGraphLanguage V} {u v : V} :
    (markedGraph c).Adj u v ↔ u ≠ v ∧ (codeRel adjSymb c u v ∨ codeRel adjSymb c v u) :=
  SimpleGraph.fromRel_adj _ _ _

/-- When the relation of a code is symmetric and irreflexive, as on `markedTreeClass`, adjacency
in its graph is the relation itself. -/
theorem markedGraph_adj_iff_codeRel {c : RelationalConfiguration markedGraphLanguage V}
    (hsymm : ∀ u v, codeRel adjSymb c u v → codeRel adjSymb c v u)
    (hirr : ∀ v, ¬ codeRel adjSymb c v v) {u v : V} :
    (markedGraph c).Adj u v ↔ codeRel adjSymb c u v := by
  rw [markedGraph_adj]
  refine ⟨fun ⟨_, h⟩ => h.elim id (hsymm v u), fun h => ⟨?_, .inl h⟩⟩
  rintro rfl
  exact hirr u h

/-- Relabelling a code by `σ` relabels its graph: `σ` is an isomorphism from the graph of `c` to
that of `σ • c`. -/
def markedGraphIsoPermSmul (σ : Equiv.Perm V) (c : RelationalConfiguration markedGraphLanguage V) :
    markedGraph c ≃g markedGraph (σ • c) where
  toEquiv := σ
  map_rel_iff' {u v} := by simp

/-- The graph isomorphism `markedGraphIsoPermSmul σ c` acts on vertices as `σ`. -/
@[simp]
theorem markedGraphIsoPermSmul_apply (σ : Equiv.Perm V)
    (c : RelationalConfiguration markedGraphLanguage V) (v : V) :
    markedGraphIsoPermSmul σ c v = σ v :=
  (rfl)

/-- The inverse of `markedGraphIsoPermSmul σ c` acts on vertices as `σ.symm`. -/
@[simp]
theorem markedGraphIsoPermSmul_symm_apply (σ : Equiv.Perm V)
    (c : RelationalConfiguration markedGraphLanguage V) (v : V) :
    (markedGraphIsoPermSmul σ c).symm v = σ.symm v :=
  (rfl)

/-- Every atom of the language of marked graphs is an adjacency atom `adj(u, v)` or a marking
atom `mark(v)`. -/
@[elab_as_elim]
theorem Atom.induction_markedGraph {motive : Atom markedGraphLanguage V → Prop}
    (adj : ∀ u v : V, motive (atom adjSymb ![u, v])) (mark : ∀ v : V, motive (atom markSymb ![v]))
    (a : Atom markedGraphLanguage V) : motive a := by
  induction a using Atom.induction_atom with
  | h R x =>
    cases R with
    | adj =>
      have hx : x = ![x 0, x 1] := by
        funext i
        fin_cases i <;> rfl
      rw [hx]
      exact adj (x 0) (x 1)
    | mark =>
      have hx : x = ![x 0] := by
        funext i
        fin_cases i
        rfl
      rw [hx]
      exact mark (x 0)

/-- Two codes of the language of marked graphs are equal when they have the same relation and
mark the same vertices. -/
theorem ext_markedGraph {c d : RelationalConfiguration markedGraphLanguage V}
    (hadj : ∀ u v, codeRel adjSymb c u v ↔ codeRel adjSymb d u v)
    (hmark : ∀ v, IsMarked c v ↔ IsMarked d v) : c = d := by
  refine ext fun a => ?_
  induction a using Atom.induction_markedGraph with
  | adj u v => rw [Bool.eq_iff_iff, ← codeRel_iff, ← codeRel_iff, hadj]
  | mark v => rw [Bool.eq_iff_iff, ← isMarked_iff, ← isMarked_iff, hmark]

/-! ### Marked trees -/

/-- The **marked trees**: the codes whose relation is symmetric and irreflexive, whose graph is a
tree (connected and acyclic), and which mark exactly one vertex. -/
def markedTreeClass : Set (RelationalConfiguration markedGraphLanguage V) :=
  {c | (∀ u v, codeRel adjSymb c u v → codeRel adjSymb c v u) ∧
    (∀ v, ¬ codeRel adjSymb c v v) ∧
    (markedGraph c).IsTree ∧ ∃! v, IsMarked c v}

/-- Unfolding lemma for `markedTreeClass`. -/
theorem mem_markedTreeClass {c : RelationalConfiguration markedGraphLanguage V} :
    c ∈ markedTreeClass ↔ (∀ u v, codeRel adjSymb c u v → codeRel adjSymb c v u) ∧
    (∀ v, ¬ codeRel adjSymb c v v) ∧
      (markedGraph c).IsTree ∧ ∃! v, IsMarked c v :=
  Iff.rfl

/-- The marked trees form an isomorphism-invariant class. -/
theorem isomorphismInvariant_markedTreeClass :
    IsomorphismInvariant (markedTreeClass (V := V)) := by
  refine isomorphismInvariant_iff.2 fun c d hcd hc => ?_
  obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 hcd
  obtain ⟨hsymm, hirr, htree, v, hv, huniq⟩ := hc
  refine ⟨fun x y h => ?_, fun x h => ?_, (markedGraphIsoPermSmul σ c).isTree_iff.1 htree,
    σ v, by simpa using hv, fun w hw => ?_⟩
  · rw [codeRel_perm_smul] at h ⊢
    exact hsymm _ _ h
  · rw [codeRel_perm_smul] at h
    exact hirr _ h
  · have hw' : IsMarked c (σ.symm w) := (isMarked_perm_smul σ c w).1 hw
    simpa using congrArg σ (huniq _ hw')

section Measurable

/-- The graph of a code depends measurably on the code. -/
theorem measurable_markedGraph :
    Measurable (markedGraph : RelationalConfiguration markedGraphLanguage V → SimpleGraph V) := by
  refine SimpleGraph.measurable_iff_adj.2 fun x y => measurableSet_setOfPred.1 ?_
  simp only [markedGraph_adj, ofPred_and, ofPred_or]
  exact (MeasurableSet.const _).inter
    ((measurableSet_setOf_codeRel adjSymb x y).union (measurableSet_setOf_codeRel adjSymb y x))

variable [Countable V]

/-- On a countable carrier the marked trees form a Borel class. -/
theorem measurableSet_markedTreeClass : MeasurableSet (markedTreeClass (V := V)) := by
  classical
  have hE := measurableSet_setOf_codeRel (V := V) adjSymb
  have hM := measurableSet_setOf_isMarked (V := V)
  have hU : {c : RelationalConfiguration markedGraphLanguage V | ∃! v, IsMarked c v} =
      ⋃ v, {c | IsMarked c v} ∩ ⋂ w, ⋂ (_ : w ≠ v), {c | IsMarked c w}ᶜ := by
    ext c
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_iInter, mem_compl_iff]
    exact exists_congr fun v => and_congr_right fun _ =>
      ⟨fun h w hw hm => hw (h w hm), fun h w hm => by_contra fun hw => h w hw hm⟩
  have hSymm : MeasurableSet {c : RelationalConfiguration markedGraphLanguage V |
      ∀ u v, codeRel adjSymb c u v → codeRel adjSymb c v u} := by
    simp only [ofPred_forall, ← compl_ofPred, imp_iff_not_or, ofPred_or]
    exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
      (hE x y).compl.union (hE y x)
  have hIrr : MeasurableSet {c : RelationalConfiguration markedGraphLanguage V |
      ∀ v, ¬ codeRel adjSymb c v v} := by
    simp only [ofPred_forall, ← compl_ofPred]
    exact MeasurableSet.iInter fun x => (hE x x).compl
  have : markedTreeClass (V := V) =
      {c | ∀ u v, codeRel adjSymb c u v → codeRel adjSymb c v u} ∩
      ({c | ∀ v, ¬ codeRel adjSymb c v v} ∩
        ({c | (markedGraph c).IsTree} ∩ {c | ∃! v, IsMarked c v})) := by
    ext c
    rfl
  rw [this, hU]
  have hUm := MeasurableSet.iUnion fun v => (hM v).inter
    (MeasurableSet.iInter fun w => MeasurableSet.iInter fun (_ : w ≠ v) => (hM w).compl)
  exact hSymm.inter (hIrr.inter
    ((measurableSet_setOf_isTree.preimage measurable_markedGraph).inter hUm))

end Measurable

/-! ### The cover graph of a coded order -/

/-- In the code of a preorder, `RelCovBy` for the relation of `leSymb` is Mathlib's `CovBy`. -/
theorem relCovBy_codeRel_leSymb_ofStructure_orderStructure {α : Type*} [Preorder α] {u v : α} :
    RelCovBy (codeRel leSymb (@ofStructure Language.order α (orderStructure α))) u v ↔ u ⋖ v := by
  rw [codeRel_leSymb_ofStructure_orderStructure, relCovBy_le_iff_covBy]

/-- The marked graph of a relation `r` read as an order: `u` and `v` are related when one
covers the other, and the least elements, those below every element, are marked. -/
@[instance_reducible]
def coverStructure (r : V → V → Prop) : markedGraphLanguage.Structure V where
  RelMap
    | .adj => fun x => RelCovBy r (x 0) (x 1) ∨ RelCovBy r (x 1) (x 0)
    | .mark => fun x => ∀ w, r (x 0) w

/-- The adjacency relation of `coverStructure r`: one entry covers the other. -/
theorem coverStructure_relMap_adj (r : V → V → Prop) (x : Fin 2 → V) :
    @Structure.RelMap markedGraphLanguage V (coverStructure r) 2 adjSymb x ↔
      RelCovBy r (x 0) (x 1) ∨ RelCovBy r (x 1) (x 0) :=
  -- The `adj` branch of the pattern match defining `coverStructure`.
  Iff.rfl

/-- The marking predicate of `coverStructure r`: the entry lies below every element. -/
theorem coverStructure_relMap_mark (r : V → V → Prop) (x : Fin 1 → V) :
    @Structure.RelMap markedGraphLanguage V (coverStructure r) 1 markSymb x ↔ ∀ w, r (x 0) w :=
  -- The `mark` branch of the pattern match defining `coverStructure`.
  Iff.rfl

/-- The **cover graph** of a coded order `c`, with its least elements marked: the code of
`coverStructure (codeRel leSymb c)`. -/
noncomputable def coverGraphCode (c : RelationalConfiguration Language.order V) :
    RelationalConfiguration markedGraphLanguage V :=
  @ofStructure markedGraphLanguage V (coverStructure (codeRel leSymb c))

/-- The cover graph relates `u` and `v` when one covers the other. -/
@[simp]
theorem codeRel_coverGraphCode (c : RelationalConfiguration Language.order V) (u v : V) :
    codeRel adjSymb (coverGraphCode c) u v ↔
      RelCovBy (codeRel leSymb c) u v ∨ RelCovBy (codeRel leSymb c) v u := by
  rw [coverGraphCode, @codeRel_ofStructure _ _ (coverStructure _), coverStructure_relMap_adj,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]

/-- The cover graph marks the least elements. -/
@[simp]
theorem isMarked_coverGraphCode (c : RelationalConfiguration Language.order V) (v : V) :
    IsMarked (coverGraphCode c) v ↔ ∀ w, codeRel leSymb c v w := by
  rw [coverGraphCode, @isMarked_ofStructure _ (coverStructure _), coverStructure_relMap_mark,
    Matrix.cons_val_fin_one]

/-- **The cover-graph map is measurable** on a countable carrier: each adjacency coordinate is
the indicator of a closed set of codes, a countable intersection of conditions on finitely many
coordinates, and so is each marking coordinate. -/
theorem measurable_coverGraphCode [Countable V] :
    Measurable (coverGraphCode : RelationalConfiguration Language.order V → _) := by
  classical
  have hE := measurableSet_setOf_codeRel (L := Language.order) (V := V) leSymb
  have hlt (x y : V) : MeasurableSet {c : RelationalConfiguration Language.order V |
      codeRel leSymb c x y ∧ ¬ codeRel leSymb c y x} :=
    (hE x y).inter (hE y x).compl
  have hC (x y : V) : MeasurableSet {c : RelationalConfiguration Language.order V |
      RelCovBy (codeRel leSymb c) x y} := by
    simp only [relCovBy_iff, ofPred_and, ofPred_forall]
    exact (hlt x y).inter (MeasurableSet.iInter fun w => ((hlt x w).inter (hlt w y)).compl)
  refine measurable_iff.2 fun a => measurable_to_bool ?_
  induction a using Atom.induction_markedGraph with
  | adj x y =>
    simp only [preimage, mem_singleton_iff, ← codeRel_iff, codeRel_coverGraphCode, ofPred_or]
    exact (hC x y).union (hC y x)
  | mark x =>
    simp only [preimage, mem_singleton_iff, ← isMarked_iff, isMarked_coverGraphCode, ofPred_forall]
    exact MeasurableSet.iInter fun w => hE x w

/-- **The cover-graph map commutes with relabelling.** -/
theorem coverGraphCode_perm_smul (σ : Equiv.Perm V) (c : RelationalConfiguration Language.order V) :
    coverGraphCode (σ • c) = σ • coverGraphCode c := by
  refine ext_markedGraph (fun x y => ?_) fun x => ?_
  · have h : codeRel leSymb (σ • c) = fun a b => codeRel leSymb c (σ.symm a) (σ.symm b) := by
      ext a b
      exact codeRel_perm_smul leSymb σ c a b
    rw [codeRel_perm_smul, codeRel_coverGraphCode, codeRel_coverGraphCode, h,
      relCovBy_comap_equiv, relCovBy_comap_equiv]
  · rw [isMarked_perm_smul, isMarked_coverGraphCode, isMarked_coverGraphCode]
    simp only [codeRel_perm_smul]
    exact ⟨fun h w => by simpa using h (σ w), fun h w => h (σ.symm w)⟩

/-- **The cover-graph map preserves isomorphism.** -/
theorem isoSetoid_coverGraphCode {c d : RelationalConfiguration Language.order V}
    (h : isoSetoid Language.order V c d) :
    isoSetoid markedGraphLanguage V (coverGraphCode c) (coverGraphCode d) := by
  obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
  rw [coverGraphCode_perm_smul]
  exact isoSetoid_perm_smul σ _

end RelationalConfiguration

end TauCeti
