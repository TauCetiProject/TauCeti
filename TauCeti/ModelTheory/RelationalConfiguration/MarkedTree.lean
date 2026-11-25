/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.ModelTheory.RelationalConfiguration.OrderClass

/-!
# Marked trees and the cover graph of a coded tree

Trees are presented in two ways in the proof that trees are Borel complete: as partial orders
(`TauCeti.RelationalConfiguration.treeClass`), and as connected acyclic graphs with one marked
vertex, the root. This file sets up the second presentation and the map between the two.

The language `markedGraphLanguage` has a binary symbol `adj` and a unary symbol `mark`. A code
`c` on a carrier `V` gives the relation `codeRel .adj c` and the predicate `IsMarked c`. The
class `markedTreeClass` consists of the codes whose relation is symmetric and irreflexive, whose
graph `markedGraph c` is a tree (Mathlib's `SimpleGraph.IsTree`: connected and acyclic), and
which mark exactly one vertex. It is isomorphism invariant, and on a countable carrier it is
Borel: connectedness is a countable intersection of reachability conditions, each a countable
union over finite paths, and acyclicity says that every edge is a bridge, a reachability
condition in the graph with that edge deleted.

The cover graph of a coded order `c` (`coverGraphCode c`) joins `u` and `v` when one covers the
other, and marks the least elements. Each of its coordinates is the indicator of a closed set of
codes (a cover relation is a countable intersection of conditions on finitely many coordinates),
so the map is measurable; it is not continuous, even on coded trees. It commutes with relabelling,
so it sends isomorphic codes to isomorphic codes.

## Main definitions

* `TauCeti.RelationalConfiguration.markedGraphLanguage`: one binary and one unary symbol.
* `TauCeti.RelationalConfiguration.markedTreeClass`: the codes of connected acyclic graphs with
  exactly one marked vertex.
* `TauCeti.RelationalConfiguration.coverGraphCode`: the cover graph of a coded order, with its
  least elements marked.

## Main results

* `TauCeti.measurableSet_setOf_reflTransGen`: reachability along a measurable family of relations
  on a countable type is measurable.
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

section Reachability

variable {α V : Type*} [MeasurableSpace α] {R : α → V → V → Prop}

/-- Being a chain along a fixed finite list is measurable in a measurable family of relations. -/
theorem measurableSet_setOf_isChain (hR : ∀ a b, MeasurableSet {x | R x a b}) :
    ∀ l : List V, MeasurableSet {x | List.IsChain (R x) l}
  | [] => by simp
  | [_] => by simp
  | a :: b :: l => by
    simp only [List.isChain_cons_cons, ofPred_and]
    exact (hR a b).inter (measurableSet_setOf_isChain hR (b :: l))

/-- **Reachability is measurable.** For a family of relations on a countable type, each of whose
instances is a measurable condition, reachability along the relation is measurable: it is a
countable union over the finite paths. -/
theorem measurableSet_setOf_reflTransGen [Countable V] (hR : ∀ a b, MeasurableSet {x | R x a b})
    (u v : V) : MeasurableSet {x | Relation.ReflTransGen (R x) u v} := by
  have h : {x | Relation.ReflTransGen (R x) u v} = ⋃ l : List V,
      {x | List.IsChain (R x) (u :: l)} ∩ {_x | (u :: l).getLast (List.cons_ne_nil _ _) = v} := by
    ext x
    simp only [mem_ofPred_eq, mem_iUnion, mem_inter_iff]
    exact ⟨List.exists_isChain_cons_of_relationReflTransGen,
      fun ⟨l, hl, hv⟩ ↦ List.relationReflTransGen_of_exists_isChain_cons l hl hv⟩
  rw [h]
  exact MeasurableSet.iUnion fun l ↦
    (measurableSet_setOf_isChain hR _).inter (MeasurableSet.const _)

end Reachability

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

/-- Relabelling a code by `σ` relabels its graph: `σ` is an isomorphism from the graph of `c` to
that of `σ • c`. -/
def markedGraphIsoPermSmul (σ : Equiv.Perm V) (c : RelationalConfiguration markedGraphLanguage V) :
    markedGraph c ≃g markedGraph (σ • c) where
  toEquiv := σ
  map_rel_iff' {u v} := by simp

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

private theorem measurableSet_setOf_codeRel_adjSymb (x y : V) :
    MeasurableSet {c : RelationalConfiguration markedGraphLanguage V | codeRel adjSymb c x y} := by
  simpa only [codeRel_iff] using measurableSet_setOf_eval (atom adjSymb ![x, y]) true

private theorem measurableSet_setOf_isMarked (v : V) :
    MeasurableSet {c : RelationalConfiguration markedGraphLanguage V | IsMarked c v} := by
  simpa only [isMarked_iff] using measurableSet_setOf_eval (atom markSymb ![v]) true

private theorem measurableSet_setOf_markedGraph_adj (x y : V) :
    MeasurableSet {c : RelationalConfiguration markedGraphLanguage V |
      (markedGraph c).Adj x y} := by
  simp only [markedGraph_adj, ofPred_and, ofPred_or]
  exact (MeasurableSet.const _).inter
    ((measurableSet_setOf_codeRel_adjSymb x y).union (measurableSet_setOf_codeRel_adjSymb y x))

variable [Countable V]

/-- Being a tree is a Borel condition on the codes: connectedness is reachability between every
two vertices, and acyclicity says that every edge is a bridge. -/
private theorem measurableSet_setOf_isTree :
    MeasurableSet {c : RelationalConfiguration markedGraphLanguage V | (markedGraph c).IsTree} := by
  have hA := measurableSet_setOf_markedGraph_adj (V := V)
  have hR (u v : V) : MeasurableSet {c : RelationalConfiguration markedGraphLanguage V |
      (markedGraph c).Reachable u v} := by
    simp only [SimpleGraph.reachable_iff_reflTransGen]
    exact measurableSet_setOf_reflTransGen hA u v
  have hB (x y : V) : MeasurableSet {c : RelationalConfiguration markedGraphLanguage V |
      ((markedGraph c).deleteEdges {s(x, y)}).Reachable x y} := by
    simp only [SimpleGraph.reachable_iff_reflTransGen]
    refine measurableSet_setOf_reflTransGen (fun a b => ?_) x y
    simp only [SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff, ofPred_and]
    exact (hA a b).inter (MeasurableSet.const _)
  have hT : {c : RelationalConfiguration markedGraphLanguage V | (markedGraph c).IsTree} =
      {_c | Nonempty V} ∩ (⋂ u, ⋂ v, {c | (markedGraph c).Reachable u v}) ∩
        ⋂ x, ⋂ y, {c | (markedGraph c).Adj x y}ᶜ ∪
          {c | ((markedGraph c).deleteEdges {s(x, y)}).Reachable x y}ᶜ := by
    ext c
    simp only [mem_ofPred_eq, mem_inter_iff, mem_iInter, mem_union, mem_compl_iff,
      SimpleGraph.isTree_iff, SimpleGraph.connected_iff,
      SimpleGraph.isAcyclic_iff_forall_adj_isBridge, SimpleGraph.isBridge_iff,
      SimpleGraph.Preconnected, imp_iff_not_or]
    tauto
  rw [hT]
  exact ((MeasurableSet.const (Nonempty V)).inter
    (MeasurableSet.iInter fun u => MeasurableSet.iInter fun v => hR u v)).inter
      (MeasurableSet.iInter fun x => MeasurableSet.iInter fun y =>
        (hA x y).compl.union (hB x y).compl)

/-- On a countable carrier the marked trees form a Borel class. -/
theorem measurableSet_markedTreeClass : MeasurableSet (markedTreeClass (V := V)) := by
  classical
  have hE := measurableSet_setOf_codeRel_adjSymb (V := V)
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
  exact hSymm.inter (hIrr.inter (measurableSet_setOf_isTree.inter hUm))

end Measurable

/-! ### The cover graph of a coded order -/

/-- In a relation `r` read as a non-strict order, `v` **covers** `u`: `u < v`, and no `w`
satisfies `u < w < v`, where `a < b` means `r a b` and not `r b a`. -/
def Covers (r : V → V → Prop) (u v : V) : Prop :=
  (r u v ∧ ¬ r v u) ∧ ∀ w, ¬ ((r u w ∧ ¬ r w u) ∧ (r w v ∧ ¬ r v w))

/-- Unfolding lemma for `Covers`. -/
theorem covers_iff {r : V → V → Prop} {u v : V} :
    Covers r u v ↔ (r u v ∧ ¬ r v u) ∧ ∀ w, ¬ ((r u w ∧ ¬ r w u) ∧ (r w v ∧ ¬ r v w)) :=
  Iff.rfl

/-- The marked graph of a relation `r` read as an order: `u` and `v` are related when one
covers the other, and the least elements, those below every element, are marked. -/
@[instance_reducible]
def coverStructure (r : V → V → Prop) : markedGraphLanguage.Structure V where
  RelMap
    | .adj => fun x => Covers r (x 0) (x 1) ∨ Covers r (x 1) (x 0)
    | .mark => fun x => ∀ w, r (x 0) w

/-- The **cover graph** of a coded order `c`, with its least elements marked: the code of
`coverStructure (codeRel leSymb c)`. -/
noncomputable def coverGraphCode (c : RelationalConfiguration Language.order V) :
    RelationalConfiguration markedGraphLanguage V :=
  @ofStructure markedGraphLanguage V (coverStructure (codeRel leSymb c))

/-- The cover graph relates `u` and `v` when one covers the other. -/
@[simp]
theorem codeRel_coverGraphCode (c : RelationalConfiguration Language.order V) (u v : V) :
    codeRel adjSymb (coverGraphCode c) u v ↔
      Covers (codeRel leSymb c) u v ∨ Covers (codeRel leSymb c) v u := by
  rw [coverGraphCode, @codeRel_ofStructure _ _ (coverStructure _)]
  rfl

/-- The cover graph marks the least elements. -/
@[simp]
theorem isMarked_coverGraphCode (c : RelationalConfiguration Language.order V) (v : V) :
    IsMarked (coverGraphCode c) v ↔ ∀ w, codeRel leSymb c v w := by
  classical
  rw [isMarked_iff, coverGraphCode, @eval_ofStructure _ _ (coverStructure _), decide_eq_true_iff]
  rfl

/-- Every atom of the language of marked graphs is an adjacency atom or a marking atom. -/
private theorem atom_cases (a : Atom markedGraphLanguage V) :
    (∃ x y, a = atom adjSymb ![x, y]) ∨ ∃ x, a = atom markSymb ![x] := by
  induction a using Atom.induction_atom with
  | h R x =>
    cases R with
    | adj => exact .inl ⟨x 0, x 1, by congr 1; ext i; fin_cases i <;> rfl⟩
    | mark => exact .inr ⟨x 0, by congr 1; ext i; fin_cases i; rfl⟩

/-- **The cover-graph map is measurable** on a countable carrier: each adjacency coordinate is
the indicator of a closed set of codes, a countable intersection of conditions on finitely many
coordinates, and so is each marking coordinate. -/
theorem measurable_coverGraphCode [Countable V] :
    Measurable (coverGraphCode : RelationalConfiguration Language.order V → _) := by
  classical
  have hE (x y : V) : MeasurableSet {c : RelationalConfiguration Language.order V |
      codeRel leSymb c x y} := by
    simpa only [codeRel_iff] using measurableSet_setOf_eval (atom leSymb ![x, y]) true
  have hlt (x y : V) : MeasurableSet {c : RelationalConfiguration Language.order V |
      codeRel leSymb c x y ∧ ¬ codeRel leSymb c y x} :=
    (hE x y).inter (hE y x).compl
  have hC (x y : V) : MeasurableSet {c : RelationalConfiguration Language.order V |
      Covers (codeRel leSymb c) x y} := by
    simp only [covers_iff, ofPred_and, ofPred_forall]
    exact (hlt x y).inter (MeasurableSet.iInter fun w => ((hlt x w).inter (hlt w y)).compl)
  refine measurable_iff.2 fun a => measurable_to_bool ?_
  rcases atom_cases a with ⟨x, y, rfl⟩ | ⟨x, rfl⟩
  · have h := (hC x y).union (hC y x)
    simp only [← codeRel_coverGraphCode, ← ofPred_or, codeRel_iff] at h
    simpa only [preimage, mem_singleton_iff] using h
  · have h := MeasurableSet.iInter fun w => hE x w
    simp only [← ofPred_forall, ← isMarked_coverGraphCode, isMarked_iff] at h
    simpa only [preimage, mem_singleton_iff] using h

/-- **The cover-graph map commutes with relabelling.** -/
theorem coverGraphCode_perm_smul (σ : Equiv.Perm V) (c : RelationalConfiguration Language.order V) :
    coverGraphCode (σ • c) = σ • coverGraphCode c := by
  refine ext fun a => ?_
  rcases atom_cases a with ⟨x, y, rfl⟩ | ⟨x, rfl⟩
  · rw [Bool.eq_iff_iff, ← codeRel_iff, ← codeRel_iff, codeRel_perm_smul, codeRel_coverGraphCode,
      codeRel_coverGraphCode]
    simp only [covers_iff, codeRel_perm_smul]
    refine or_congr (and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩)
      (and_congr Iff.rfl ⟨fun h w => ?_, fun h w => ?_⟩)
    · simpa using h (σ w)
    · simpa using h (σ.symm w)
    · simpa using h (σ w)
    · simpa using h (σ.symm w)
  · rw [Bool.eq_iff_iff, ← isMarked_iff, ← isMarked_iff, isMarked_perm_smul,
      isMarked_coverGraphCode, isMarked_coverGraphCode]
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
