/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.DenseLinearOrder
public import TauCeti.ModelTheory.RelationalConfiguration.WellOrder
public import TauCeti.SetTheory.Descriptive.Tree.Order

/-!
# The classes of coded linear orders and coded trees

In the language `Language.order` of one binary symbol `leSymb`, read as a non-strict order, a
configuration `c` on a carrier `V` assigns to `leSymb` the relation `codeRel leSymb c`. This file
defines the two classes of codes through which graphs are reduced to orders in the proof that
linear orders and trees are Borel complete:

* `linearOrderClass`, the codes of linear orders, the models of Mathlib's
  `Language.order.linearOrderTheory`. Every axiom of that theory is universal, so the class is
  closed.
* `treeClass`, the codes of trees: partial orders with a least element in which every principal
  down-set `{y | y ≤ x}` is a finite chain (`TauCeti.IsTreeOrder`). Finiteness of down-sets is a
  countable union over finite bounds, so on a countable carrier the class is Borel. On `ℕ` it is
  not closed: the codes of the well-orders `n < n - 1 < ⋯ < 0 < n + 1 < n + 2 < ⋯` of type `ω`
  converge to the code of `(ℕ, ≥)`, which has no least element.

Both classes are isomorphism invariant. Coded trees and trees of finite sequences in the sense
of descriptive set theory (`Descriptive.tree`) present the same trees: a tree order is
isomorphic to the prefix order of the tree of its paths from the least element, and an infinite
tree of finite sequences of natural numbers, relabelled along a bijection with `ℕ`, is a coded tree.

## Main definitions

* `TauCeti.RelationalConfiguration.ofRel r`: the code of a relation `r`.
* `TauCeti.RelationalConfiguration.linearOrderClass`: the codes of linear orders.
* `TauCeti.RelationalConfiguration.addDiag c`: the code of the relation of `c` with the diagonal
  added.
* `TauCeti.RelationalConfiguration.treeClass`: the codes of trees.

## Main results

* `TauCeti.RelationalConfiguration.codeRel_ofRel`, `TauCeti.RelationalConfiguration.ofRel_codeRel`:
  `ofRel` and `codeRel leSymb` are inverse bijections between relations and codes.
* `TauCeti.RelationalConfiguration.mem_linearOrderClass`: a code lies in `linearOrderClass`
  exactly when its relation is a linear order.
* `TauCeti.RelationalConfiguration.isClosed_linearOrderClass`,
  `TauCeti.RelationalConfiguration.isomorphismInvariant_linearOrderClass`.
* `TauCeti.RelationalConfiguration.addDiag_mem_linearOrderClass`: adding the diagonal to a coded
  strict total order gives a coded linear order.
* `TauCeti.RelationalConfiguration.type_eq_of_isoSetoid_addDiag`: isomorphic codes with the
  diagonal added come from coded strict well-orders of the same type.
* `TauCeti.RelationalConfiguration.mem_treeClass_iff_mem_modelsOfTheory_and`: `treeClass` is the
  class of models of `Language.order.partialOrderTheory` with a least element and finite chains as
  principal down-sets.
* `TauCeti.RelationalConfiguration.measurableSet_treeClass`,
  `TauCeti.RelationalConfiguration.isomorphismInvariant_treeClass`: on a countable carrier the
  class is invariant Borel.
* `TauCeti.RelationalConfiguration.not_isClosed_treeClass`: on `ℕ` the class is not closed.
* `TauCeti.RelationalConfiguration.exists_tree_relIso_of_mem_treeClass`,
  `TauCeti.RelationalConfiguration.exists_mem_treeClass_relIso`: coded trees on `ℕ` and infinite
  trees in `Descriptive.tree ℕ` present the same orders.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), §2 (linear orders and trees as classes of countable structures).
* A. Montalbán, *Computable structure theory: within the arithmetic*, author's draft of Part 1
  (2019), Lemma VI.18.
-/

public section

open FirstOrder FirstOrder.Language Set Filter Topology Descriptive

namespace TauCeti

variable {V : Type*}

namespace RelationalConfiguration

/-! ### Coded linear orders -/

/-- The **coded linear orders**: the configurations whose relation `codeRel leSymb c` is a
(non-strict) linear order, the models of `Language.order.linearOrderTheory`. -/
def linearOrderClass : Set (RelationalConfiguration Language.order V) :=
  modelsOfTheory Language.order.linearOrderTheory

/-- A configuration is a coded linear order exactly when its relation is a linear order. -/
@[simp]
theorem mem_linearOrderClass {c : RelationalConfiguration Language.order V} :
    c ∈ linearOrderClass ↔ IsLinearOrder V (codeRel leSymb c) :=
  mem_modelsOfTheory_linearOrderTheory

/-- The coded linear orders form a closed class. -/
theorem isClosed_linearOrderClass : IsClosed (linearOrderClass (V := V)) :=
  isClosed_modelsOfTheory_linearOrder

/-- On a countable carrier the coded linear orders form a Borel class. -/
theorem measurableSet_linearOrderClass [Countable V] :
    MeasurableSet (linearOrderClass (V := V)) :=
  isClosed_linearOrderClass.measurableSet

/-- The coded linear orders form an isomorphism-invariant class. -/
theorem isomorphismInvariant_linearOrderClass :
    IsomorphismInvariant (linearOrderClass (V := V)) :=
  isomorphismInvariant_modelsOfTheory _

/-- `orderStructure` reads `leSymb` as `≤`. -/
private theorem relMap_leSymb_orderStructure [LE V] (x : Fin 2 → V) :
    @Structure.RelMap Language.order V (orderStructure V) 2 leSymb x ↔ x 0 ≤ x 1 :=
  -- `orderStructure` is defined by matching on the symbol, with `x 0 ≤ x 1` for `leSymb`.
  Iff.rfl

/-- The code of a relation `r` on `V` in `Language.order`: the configuration whose relation for
`leSymb` is `r`, that is, the code of `V` with the structure `orderStructure` reading `r` as
`≤`. -/
noncomputable def ofRel (r : V → V → Prop) : RelationalConfiguration Language.order V :=
  @ofStructure Language.order V (@orderStructure V ⟨r⟩)

/-- The code of a relation `r` reads `leSymb` as `r`. -/
@[simp]
theorem codeRel_ofRel (r : V → V → Prop) : codeRel leSymb (ofRel r) = r := by
  ext x y
  let _ : LE V := ⟨r⟩
  let _ : Language.order.Structure V := orderStructure V
  rw [ofRel, codeRel_ofStructure, relMap_leSymb_orderStructure, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  -- The `LE` instance `⟨r⟩` reads `x ≤ y` as `r x y`.
  rfl

open Classical in
/-- The code of a relation `r` makes the atom `leSymb(v 0, v 1)` true exactly when
`r (v 0) (v 1)`. -/
@[simp]
theorem eval_ofRel (r : V → V → Prop) (v : Fin 2 → V) :
    (ofRel r).eval (atom leSymb v) = decide (r (v 0) (v 1)) := by
  let _ : LE V := ⟨r⟩
  let _ : Language.order.Structure V := orderStructure V
  rw [ofRel, eval_ofStructure, relMap_leSymb_orderStructure]
  -- The `LE` instance `⟨r⟩` reads `v 0 ≤ v 1` as `r (v 0) (v 1)`.
  rfl

/-- Every code is the code of its own relation. -/
@[simp]
theorem ofRel_codeRel (c : RelationalConfiguration Language.order V) :
    ofRel (codeRel leSymb c) = c := by
  classical
  refine ext fun a => ?_
  induction a using Atom.induction_atom with | @h k R v => ?_
  obtain rfl : k = 2 := by cases R; rfl
  rw [order.relation_eq_leSymb R, eval_ofRel, codeRel_iff, Bool.decide_eq_true]
  congr
  ext i
  fin_cases i <;> rfl

/-- Distinct relations have distinct codes. -/
theorem ofRel_injective : Function.Injective (ofRel (V := V)) := fun r s h => by
  rw [← codeRel_ofRel r, h, codeRel_ofRel]

/-- Two relations have the same code exactly when they are equal. -/
@[simp]
theorem ofRel_inj {r s : V → V → Prop} : ofRel r = ofRel s ↔ r = s :=
  ofRel_injective.eq_iff

/-- The code of an ordered type reads `leSymb` as its order. -/
@[simp]
theorem codeRel_leSymb_ofStructure_orderStructure [LE V] :
    codeRel leSymb (@ofStructure Language.order V (orderStructure V)) = (· ≤ ·) :=
  -- `orderStructure V` is `@orderStructure V ⟨(· ≤ ·)⟩` by structure eta for `LE V`.
  codeRel_ofRel _

/-- The code of a linearly ordered type is a coded linear order. -/
theorem ofStructure_mem_linearOrderClass [LinearOrder V] :
    @ofStructure Language.order V (orderStructure V) ∈ linearOrderClass := by
  rw [mem_linearOrderClass, codeRel_leSymb_ofStructure_orderStructure]
  infer_instance

/-! ### Adding the diagonal to a coded strict order -/

/-- The code obtained by adding the diagonal to the relation of `c`, written as the order
`x = y ∨ r x y` of Mathlib's `partialOrderOfSO`. -/
noncomputable def addDiag (c : RelationalConfiguration Language.order V) :
    RelationalConfiguration Language.order V :=
  ofRel fun x y => x = y ∨ codeRel leSymb c x y

/-- The relation of `addDiag c` is the relation of `c` with the diagonal added. -/
@[simp]
theorem codeRel_addDiag (c : RelationalConfiguration Language.order V) (x y : V) :
    codeRel leSymb (addDiag c) x y ↔ x = y ∨ codeRel leSymb c x y := by
  rw [addDiag, codeRel_ofRel]

/-- Adding the diagonal to a coded strict total order gives a coded linear order: its relation
is the order of Mathlib's `linearOrderOfSTO`. -/
theorem addDiag_mem_linearOrderClass {c : RelationalConfiguration Language.order V}
    [IsStrictTotalOrder V (codeRel leSymb c)] : addDiag c ∈ linearOrderClass := by
  classical
  have h : codeRel leSymb (addDiag c) = (linearOrderOfSTO (codeRel leSymb c)).le := by
    ext x y
    exact codeRel_addDiag c x y
  rw [mem_linearOrderClass, h]
  let := linearOrderOfSTO (codeRel leSymb c)
  infer_instance

/-- Isomorphic codes with the diagonal added come from coded strict well-orders of the same
type. -/
theorem type_eq_of_isoSetoid_addDiag {c d : RelationalConfiguration Language.order V}
    (hc : c ∈ wellOrderClass leSymb) (hd : d ∈ wellOrderClass leSymb)
    (h : isoSetoid Language.order V (addDiag c) (addDiag d)) :
    @Ordinal.type V (codeRel leSymb c) (mem_wellOrderClass.1 hc) =
      @Ordinal.type V (codeRel leSymb d) (mem_wellOrderClass.1 hd) := by
  have := mem_wellOrderClass.1 hc
  have := mem_wellOrderClass.1 hd
  obtain ⟨σ, hσ⟩ := isoSetoid_iff_exists_perm_smul_eq.1 h
  -- `σ` carries the reflexive closure of `codeRel leSymb c` to that of `codeRel leSymb d`.
  have hrefl (x y : V) :
      σ x = σ y ∨ codeRel leSymb d (σ x) (σ y) ↔ x = y ∨ codeRel leSymb c x y := by
    have := codeRel_perm_smul leSymb σ (addDiag c) (σ x) (σ y)
    rw [hσ] at this
    simpa using this
  refine RelIso.ordinalType_congr ⟨σ, fun {x y} => ?_⟩
  by_cases hxy : x = y
  · subst hxy
    exact ⟨fun h => absurd h (irrefl _), fun h => absurd h (irrefl _)⟩
  · have hσxy : σ x ≠ σ y := σ.injective.ne hxy
    simpa [hxy, hσxy] using hrefl x y

/-! ### Coded trees -/

/-- The **coded trees**: the configurations whose relation `codeRel leSymb c` is a tree order, a
partial order with a least element in which every principal down-set is a finite chain. -/
def treeClass : Set (RelationalConfiguration Language.order V) :=
  {c | IsTreeOrder (codeRel leSymb c)}

/-- Unfolding lemma for `treeClass`. -/
@[simp]
theorem mem_treeClass {c : RelationalConfiguration Language.order V} :
    c ∈ treeClass ↔ IsTreeOrder (codeRel leSymb c) :=
  Iff.rfl

/-- The coded trees are the models of `Language.order.partialOrderTheory` with a least element in
which every principal down-set is a finite chain. -/
theorem mem_treeClass_iff_mem_modelsOfTheory_and {c : RelationalConfiguration Language.order V} :
    c ∈ treeClass ↔ c ∈ modelsOfTheory Language.order.partialOrderTheory ∧
      (∃ a, ∀ x, codeRel leSymb c a x) ∧ (∀ x, {y | codeRel leSymb c y x}.Finite) ∧
      ∀ x, IsChain (codeRel leSymb c) {y | codeRel leSymb c y x} := by
  rw [mem_modelsOfTheory_partialOrderTheory, mem_treeClass]
  exact ⟨fun h =>
    ⟨h.isPartialOrder, h.exists_forall, h.finite_setOf, h.isChain_setOf⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

/-- The code of a linearly ordered type is a coded tree when the type is nonempty and embeds
into `ℕ` monotonically, for instance `(ℕ, ≤)` itself. -/
theorem ofStructure_mem_treeClass [Nonempty V] [LinearOrder V] {f : V → ℕ}
    (hf : StrictMono f) : @ofStructure Language.order V (orderStructure V) ∈ treeClass := by
  rw [mem_treeClass, codeRel_leSymb_ofStructure_orderStructure]
  have h := isTreeOrder_of_injective hf.injective
  simp only [hf.le_iff_le] at h
  exact h

/-- The coded trees form an isomorphism-invariant class. -/
theorem isomorphismInvariant_treeClass : IsomorphismInvariant (treeClass (V := V)) :=
  isomorphismInvariant_setOf_codeRel leSymb fun e h => h.of_relIso e

/-- On a countable carrier the coded trees form a Borel class: finiteness of a down-set is a
countable union over finite sets bounding it. -/
theorem measurableSet_treeClass [Countable V] : MeasurableSet (treeClass (V := V)) := by
  classical
  let E (x y : V) : Set (RelationalConfiguration Language.order V) := {c | codeRel leSymb c x y}
  have hE (x y : V) : MeasurableSet (E x y) := measurableSet_setOf_codeRel leSymb x y
  have heq : treeClass = modelsOfTheory Language.order.partialOrderTheory ∩
      (⋃ a, ⋂ x, E a x) ∩ (⋂ x, ⋃ s : Finset V, ⋂ y ∈ (↑s : Set V)ᶜ, (E y x)ᶜ) ∩
      (⋂ x, ⋂ y, ⋂ z, ⋂ (_ : y ≠ z), (E y x ∩ E z x)ᶜ ∪ (E y z ∪ E z y)) := by
    ext c
    simp only [mem_treeClass_iff_mem_modelsOfTheory_and, mem_inter_iff, mem_iUnion, mem_iInter,
      mem_compl_iff, mem_union, E, mem_ofPred_eq, Finset.mem_coe, and_assoc, not_and_or,
      IsChain, Set.Pairwise]
    refine and_congr_right fun _ => and_congr_right fun _ => and_congr ?_ ?_
    · refine forall_congr' fun x => ⟨fun h => ⟨h.toFinset, fun y hy hR => hy ?_⟩, ?_⟩
      · simpa using hR
      · rintro ⟨s, hs⟩
        exact s.finite_toSet.subset fun y hy => by_contra fun hn => hs y hn hy
    · refine forall_congr' fun x => ⟨fun h y z hyz => ?_, fun h y hy z hz hyz => ?_⟩
      · by_cases hy : codeRel leSymb c y x
        · by_cases hz : codeRel leSymb c z x
          · exact Or.inr (h hy hz hyz)
          · exact Or.inl (Or.inr hz)
        · exact Or.inl (Or.inl hy)
      · exact ((h y z hyz).resolve_left (by tauto))
  rw [heq]
  refine (((measurableSet_modelsOfTheory_of_countable ?_).inter ?_).inter ?_).inter ?_
  · simp [partialOrderTheory, preorderTheory]
  · exact MeasurableSet.iUnion fun a => MeasurableSet.iInter fun x => hE a x
  · exact MeasurableSet.iInter fun x => MeasurableSet.iUnion fun s =>
      MeasurableSet.iInter fun y => MeasurableSet.iInter fun _ => (hE y x).compl
  · exact MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => MeasurableSet.iInter
      fun z => MeasurableSet.iInter fun _ =>
        (((hE y x).inter (hE z x)).compl.union ((hE y z).union (hE z y)))

/-- The rank of `x` in the order `n < n - 1 < ⋯ < 0 < n + 1 < n + 2 < ⋯` of type `ω`. -/
private def foldRank (n x : ℕ) : ℕ := if x ≤ n then n - x else x

private theorem foldRank_injective (n : ℕ) : Function.Injective (foldRank n) := by
  intro x y h
  simp only [foldRank] at h
  split_ifs at h <;> omega

/-- On `ℕ` the coded trees do not form a closed class: the codes of the well-orders
`n < n - 1 < ⋯ < 0 < n + 1 < n + 2 < ⋯` converge to the code of `(ℕ, ≥)`, which has no least
element. -/
theorem not_isClosed_treeClass : ¬ IsClosed (treeClass (V := ℕ)) := by
  intro hclosed
  have hmem : ∀ n, ofRel (fun x y => foldRank n x ≤ foldRank n y) ∈ treeClass := fun n => by
    rw [mem_treeClass, codeRel_ofRel]
    exact isTreeOrder_of_injective (foldRank_injective n)
  have htend : Tendsto (fun n => ofRel (fun x y => foldRank n x ≤ foldRank n y)) atTop
      (𝓝 (ofRel fun x y : ℕ => y ≤ x)) := by
    refine tendsto_pi_nhds.2 fun a => ?_
    simp only [← eval_def]
    induction a using Atom.induction_atom with | @h k R v => ?_
    obtain rfl : k = 2 := by cases R; rfl
    rw [order.relation_eq_leSymb R]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (Finset.univ.sup v)] with n hn
    rw [eval_ofRel, eval_ofRel]
    have h0 := (Finset.le_sup (f := v) (Finset.mem_univ 0)).trans hn
    have h1 := (Finset.le_sup (f := v) (Finset.mem_univ 1)).trans hn
    refine decide_eq_decide.2 ?_
    simp only [foldRank, h0, h1, ↓reduceIte]
    omega
  have h := (hclosed.mem_of_tendsto htend (Eventually.of_forall hmem)).exists_forall
  rw [codeRel_ofRel] at h
  obtain ⟨a, ha⟩ := h
  exact absurd (ha (a + 1)) (by omega)

/-- **Coded trees are trees of finite sequences** (`treeClass` and `Descriptive.tree ℕ` present
the same trees): the decoded order of every coded tree on `ℕ` is isomorphic to the prefix order of
an infinite tree of finite sequences of natural numbers. -/
theorem exists_tree_relIso_of_mem_treeClass {c : RelationalConfiguration Language.order ℕ}
    (hc : c ∈ treeClass) : ∃ T : tree ℕ, (T : Set (List ℕ)).Infinite ∧
      Nonempty (codeRel leSymb c ≃r fun x y : T => (x : List ℕ) <+: y) := by
  obtain ⟨T, ⟨e⟩⟩ := hc.exists_relIso_tree
  exact ⟨T, Set.infinite_coe_iff.1 (Infinite.of_injective e e.injective), ⟨e⟩⟩

/-- **Trees of finite sequences are coded trees**: the prefix order of every infinite tree of
finite sequences of natural numbers is isomorphic to the decoded order of a coded tree on `ℕ`. -/
theorem exists_mem_treeClass_relIso {T : tree ℕ} (hT : (T : Set (List ℕ)).Infinite) :
    ∃ c : RelationalConfiguration Language.order ℕ, c ∈ treeClass ∧
      Nonempty (codeRel leSymb c ≃r fun x y : T => (x : List ℕ) <+: y) := by
  have : Infinite T := hT.to_subtype
  obtain ⟨_⟩ := nonempty_denumerable T
  let e : ℕ ≃ T := (Denumerable.eqv T).symm
  let f : (fun x y : ℕ => ((e x : List ℕ) <+: e y)) ≃r fun x y : T => (x : List ℕ) <+: y :=
    ⟨e, Iff.rfl⟩
  have hnil : [] ∈ T := Tree.mem_of_prefix List.nil_prefix hT.nonempty.some_mem
  refine ⟨ofRel fun x y => (e x : List ℕ) <+: e y, ?_, ?_⟩
  · rw [mem_treeClass, codeRel_ofRel]
    exact (isTreeOrder_isPrefix hnil).of_relIso f.symm
  · rw [codeRel_ofRel]
    exact ⟨f⟩

end RelationalConfiguration

end TauCeti
