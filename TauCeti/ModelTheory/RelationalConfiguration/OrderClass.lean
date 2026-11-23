/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.DenseLinearOrder
public import TauCeti.ModelTheory.RelationalConfiguration.WellOrder
public import Mathlib.SetTheory.Descriptive.Tree

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
  countable union over finite bounds, so on a countable carrier the class is Borel. It is not
  closed: the codes of the well-orders `n < n - 1 < ⋯ < 0 < n + 1 < n + 2 < ⋯` of type `ω`
  converge to the code of `(ℕ, ≥)`, which has no least element.

Both classes are isomorphism invariant. Coded trees and trees of finite sequences in the sense
of descriptive set theory (`Descriptive.tree`) present the same trees: a tree order is
isomorphic to the prefix order of the tree of its paths from the least element, and an infinite
tree of finite sequences of natural numbers, relabelled along a bijection with `ℕ`, is a coded tree.

## Main definitions

* `TauCeti.IsTreeOrder r`: `r` is a partial order with a least element whose principal down-sets
  are finite chains.
* `TauCeti.RelationalConfiguration.linearOrderClass`: the codes of linear orders.
* `TauCeti.RelationalConfiguration.treeClass`: the codes of trees.

## Main results

* `TauCeti.RelationalConfiguration.mem_linearOrderClass`: a code lies in `linearOrderClass`
  exactly when its relation is a linear order.
* `TauCeti.RelationalConfiguration.isClosed_linearOrderClass`,
  `TauCeti.RelationalConfiguration.isomorphismInvariant_linearOrderClass`.
* `TauCeti.RelationalConfiguration.mem_treeClass_iff_mem_modelsOfTheory`: `treeClass` is the
  class of models of `Language.order.partialOrderTheory` with a least element and finite chains as
  principal down-sets.
* `TauCeti.RelationalConfiguration.measurableSet_treeClass`,
  `TauCeti.RelationalConfiguration.isomorphismInvariant_treeClass`: on a countable carrier the
  class is invariant Borel.
* `TauCeti.RelationalConfiguration.not_isClosed_treeClass`: on `ℕ` the class is not closed.
* `TauCeti.IsTreeOrder.exists_relIso_tree`, `TauCeti.isTreeOrder_isPrefix`: tree orders are the
  prefix orders of nonempty trees of finite sequences, up to isomorphism.
* `TauCeti.RelationalConfiguration.exists_tree_relIso_of_mem_treeClass`,
  `TauCeti.RelationalConfiguration.exists_mem_treeClass_relIso`: coded trees on `ℕ` and infinite
  trees in `Descriptive.tree ℕ` present the same orders.

## References

* H. Friedman and L. Stanley, *A Borel reducibility theory for classes of countable structures*,
  J. Symbolic Logic 54 (1989), §2 (linear orders and trees as classes of countable structures).
* A. Montalbán, *Computable structure theory: beyond the arithmetic*, draft, Lemma VI.18.
-/

public section

open FirstOrder FirstOrder.Language Set Filter Topology Descriptive

namespace TauCeti

variable {V W : Type*}

/-- A binary relation `r` is a **tree order** when it is a partial order with a least element in
which every principal down-set `{y | r y x}` is finite and linearly ordered by `r`. -/
structure IsTreeOrder (r : V → V → Prop) : Prop where
  /-- A tree order is a partial order. -/
  isPartialOrder : IsPartialOrder V r
  /-- A tree order has a least element. -/
  exists_forall : ∃ a, ∀ x, r a x
  /-- Every principal down-set of a tree order is finite. -/
  finite_setOf : ∀ x, {y | r y x}.Finite
  /-- Every principal down-set of a tree order is a chain. -/
  isChain_setOf : ∀ x, IsChain r {y | r y x}

/-- Being a tree order is transported along relation isomorphisms. -/
theorem IsTreeOrder.of_relIso {r : V → V → Prop} {s : W → W → Prop} (e : r ≃r s)
    (h : IsTreeOrder r) : IsTreeOrder s := by
  have : IsPartialOrder V r := h.isPartialOrder
  have hdown (x : W) : {y | s y x} = e '' {y | r y (e.symm x)} := by
    ext y
    simp only [mem_ofPred_eq, mem_image]
    refine ⟨fun hy => ⟨e.symm y, e.symm.map_rel_iff.2 hy, by simp⟩, ?_⟩
    rintro ⟨z, hz, rfl⟩
    simpa using e.map_rel_iff.2 hz
  refine ⟨e.symm.toRelEmbedding.isPartialOrder, ?_, fun x => ?_, fun x => ?_⟩
  · obtain ⟨a, ha⟩ := h.exists_forall
    exact ⟨e a, fun x => by simpa using e.map_rel_iff.2 (ha (e.symm x))⟩
  · rw [hdown]
    exact (h.finite_setOf _).image e
  · rw [hdown]
    exact (h.isChain_setOf _).image e

/-- The order pulled back from `ℕ` along an injection, from a nonempty type, is a tree order: a
well-order of type at most `ω`. -/
theorem isTreeOrder_of_injective [Nonempty V] {f : V → ℕ} (hf : Function.Injective f) :
    IsTreeOrder fun x y => f x ≤ f y := by
  refine ⟨?_, ?_, fun x => ?_, fun x => ?_⟩
  · exact (RelEmbedding.mk ⟨f, hf⟩ Iff.rfl : (fun x y => f x ≤ f y) ↪r (· ≤ ·)).isPartialOrder
  · exact ⟨Function.argmin f, fun x => Function.argmin_le f x⟩
  · exact (Set.finite_Iic (f x)).preimage hf.injOn
  · exact fun y _ z _ _ => le_total (f y) (f z)

/-! ### Tree orders as trees of finite sequences -/

/-- The prefix order of a nonempty tree of finite sequences is a tree order, with least element
the empty sequence. -/
theorem isTreeOrder_isPrefix {A : Type*} {T : tree A} (hT : [] ∈ T) :
    IsTreeOrder fun x y : T => (x : List A) <+: y := by
  have hpo : IsPartialOrder T fun x y : T => (x : List A) <+: y :=
    { refl := fun x => List.prefix_refl _
      trans := fun _ _ _ => List.IsPrefix.trans
      antisymm := fun _ _ h₁ h₂ =>
        Subtype.ext (h₁.eq_of_length (le_antisymm h₁.length_le h₂.length_le)) }
  refine ⟨hpo, ⟨⟨[], hT⟩, fun x => List.nil_prefix⟩, fun x => ?_,
    fun x y hy z hz _ => List.prefix_or_prefix_of_prefix hy hz⟩
  exact ((x : List A).inits.finite_toSet.preimage Subtype.val_injective.injOn).subset
    fun y hy => List.mem_inits _ _ |>.2 hy

section Path

variable [PartialOrder V] (h : IsTreeOrder fun x y : V => x ≤ y)

/-- The number of strict predecessors of a node. -/
private noncomputable def height (x : V) : ℕ := (Iio x).ncard

include h in
private theorem finite_Iio (x : V) : (Iio x).Finite :=
  (h.finite_setOf x).subset fun _ hy => le_of_lt hy

include h in
private theorem height_lt {x y : V} (hxy : x < y) : height x < height y :=
  ncard_lt_ncard ⟨Iio_subset_Iio hxy.le, fun hs => lt_irrefl x (hs hxy)⟩ (finite_Iio h y)

include h in
private theorem le_of_not_nonempty {x : V} (hx : ¬ (Iio x).Nonempty) (y : V) : x ≤ y := by
  obtain ⟨a, ha⟩ := h.exists_forall
  obtain rfl | hlt := (ha x).eq_or_lt
  · exact ha y
  · exact absurd ⟨a, hlt⟩ hx

open Classical in
/-- The parent of a node with a strict predecessor: its greatest strict predecessor. -/
private noncomputable def parent (x : V) : V :=
  if hx : (Iio x).Nonempty then
    ((finite_Iio h x).toFinset.exists_max_image height (by simpa using hx)).choose
  else x

private theorem parent_spec {x : V} (hx : (Iio x).Nonempty) :
    parent h x < x ∧ ∀ y < x, height y ≤ height (parent h x) := by
  have hne : (finite_Iio h x).toFinset.Nonempty := by simpa using hx
  obtain ⟨hmem, hmax⟩ := ((finite_Iio h x).toFinset.exists_max_image height hne).choose_spec
  have hp : parent h x = ((finite_Iio h x).toFinset.exists_max_image height hne).choose := by
    simp only [parent, hx, ↓reduceDIte]
  rw [hp]
  exact ⟨by simpa using hmem, fun y hy => hmax y (by simpa using hy)⟩

private theorem le_parent {x y : V} (hx : (Iio x).Nonempty) (hy : y < x) : y ≤ parent h x := by
  obtain ⟨hp, hmax⟩ := parent_spec h hx
  rcases (h.isChain_setOf x).total (show y ≤ x from hy.le) (show parent h x ≤ x from hp.le)
    with hyp | hpy
  · exact hyp
  · obtain rfl | hlt := hpy.eq_or_lt
    · exact le_rfl
    · exact absurd (hmax y hy) (not_le.2 (height_lt h hlt))

open Classical in
/-- The path to a node: its strict successors of the least element, up to and including itself,
in increasing order. -/
private noncomputable def path (x : V) : List V :=
  if _hx : (Iio x).Nonempty then path (parent h x) ++ [x] else []
termination_by height x
decreasing_by exact height_lt h (parent_spec h _hx).1

private theorem path_of_nonempty {x : V} (hx : (Iio x).Nonempty) :
    path h x = path h (parent h x) ++ [x] := by
  rw [path]
  simp only [hx, ↓reduceDIte]

private theorem path_of_not_nonempty {x : V} (hx : ¬ (Iio x).Nonempty) : path h x = [] := by
  rw [path]
  simp only [hx, ↓reduceDIte]

include h in
private theorem wellFounded_lt : WellFounded (fun x y : V => x < y) :=
  Subrelation.wf (fun hxy => height_lt h hxy) (measure height).wf

private theorem mem_path {y z : V} : z ∈ path h y ↔ (Iio z).Nonempty ∧ z ≤ y := by
  induction y using (wellFounded_lt h).induction with
  | _ y ih =>
  by_cases hy : (Iio y).Nonempty
  · rw [path_of_nonempty h hy, List.mem_append, List.mem_singleton,
      ih _ (parent_spec h hy).1]
    refine ⟨?_, fun ⟨hz, hzy⟩ => ?_⟩
    · rintro (⟨hz, hzp⟩ | rfl)
      · exact ⟨hz, hzp.trans (parent_spec h hy).1.le⟩
      · exact ⟨hy, le_rfl⟩
    · obtain rfl | hlt := hzy.eq_or_lt
      · exact Or.inr rfl
      · exact Or.inl ⟨hz, le_parent h hy hlt⟩
  · rw [path_of_not_nonempty h hy]
    simp only [List.not_mem_nil, false_iff, not_and]
    intro hz hzy
    obtain rfl | hlt := hzy.eq_or_lt
    · exact hy hz
    · exact hy ⟨z, hlt⟩

private theorem path_prefix_path {x y : V} : path h x <+: path h y ↔ x ≤ y := by
  refine ⟨fun hxy => ?_, fun hxy => ?_⟩
  · by_cases hx : (Iio x).Nonempty
    · exact ((mem_path h).1 (hxy.subset ((mem_path h).2 ⟨hx, le_rfl⟩))).2
    · exact le_of_not_nonempty h hx y
  · induction y using (wellFounded_lt h).induction with
    | _ y ih =>
    obtain rfl | hlt := hxy.eq_or_lt
    · exact List.prefix_refl _
    · have hy : (Iio y).Nonempty := ⟨x, hlt⟩
      rw [path_of_nonempty h hy]
      exact (ih _ (parent_spec h hy).1 (le_parent h hy hlt)).trans (List.prefix_append _ _)

private theorem exists_path_eq_of_prefix {l : List V} {y : V} (hl : l <+: path h y) :
    ∃ x, path h x = l := by
  induction y using (wellFounded_lt h).induction with
  | _ y ih =>
  by_cases hy : (Iio y).Nonempty
  · rw [path_of_nonempty h hy, List.prefix_concat_iff] at hl
    rcases hl with rfl | hl
    · exact ⟨y, path_of_nonempty h hy⟩
    · exact ih _ (parent_spec h hy).1 hl
  · rw [path_of_not_nonempty h hy, List.prefix_nil] at hl
    exact ⟨y, by rw [hl, path_of_not_nonempty h hy]⟩

end Path

/-- **A tree order is a tree of finite sequences**: every tree order on `V` is isomorphic to the
prefix order of a tree of finite sequences of elements of `V`, by sending a node to the increasing
list of the nodes above the least element and below or equal to it. -/
theorem IsTreeOrder.exists_relIso_tree {r : V → V → Prop} (h : IsTreeOrder r) :
    ∃ T : tree V, Nonempty (r ≃r fun x y : T => (x : List V) <+: y) := by
  have := h.isPartialOrder
  let _ : PartialOrder V :=
    { le := r, le_refl := refl_of r, le_trans := fun _ _ _ => trans_of r,
      le_antisymm := fun _ _ => antisymm_of r }
  have h' : IsTreeOrder fun x y : V => x ≤ y := h
  have hinj : Function.Injective (path h') := fun x y hxy =>
    le_antisymm ((path_prefix_path h').1 (hxy ▸ List.prefix_refl _))
      ((path_prefix_path h').1 (hxy ▸ List.prefix_refl _))
  let T : tree V := ⟨range (path h'), fun l a ⟨y, hy⟩ =>
    exists_path_eq_of_prefix h' (hy ▸ List.prefix_append l [a])⟩
  exact ⟨T, ⟨⟨Equiv.ofInjective _ hinj, (path_prefix_path h')⟩⟩⟩

namespace RelationalConfiguration

/-! ### Coded linear orders -/

/-- The **coded linear orders**: the configurations whose relation `codeRel leSymb c` is a
(non-strict) linear order, the models of `Language.order.linearOrderTheory`. -/
def linearOrderClass : Set (RelationalConfiguration Language.order V) :=
  modelsOfTheory Language.order.linearOrderTheory

/-- A configuration is a coded linear order exactly when its relation is a linear order. -/
theorem mem_linearOrderClass {c : RelationalConfiguration Language.order V} :
    c ∈ linearOrderClass ↔ IsLinearOrder V (codeRel leSymb c) := by
  simp only [linearOrderClass, mem_modelsOfTheory, linearOrderTheory, partialOrderTheory,
    preorderTheory, Theory.model_insert_iff, Theory.model_singleton_iff, Relations.realize_total,
    Relations.realize_antisymmetric, Relations.realize_reflexive, Relations.realize_transitive,
    relMap_toStructure_iff_codeRel]
  exact ⟨fun ⟨_, _, _, _⟩ => { }, fun _ => ⟨inferInstance, inferInstance, inferInstance,
    inferInstance⟩⟩

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

/-- The code of a relation `r`: the configuration whose relation for `leSymb` is `r`. -/
private noncomputable def ofRel (r : V → V → Prop) : RelationalConfiguration Language.order V :=
  @ofStructure Language.order V (@orderStructure V ⟨r⟩)

private theorem codeRel_ofRel (r : V → V → Prop) : codeRel leSymb (ofRel r) = r := by
  ext x y
  let : Language.order.Structure V := @orderStructure V ⟨r⟩
  exact codeRel_ofStructure leSymb x y

open Classical in
private theorem eval_ofRel (r : V → V → Prop) {k : ℕ} (R : Language.order.Relations k)
    (v : Fin k → V) :
    (ofRel r).eval (atom R v) = decide (@Structure.RelMap _ _ (@orderStructure V ⟨r⟩) k R v) := by
  let : Language.order.Structure V := @orderStructure V ⟨r⟩
  exact eval_ofStructure R v

/-- The code of an ordered type reads `leSymb` as its order. -/
theorem codeRel_leSymb_ofStructure_orderStructure [LE V] :
    codeRel leSymb (@ofStructure Language.order V (orderStructure V)) = (· ≤ ·) :=
  codeRel_ofRel _

/-- The code of a linearly ordered type is a coded linear order. -/
theorem ofStructure_mem_linearOrderClass [LinearOrder V] :
    @ofStructure Language.order V (orderStructure V) ∈ linearOrderClass := by
  rw [mem_linearOrderClass, codeRel_leSymb_ofStructure_orderStructure]
  infer_instance

/-! ### Coded trees -/

/-- The **coded trees**: the configurations whose relation `codeRel leSymb c` is a tree order, a
partial order with a least element in which every principal down-set is a finite chain. -/
def treeClass : Set (RelationalConfiguration Language.order V) :=
  {c | IsTreeOrder (codeRel leSymb c)}

/-- Unfolding lemma for `treeClass`. -/
theorem mem_treeClass {c : RelationalConfiguration Language.order V} :
    c ∈ treeClass ↔ IsTreeOrder (codeRel leSymb c) :=
  Iff.rfl

/-- A configuration models `Language.order.partialOrderTheory` exactly when its relation is a
partial order. -/
theorem mem_modelsOfTheory_partialOrderTheory {c : RelationalConfiguration Language.order V} :
    c ∈ modelsOfTheory Language.order.partialOrderTheory ↔
      IsPartialOrder V (codeRel leSymb c) := by
  simp only [mem_modelsOfTheory, partialOrderTheory, preorderTheory, Theory.model_insert_iff,
    Theory.model_singleton_iff, Relations.realize_antisymmetric, Relations.realize_reflexive,
    Relations.realize_transitive, relMap_toStructure_iff_codeRel]
  exact ⟨fun ⟨_, _, _⟩ => { }, fun _ => ⟨inferInstance, inferInstance, inferInstance⟩⟩

/-- The coded trees are the models of `Language.order.partialOrderTheory` with a least element in
which every principal down-set is a finite chain. -/
theorem mem_treeClass_iff_mem_modelsOfTheory {c : RelationalConfiguration Language.order V} :
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

/-- Relabelling by a permutation preserves being a coded tree. -/
theorem perm_smul_mem_treeClass_iff {σ : Equiv.Perm V}
    {c : RelationalConfiguration Language.order V} :
    σ • c ∈ treeClass ↔ c ∈ treeClass := by
  let e : codeRel leSymb c ≃r codeRel leSymb (σ • c) := ⟨σ, by simp⟩
  exact ⟨fun h => h.of_relIso e.symm, fun h => h.of_relIso e⟩

/-- The coded trees form an isomorphism-invariant class. -/
theorem isomorphismInvariant_treeClass : IsomorphismInvariant (treeClass (V := V)) := by
  refine isomorphismInvariant_iff.2 fun c d hcd hc => ?_
  obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 hcd
  exact perm_smul_mem_treeClass_iff.2 hc

/-- On a countable carrier the coded trees form a Borel class: finiteness of a down-set is a
countable union over finite sets bounding it. -/
theorem measurableSet_treeClass [Countable V] : MeasurableSet (treeClass (V := V)) := by
  classical
  let E (x y : V) : Set (RelationalConfiguration Language.order V) := {c | codeRel leSymb c x y}
  have hE (x y : V) : MeasurableSet (E x y) := by
    simpa only [E, codeRel_iff] using measurableSet_setOf_eval (atom leSymb ![x, y]) true
  have heq : treeClass = modelsOfTheory Language.order.partialOrderTheory ∩
      (⋃ a, ⋂ x, E a x) ∩ (⋂ x, ⋃ s : Finset V, ⋂ y ∈ (↑s : Set V)ᶜ, (E y x)ᶜ) ∩
      (⋂ x, ⋂ y, ⋂ z, ⋂ (_ : y ≠ z), (E y x ∩ E z x)ᶜ ∪ (E y z ∪ E z y)) := by
    ext c
    simp only [mem_treeClass_iff_mem_modelsOfTheory, mem_inter_iff, mem_iUnion, mem_iInter,
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
    induction a using Atom.induction_atom with | _ R v => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (Finset.univ.sup v)] with n hn
    rw [eval_ofRel, eval_ofRel]
    cases R
    have h0 := (Finset.le_sup (f := v) (Finset.mem_univ 0)).trans hn
    have h1 := (Finset.le_sup (f := v) (Finset.mem_univ 1)).trans hn
    refine decide_eq_decide.2 ?_
    change v 1 ≤ v 0 ↔ foldRank n (v 0) ≤ foldRank n (v 1)
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
