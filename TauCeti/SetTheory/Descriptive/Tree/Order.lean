/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Descriptive.Tree
public import Mathlib.Data.Set.Card
public import Mathlib.Order.RelIso.Set
public import Mathlib.Data.Set.Finite.Lemmas
public import TauCeti.Order.RelCovBy
import Mathlib.Order.Interval.Finset.Nat

/-!
# Tree orders and trees of finite sequences

A **tree order** is a partial order with a least element in which every principal down-set
`{y | y ≤ x}` is a finite chain. This file shows that tree orders and trees of finite sequences in
the sense of descriptive set theory (`Descriptive.tree`) present the same orders: the prefix order
of a nonempty tree of finite sequences is a tree order, and a tree order is isomorphic to the
prefix order of the tree of its paths from the least element.

## Main definitions

* `TauCeti.IsTreeOrder r`: `r` is a partial order with a least element whose principal down-sets
  are finite chains.

## Main results

* `TauCeti.IsTreeOrder.of_relIso`: being a tree order is transported along relation isomorphisms.
* `TauCeti.IsTreeOrder.ncard_lt_ncard_of_rel_of_not_rel`, `TauCeti.IsTreeOrder.wellFounded`: a
  strict predecessor has strictly fewer predecessors, so the strict order of a tree order is
  well-founded.
* `TauCeti.isTreeOrder_of_injective`: the order pulled back from `ℕ` along an injection is a tree
  order.
* `TauCeti.IsTreeOrder.exists_relCovBy`, `TauCeti.IsTreeOrder.rel_of_relCovBy`: every element
  with a strict predecessor covers its *parent*, the largest of its strict predecessors.
* `TauCeti.IsTreeOrder.eq_of_relCovBy`: every element covers at most one element.
* `TauCeti.isTreeOrder_isPrefix`, `TauCeti.IsTreeOrder.exists_relIso_tree`: tree orders are the
  prefix orders of nonempty trees of finite sequences, up to isomorphism.
-/

public section

open Set Descriptive

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

/-- In a tree order a strict predecessor `x` of `y` has strictly fewer predecessors than `y`. -/
theorem IsTreeOrder.ncard_lt_ncard_of_rel_of_not_rel {r : V → V → Prop} (h : IsTreeOrder r)
    {x y : V} (hxy : r x y) (hyx : ¬ r y x) : {w | r w x}.ncard < {w | r w y}.ncard := by
  have := h.isPartialOrder
  exact ncard_lt_ncard ⟨fun z hz => trans_of r hz hxy, fun hs => hyx (hs (refl_of r y))⟩
    (h.finite_setOf y)

/-- The strict order of a tree order is well-founded: a strict predecessor has strictly fewer
predecessors. -/
theorem IsTreeOrder.wellFounded {r : V → V → Prop} (h : IsTreeOrder r) :
    WellFounded fun x y => r x y ∧ ¬ r y x :=
  Subrelation.wf (fun {_ _} hxy => h.ncard_lt_ncard_of_rel_of_not_rel hxy.1 hxy.2)
    (measure fun x => {y | r y x}.ncard).wf

/-- The order pulled back from `ℕ` along an injection, from a nonempty type, is a tree order: a
well-order of type at most `ω`. -/
theorem isTreeOrder_of_injective [Nonempty V] {f : V → ℕ} (hf : Function.Injective f) :
    IsTreeOrder fun x y => f x ≤ f y := by
  refine ⟨?_, ?_, fun x => ?_, fun x => ?_⟩
  · exact (RelEmbedding.mk ⟨f, hf⟩ Iff.rfl : (fun x y => f x ≤ f y) ↪r (· ≤ ·)).isPartialOrder
  · exact ⟨Function.argmin f, fun x => Function.argmin_le f x⟩
  · exact (Set.finite_Iic (f x)).preimage hf.injOn
  · exact fun y _ z _ _ => le_total (f y) (f z)

/-! ### Parents -/

namespace IsTreeOrder

variable {r : V → V → Prop} (h : IsTreeOrder r)
include h

/-- If `p` is covered by `y` in a tree order, every strict predecessor of `y` lies below `p`. -/
theorem rel_of_relCovBy {p y z : V} (hpy : RelCovBy r p y) (hz : r z y) (hzy : z ≠ y) :
    r z p := by
  have := h.isPartialOrder
  rw [relCovBy_iff] at hpy
  by_contra hzp
  refine ((h.isChain_setOf y).total hz hpy.1.1).elim hzp fun hpz => ?_
  exact hpy.2 z ⟨⟨hpz, hzp⟩, hz, fun hyz => hzy (antisymm_of r hz hyz)⟩

/-- In a tree order every element with a strict predecessor `z` covers some element: the largest
of its strict predecessors. -/
theorem exists_relCovBy {y z : V} (hz : r z y) (hzy : z ≠ y) : ∃ p, RelCovBy r p y := by
  have := h.isPartialOrder
  let S := {z | r z y} \ {y}
  have hS : S.Finite := (h.finite_setOf y).sdiff
  obtain ⟨p, ⟨hpy, hpy'⟩, hmax⟩ := Set.exists_max_image S (fun z => {w | r w z}.ncard) hS
    ⟨z, hz, hzy⟩
  have hp (z : V) (hz : r z y) (hzy : z ≠ y) : r z p := by
    refine ((h.isChain_setOf y).total hz hpy).elim id fun hpz => ?_
    have hsub : {w | r w p} ⊆ {w | r w z} := fun w hw => trans_of r hw hpz
    have heq := Set.ext_iff.1
      (Set.eq_of_subset_of_ncard_le hsub (hmax z ⟨hz, hzy⟩) (h.finite_setOf z)) z
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq] at heq
    exact heq.2 (refl_of r z)
  refine ⟨p, relCovBy_iff.2 ⟨⟨hpy, fun hyp => hpy' (antisymm_of r hpy hyp)⟩,
    fun w ⟨⟨_, hwp⟩, hwy, hyw⟩ => ?_⟩⟩
  exact hwp (hp w hwy fun hw => hyw (hw ▸ refl_of r y))

/-- In a tree order every element covers at most one element. -/
theorem eq_of_relCovBy {p q y : V} (hp : RelCovBy r p y) (hq : RelCovBy r q y) : p = q := by
  have := h.isPartialOrder
  exact antisymm_of r (h.rel_of_relCovBy hq hp.rel hp.ne) (h.rel_of_relCovBy hp hq.rel hq.ne)

end IsTreeOrder

/-! ### Tree orders as trees of finite sequences -/

/-- The prefix order of a nonempty tree of finite sequences is a tree order, with least element
the empty sequence. -/
theorem isTreeOrder_isPrefix {A : Type*} {T : tree A} (hT : [] ∈ T) :
    IsTreeOrder fun x y : T => (x : List A) <+: y := by
  refine ⟨(Subrel.relEmbedding (· <+: ·) (· ∈ T)).isPartialOrder,
    ⟨⟨[], hT⟩, fun x => List.nil_prefix⟩, fun x => ?_,
    fun x y hy z hz _ => List.prefix_or_prefix_of_prefix hy hz⟩
  exact ((x : List A).inits.finite_toSet.preimage Subtype.val_injective.injOn).subset
    fun y hy => List.mem_inits _ _ |>.2 hy

section Path

variable [PartialOrder V] (h : IsTreeOrder fun x y : V => x ≤ y)

include h in
private theorem le_of_not_nonempty {x : V} (hx : ¬ (Iio x).Nonempty) (y : V) : x ≤ y := by
  obtain ⟨a, ha⟩ := h.exists_forall
  obtain rfl | hlt := (ha x).eq_or_lt
  · exact ha y
  · exact absurd ⟨a, hlt⟩ hx

include h in
private theorem exists_covBy {x : V} (hx : (Iio x).Nonempty) : ∃ p, p ⋖ x := by
  obtain ⟨z, hz⟩ := hx
  simp_rw [← relCovBy_le_iff_covBy]
  exact h.exists_relCovBy hz.le hz.ne

open Classical in
/-- The parent of a node with a strict predecessor: the node it covers. -/
private noncomputable def parent (x : V) : V :=
  if hx : (Iio x).Nonempty then (exists_covBy h hx).choose else x

private theorem parent_spec {x : V} (hx : (Iio x).Nonempty) : parent h x ⋖ x := by
  have hp : parent h x = (exists_covBy h hx).choose := by
    simp only [parent, hx, ↓reduceDIte]
  exact hp ▸ (exists_covBy h hx).choose_spec

private theorem le_parent {x y : V} (hx : (Iio x).Nonempty) (hy : y < x) : y ≤ parent h x :=
  h.rel_of_relCovBy (relCovBy_le_iff_covBy.2 (parent_spec h hx)) hy.le hy.ne

open Classical in
/-- The path to a node: its strict successors of the least element, up to and including itself,
in increasing order. -/
private noncomputable def path (x : V) : List V :=
  if _hx : (Iio x).Nonempty then path (parent h x) ++ [x] else []
termination_by {y | y ≤ x}.ncard
decreasing_by
  exact h.ncard_lt_ncard_of_rel_of_not_rel (parent_spec h _hx).le (parent_spec h _hx).lt.not_ge

private theorem path_of_nonempty {x : V} (hx : (Iio x).Nonempty) :
    path h x = path h (parent h x) ++ [x] := by
  rw [path]
  simp only [hx, ↓reduceDIte]

private theorem path_of_not_nonempty {x : V} (hx : ¬ (Iio x).Nonempty) : path h x = [] := by
  rw [path]
  simp only [hx, ↓reduceDIte]

include h in
private theorem wellFounded_lt : WellFounded (fun x y : V => x < y) :=
  Subrelation.wf (fun hxy => lt_iff_le_not_ge.1 hxy) h.wellFounded

private theorem mem_path {y z : V} : z ∈ path h y ↔ (Iio z).Nonempty ∧ z ≤ y := by
  induction y using (wellFounded_lt h).induction with
  | _ y ih =>
  by_cases hy : (Iio y).Nonempty
  · rw [path_of_nonempty h hy, List.mem_append, List.mem_singleton,
      ih _ (parent_spec h hy).lt]
    refine ⟨?_, fun ⟨hz, hzy⟩ => ?_⟩
    · rintro (⟨hz, hzp⟩ | rfl)
      · exact ⟨hz, hzp.trans (parent_spec h hy).lt.le⟩
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
      exact (ih _ (parent_spec h hy).lt (le_parent h hy hlt)).trans (List.prefix_append _ _)

private theorem exists_path_eq_of_prefix {l : List V} {y : V} (hl : l <+: path h y) :
    ∃ x, path h x = l := by
  induction y using (wellFounded_lt h).induction with
  | _ y ih =>
  by_cases hy : (Iio y).Nonempty
  · rw [path_of_nonempty h hy, List.prefix_concat_iff] at hl
    rcases hl with rfl | hl
    · exact ⟨y, path_of_nonempty h hy⟩
    · exact ih _ (parent_spec h hy).lt hl
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
  -- The `≤` of this local partial order unfolds to `r`, so `h` is a tree order for `≤`, and
  -- `path_prefix_path h'` below states `path h' x <+: path h' y ↔ r x y`.
  have h' : IsTreeOrder fun x y : V => x ≤ y := h
  have hinj : Function.Injective (path h') := fun x y hxy =>
    le_antisymm ((path_prefix_path h').1 (hxy ▸ List.prefix_refl _))
      ((path_prefix_path h').1 (hxy ▸ List.prefix_refl _))
  let T : tree V := ⟨range (path h'), fun l a ⟨y, hy⟩ =>
    exists_path_eq_of_prefix h' (hy ▸ List.prefix_append l [a])⟩
  exact ⟨T, ⟨⟨Equiv.ofInjective _ hinj, (path_prefix_path h')⟩⟩⟩

end TauCeti
