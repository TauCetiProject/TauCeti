/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.SetTheory.Descriptive.Tree
public import Mathlib.Data.Set.Card
public import Mathlib.Order.RelIso.Set
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
* `TauCeti.IsTreeOrder.wellFounded`: the strict order of a tree order is well-founded.
* `TauCeti.isTreeOrder_of_injective`: the order pulled back from `ℕ` along an injection is a tree
  order.
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

/-- The strict order of a tree order is well-founded: a strict predecessor has strictly fewer
predecessors. -/
theorem IsTreeOrder.wellFounded {r : V → V → Prop} (h : IsTreeOrder r) :
    WellFounded fun x y => r x y ∧ ¬ r y x := by
  have := h.isPartialOrder
  refine Subrelation.wf (fun {x y} hxy => ?_) (measure fun x => {y | r y x}.ncard).wf
  exact ncard_lt_ncard ⟨fun z hz => trans_of r hz hxy.1, fun hs => hxy.2 (hs (refl_of r y))⟩
    (h.finite_setOf y)

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
  refine ⟨(Subrel.relEmbedding (· <+: ·) (· ∈ T)).isPartialOrder,
    ⟨⟨[], hT⟩, fun x => List.nil_prefix⟩, fun x => ?_,
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
  Subrelation.wf (fun hxy => lt_iff_le_not_ge.1 hxy) h.wellFounded

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
