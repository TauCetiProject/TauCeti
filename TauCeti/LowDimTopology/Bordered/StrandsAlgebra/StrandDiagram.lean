/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Fintype.Prod
public import TauCeti.Data.Finset.Inversions
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Option

/-!
# Strand diagrams

Lipshitz, Ozsváth and Thurston build the algebra of a bordered Heegaard diagram from the
*strands algebra* `A(n)`. Its basis consists of the partial bijections `φ : S → T` between subsets
of `{1, …, n}` that only move points upwards, `i ≤ φ i`. One draws `φ` as a diagram of strands in
`[0, 1] × [1, n]`, the strand starting at `(0, i)` ending at `(1, φ i)`; the *inversions* of `φ`
are its crossings, the pairs `i < j` in `S` with `φ j < φ i`. The product of two diagrams is their
concatenation when that concatenation does not create a double crossing, which happens exactly when
their inversion counts add up to that of the composite.

This file develops these diagrams for an arbitrary linear order `α` in place of `{1, …, n}`. A
diagram is a partial equivalence `α ≃. α` (Mathlib's `PEquiv`) together with the upward condition;
partial equivalences compose by `PEquiv.trans` and are extensional, so a diagram carries no data
outside its strands. The main result is that inversion counts are subadditive under composition,
`TauCeti.StrandDiagram.inversionCount_trans_le`. It implies that the condition for a nonzero
product is associative in the form needed for the associativity of the strands algebra
(`TauCeti.StrandDiagram.trans_composable_and_composable_iff`).

## Main definitions

* `TauCeti.StrandDiagram α`: an upward partial bijection of the linear order `α`.
* `TauCeti.StrandDiagram.trans`: the composite of two diagrams, first `φ` and then `ψ`.
* `TauCeti.StrandDiagram.idOn`: the identity diagram on a finite set, with horizontal strands.
* `TauCeti.StrandDiagram.source`, `TauCeti.StrandDiagram.target`: the starting and ending points.
* `TauCeti.StrandDiagram.endpoint`, `TauCeti.StrandDiagram.startpoint`: the end point of the
  strand from a point, and the starting point of the strand to a point.
* `TauCeti.StrandDiagram.inversions`, `TauCeti.StrandDiagram.inversionCount`: the crossings.
* `TauCeti.StrandDiagram.Composable`: the target of `φ` is the source of `ψ` and the inversion
  counts add, `inv (φ.trans ψ) = inv φ + inv ψ`; this is when the product of `φ` and `ψ` in the
  strands algebra is nonzero.

## Main results

* `TauCeti.StrandDiagram.inversionCount_trans_le`: `inv (φ.trans ψ) ≤ inv φ + inv ψ`.
* `TauCeti.StrandDiagram.trans_composable_and_composable_iff`: the two bracketings of a triple
  product are nonzero under the same condition.
* `TauCeti.StrandDiagram.composable_idOn_left_iff`, `TauCeti.StrandDiagram.idOn_trans_of_eq_source`
  and their right-hand versions: the identity diagrams are the units of composition.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1,
  Definition 3.2 (the strands algebra `A(n, k)`).
-/

public section

open Finset

namespace TauCeti

/-- A strand diagram on a linear order `α`: a partial bijection `φ` of `α` that moves every point
of its domain upwards, `i ≤ φ i`. It is drawn as strands from `(0, i)` to `(1, φ i)`. These are the
basis elements of the strands algebra of Lipshitz, Ozsváth and Thurston. -/
structure StrandDiagram (α : Type*) [LinearOrder α] where
  /-- The underlying partial bijection. -/
  toPEquiv : α ≃. α
  /-- Every strand goes upwards. -/
  le_of_mem' : ∀ ⦃i j : α⦄, j ∈ toPEquiv i → i ≤ j

namespace StrandDiagram

variable {α : Type*} [LinearOrder α]

instance : FunLike (StrandDiagram α) α (Option α) where
  coe φ := φ.toPEquiv
  coe_injective φ ψ h := by
    obtain ⟨φ, _⟩ := φ
    obtain ⟨ψ, _⟩ := ψ
    congr
    exact PEquiv.ext (congrFun h)

@[simp]
theorem coe_toPEquiv (φ : StrandDiagram α) : ⇑φ.toPEquiv = φ :=
  rfl

@[ext]
theorem ext {φ ψ : StrandDiagram α} (h : ∀ i, φ i = ψ i) : φ = ψ :=
  DFunLike.ext _ _ h

theorem toPEquiv_injective : Function.Injective (toPEquiv : StrandDiagram α → α ≃. α) :=
  fun _ _ h ↦ ext fun i ↦ congrArg (fun f : α ≃. α ↦ f i) h

/-- Every strand of a diagram goes upwards. -/
theorem le_of_mem (φ : StrandDiagram α) {i j : α} (h : j ∈ φ i) : i ≤ j :=
  φ.le_of_mem' h

/-- Two strands of a diagram with the same end point start at the same point. -/
theorem eq_of_mem_of_mem (φ : StrandDiagram α) {x y a : α} (hx : a ∈ φ x) (hy : a ∈ φ y) :
    x = y :=
  φ.toPEquiv.inj hx hy

/-- Strands of a diagram starting at distinct points end at distinct points. -/
theorem ne_of_mem_of_mem_of_ne (φ : StrandDiagram α) {x y a b : α} (ha : a ∈ φ x)
    (hb : b ∈ φ y) (h : x ≠ y) : a ≠ b := by
  rintro rfl
  exact h (φ.eq_of_mem_of_mem ha hb)

/-- The end point of the strand of `φ` starting at `x`, and `x` itself when no strand starts
there. -/
def endpoint (φ : StrandDiagram α) (x : α) : α :=
  (φ x).getD x

theorem endpoint_def (φ : StrandDiagram α) (x : α) : φ.endpoint x = (φ x).getD x :=
  (rfl)

theorem endpoint_eq_of_mem {φ : StrandDiagram α} {x a : α} (h : a ∈ φ x) : φ.endpoint x = a := by
  rw [Option.mem_def] at h
  simp [endpoint_def, h]

/-- The starting point of the strand of `φ` ending at `y`, and `y` itself when no strand ends
there. This inverts `TauCeti.StrandDiagram.endpoint` between the source and the target. -/
def startpoint (φ : StrandDiagram α) (y : α) : α :=
  (φ.toPEquiv.symm y).getD y

theorem startpoint_def (φ : StrandDiagram α) (y : α) :
    φ.startpoint y = (φ.toPEquiv.symm y).getD y :=
  (rfl)

theorem startpoint_eq_of_mem {φ : StrandDiagram α} {x a : α} (h : a ∈ φ x) :
    φ.startpoint a = x := by
  simp [startpoint_def, (PEquiv.eq_some_iff _).2 h]

/-- The composite of two strand diagrams: first `φ`, then `ψ`. In the strands algebra it is the
concatenation of the diagram of `φ` on the left with that of `ψ` on the right. -/
protected def trans (φ ψ : StrandDiagram α) : StrandDiagram α where
  toPEquiv := φ.toPEquiv.trans ψ.toPEquiv
  le_of_mem' i k h := by
    obtain ⟨j, hj, hk⟩ := (PEquiv.mem_trans _ _ _ _).1 h
    exact (φ.le_of_mem hj).trans (ψ.le_of_mem hk)

@[simp]
theorem toPEquiv_trans (φ ψ : StrandDiagram α) :
    (φ.trans ψ).toPEquiv = φ.toPEquiv.trans ψ.toPEquiv :=
  (rfl)

@[simp]
theorem trans_apply (φ ψ : StrandDiagram α) (i : α) : φ.trans ψ i = (φ i).bind ψ :=
  (rfl)

theorem mem_trans {φ ψ : StrandDiagram α} {i k : α} :
    k ∈ φ.trans ψ i ↔ ∃ j, j ∈ φ i ∧ k ∈ ψ j :=
  PEquiv.mem_trans _ _ _ _

theorem trans_assoc (φ ψ χ : StrandDiagram α) :
    (φ.trans ψ).trans χ = φ.trans (ψ.trans χ) :=
  toPEquiv_injective (PEquiv.trans_assoc _ _ _)

/-- A strand of a composite is horizontal exactly when it is horizontal in both pieces. -/
theorem mem_trans_self_iff {φ ψ : StrandDiagram α} {i : α} :
    i ∈ φ.trans ψ i ↔ i ∈ φ i ∧ i ∈ ψ i := by
  refine ⟨fun h ↦ ?_, fun h ↦ mem_trans.2 ⟨i, h⟩⟩
  obtain ⟨j, hj, hj'⟩ := mem_trans.1 h
  obtain rfl := le_antisymm (ψ.le_of_mem hj') (φ.le_of_mem hj)
  exact ⟨hj, hj'⟩

/-- The identity diagram on a finite set `s`: one horizontal strand at each point of `s`. -/
def idOn (s : Finset α) : StrandDiagram α where
  toPEquiv := PEquiv.ofSet (s : Set α)
  le_of_mem' _ _ h := (PEquiv.mem_ofSet_iff.1 h).1.ge

@[simp]
theorem idOn_apply (s : Finset α) (i : α) : idOn s i = if i ∈ s then some i else none :=
  (rfl)

theorem mem_idOn {s : Finset α} {i j : α} : j ∈ idOn s i ↔ i = j ∧ i ∈ s := by
  rw [Option.mem_def, idOn_apply]
  split_ifs with h <;> simp [h]

instance [Finite α] : Finite (StrandDiagram α) :=
  Finite.of_injective _ (DFunLike.coe_injective (F := StrandDiagram α))

section Finite

variable [Fintype α]

/-- The starting points of the strands of `φ`, the set `S` of the partial bijection `φ : S → T`. -/
def source (φ : StrandDiagram α) : Finset α :=
  {i | (φ i).isSome}

/-- The end points of the strands of `φ`, the set `T` of the partial bijection `φ : S → T`. -/
def target (φ : StrandDiagram α) : Finset α :=
  {j | (φ.toPEquiv.symm j).isSome}

@[simp]
theorem mem_source {φ : StrandDiagram α} {i : α} : i ∈ φ.source ↔ ∃ j, j ∈ φ i := by
  simp [source, Option.isSome_iff_exists, Option.mem_def]

@[simp]
theorem mem_target {φ : StrandDiagram α} {j : α} : j ∈ φ.target ↔ ∃ i, j ∈ φ i := by
  simp [target, Option.isSome_iff_exists, PEquiv.eq_some_iff, ← coe_toPEquiv, Option.mem_def]

theorem apply_eq_none_of_notMem_source {φ : StrandDiagram α} {i : α} (h : i ∉ φ.source) :
    φ i = none :=
  Option.eq_none_iff_forall_ne_some.2 fun j hj ↦ h (mem_source.2 ⟨j, hj⟩)

@[simp]
theorem source_idOn (s : Finset α) : (idOn s).source = s := by
  ext i
  simp only [mem_source, mem_idOn]
  simp

@[simp]
theorem target_idOn (s : Finset α) : (idOn s).target = s := by
  ext j
  simp only [mem_target, mem_idOn]
  simp

/-- If `φ` ends where `ψ` starts, their composite starts where `φ` does. -/
theorem source_trans_of_target_eq {φ ψ : StrandDiagram α} (h : φ.target = ψ.source) :
    (φ.trans ψ).source = φ.source := by
  ext i
  simp only [mem_source, mem_trans]
  refine ⟨fun ⟨_, j, hj, _⟩ ↦ ⟨j, hj⟩, fun ⟨j, hj⟩ ↦ ?_⟩
  obtain ⟨k, hk⟩ := mem_source.1 (h ▸ mem_target.2 ⟨i, hj⟩)
  exact ⟨k, j, hj, hk⟩

/-- If `φ` ends where `ψ` starts, their composite ends where `ψ` does. -/
theorem target_trans_of_target_eq {φ ψ : StrandDiagram α} (h : φ.target = ψ.source) :
    (φ.trans ψ).target = ψ.target := by
  ext k
  simp only [mem_target, mem_trans]
  refine ⟨fun ⟨_, j, _, hk⟩ ↦ ⟨j, hk⟩, fun ⟨j, hk⟩ ↦ ?_⟩
  obtain ⟨i, hi⟩ := mem_target.1 (h.symm ▸ mem_source.2 ⟨k, hk⟩)
  exact ⟨i, j, hi, hk⟩

theorem endpoint_mem {φ : StrandDiagram α} {x : α} (hx : x ∈ φ.source) : φ.endpoint x ∈ φ x := by
  obtain ⟨a, ha⟩ := mem_source.1 hx
  rwa [endpoint_eq_of_mem ha]

theorem endpoint_mem_target {φ : StrandDiagram α} {x : α} (hx : x ∈ φ.source) :
    φ.endpoint x ∈ φ.target :=
  mem_target.2 ⟨x, endpoint_mem hx⟩

/-- Strands starting at distinct points of the source end at distinct points. -/
theorem endpoint_injOn (φ : StrandDiagram α) : Set.InjOn φ.endpoint φ.source :=
  fun _ hx _ hy h ↦ φ.eq_of_mem_of_mem (endpoint_mem hx) (h ▸ endpoint_mem hy)

theorem mem_startpoint {φ : StrandDiagram α} {y : α} (hy : y ∈ φ.target) :
    y ∈ φ (φ.startpoint y) := by
  obtain ⟨x, hx⟩ := mem_target.1 hy
  rwa [startpoint_eq_of_mem hx]

theorem startpoint_mem_source {φ : StrandDiagram α} {y : α} (hy : y ∈ φ.target) :
    φ.startpoint y ∈ φ.source :=
  mem_source.2 ⟨y, mem_startpoint hy⟩

@[simp]
theorem startpoint_endpoint {φ : StrandDiagram α} {x : α} (hx : x ∈ φ.source) :
    φ.startpoint (φ.endpoint x) = x :=
  startpoint_eq_of_mem (endpoint_mem hx)

@[simp]
theorem endpoint_startpoint {φ : StrandDiagram α} {y : α} (hy : y ∈ φ.target) :
    φ.endpoint (φ.startpoint y) = y :=
  endpoint_eq_of_mem (mem_startpoint hy)

theorem idOn_trans_of_eq_source {s : Finset α} {φ : StrandDiagram α} (h : s = φ.source) :
    (idOn s).trans φ = φ := by
  ext i k
  rw [← Option.mem_def, ← Option.mem_def, mem_trans]
  simp only [mem_idOn]
  refine ⟨fun ⟨_, ⟨rfl, _⟩, hk⟩ ↦ hk, fun hk ↦ ⟨i, ⟨rfl, ?_⟩, hk⟩⟩
  exact h ▸ mem_source.2 ⟨k, hk⟩

theorem trans_idOn_of_target_eq {s : Finset α} {φ : StrandDiagram α} (h : φ.target = s) :
    φ.trans (idOn s) = φ := by
  ext i k
  rw [← Option.mem_def, ← Option.mem_def, mem_trans]
  simp only [mem_idOn]
  refine ⟨fun ⟨_, hj, rfl, _⟩ ↦ hj, fun hk ↦ ⟨k, hk, rfl, ?_⟩⟩
  exact h ▸ mem_target.2 ⟨i, hk⟩

/-- The inversions of a strand diagram: the pairs `i < j` of starting points whose strands cross,
`φ j < φ i`. These are the inversions (`Finset.inversions`) of the end-point map of `φ` on its
source. -/
def inversions (φ : StrandDiagram α) : Finset (α × α) :=
  φ.source.inversions φ.endpoint

theorem inversions_def (φ : StrandDiagram α) : φ.inversions = φ.source.inversions φ.endpoint :=
  (rfl)

@[simp]
theorem mem_inversions {φ : StrandDiagram α} {p : α × α} :
    p ∈ φ.inversions ↔ p.1 < p.2 ∧ ∃ a ∈ φ p.1, ∃ b ∈ φ p.2, b < a := by
  rw [inversions_def, Finset.mem_inversions, mem_source, mem_source]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, h⟩
    rw [endpoint_eq_of_mem ha, endpoint_eq_of_mem hb] at h
    exact ⟨hab, a, ha, b, hb, h⟩
  · rintro ⟨hab, a, ha, b, hb, h⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, by rwa [endpoint_eq_of_mem ha, endpoint_eq_of_mem hb]⟩

/-- The strands of a crossing start at starting points of the diagram. -/
theorem fst_mem_source_of_mem_inversions {φ : StrandDiagram α} {p : α × α}
    (h : p ∈ φ.inversions) : p.1 ∈ φ.source := by
  obtain ⟨-, a, ha, -⟩ := mem_inversions.1 h
  exact mem_source.2 ⟨a, ha⟩

/-- The strands of a crossing start at starting points of the diagram. -/
theorem snd_mem_source_of_mem_inversions {φ : StrandDiagram α} {p : α × α}
    (h : p ∈ φ.inversions) : p.2 ∈ φ.source := by
  obtain ⟨-, -, -, b, hb, -⟩ := mem_inversions.1 h
  exact mem_source.2 ⟨b, hb⟩

/-- The strands of `φ` starting at `x` and `y`, with end points `a` and `b`, cross exactly when
`x < y` and `b < a`. -/
theorem mem_inversions_iff_of_mem {φ : StrandDiagram α} {x y a b : α} (ha : a ∈ φ x)
    (hb : b ∈ φ y) :
    (x, y) ∈ φ.inversions ↔ x < y ∧ b < a := by
  rw [mem_inversions]
  refine ⟨fun ⟨hxy, a', ha', b', hb', h⟩ ↦ ⟨hxy, ?_⟩, fun ⟨hxy, h⟩ ↦ ⟨hxy, a, ha, b, hb, h⟩⟩
  rwa [Option.mem_unique ha' ha, Option.mem_unique hb' hb] at h

/-- For distinct `x` and `y`, the sorted pair `(min x y, max x y)` is a crossing exactly when the
strands from `x` and `y` reverse their order. -/
theorem min_max_mem_inversions_iff {φ : StrandDiagram α} {x y a b : α} (hxy : x ≠ y)
    (ha : a ∈ φ x) (hb : b ∈ φ y) : (min x y, max x y) ∈ φ.inversions ↔ (x < y ↔ b < a) := by
  have hab : a ≠ b := φ.ne_of_mem_of_mem_of_ne ha hb hxy
  rcases lt_or_gt_of_ne hxy with h | h
  · simp [min_eq_left h.le, max_eq_right h.le, mem_inversions_iff_of_mem ha hb, h]
  · simp only [min_eq_right h.le, max_eq_left h.le, mem_inversions_iff_of_mem hb ha, h,
      true_and, h.not_gt, false_iff, not_lt]
    exact ⟨fun h' ↦ h'.le, fun h' ↦ lt_of_le_of_ne h' hab⟩

/-- The two strands of a crossing written as a sorted pair start at starting points of the
diagram. -/
theorem mem_source_of_min_max_mem_inversions {φ : StrandDiagram α} {x y : α}
    (h : (min x y, max x y) ∈ φ.inversions) : x ∈ φ.source ∧ y ∈ φ.source := by
  have h₁ := fst_mem_source_of_mem_inversions h
  have h₂ := snd_mem_source_of_mem_inversions h
  rcases le_total x y with hxy | hxy
  · simp only [min_eq_left hxy, max_eq_right hxy] at h₁ h₂
    exact ⟨h₁, h₂⟩
  · simp only [min_eq_right hxy, max_eq_left hxy] at h₁ h₂
    exact ⟨h₂, h₁⟩

/-- The number of crossings of a strand diagram, written `inv(φ)` by Lipshitz, Ozsváth and
Thurston. -/
def inversionCount (φ : StrandDiagram α) : ℕ :=
  #φ.inversions

theorem inversionCount_def (φ : StrandDiagram α) : φ.inversionCount = #φ.inversions :=
  (rfl)

@[simp]
theorem inversions_idOn (s : Finset α) : (idOn s).inversions = ∅ := by
  ext ⟨i, j⟩
  simp only [mem_inversions, mem_idOn, Finset.notMem_empty, iff_false, not_and, not_exists]
  rintro hij _ ⟨rfl, -⟩ _ ⟨rfl, -⟩
  exact hij.not_gt

@[simp]
theorem inversionCount_idOn (s : Finset α) : (idOn s).inversionCount = 0 := by
  simp [inversionCount_def]

/-- **Inversion counts are subadditive.** Every crossing of the concatenation of two strand
diagrams comes from a crossing of one of them: either the two strands already cross in `φ`, or
they run in order through `φ` and cross in `ψ`. -/
theorem inversionCount_trans_le (φ ψ : StrandDiagram α) :
    (φ.trans ψ).inversionCount ≤ φ.inversionCount + ψ.inversionCount := by
  classical
  set I := (φ.trans ψ).inversions
  rw [inversionCount_def, ← card_filter_add_card_filter_not (s := I) (· ∈ φ.inversions)]
  refine Nat.add_le_add (card_le_card fun p hp ↦ (mem_filter.1 hp).2) ?_
  -- A crossing of the composite that is not a crossing of `φ` is the image under `φ` of a
  -- crossing of `ψ`.
  have key : ∀ p ∈ I.filter (· ∉ φ.inversions), ∃ a ∈ φ p.1, ∃ b ∈ φ p.2,
      ((φ p.1).getD p.1, (φ p.2).getD p.2) = (a, b) ∧ (a, b) ∈ ψ.inversions := by
    rintro ⟨i, j⟩ hp
    rw [mem_filter, mem_inversions, mem_inversions] at hp
    obtain ⟨⟨hij, c, hc, d, hd, hdc⟩, hnot⟩ := hp
    obtain ⟨a, ha, hc⟩ := mem_trans.1 hc
    obtain ⟨b, hb, hd⟩ := mem_trans.1 hd
    have hab : a < b := by
      refine lt_of_le_of_ne (not_lt.1 fun hba ↦ hnot ⟨hij, a, ha, b, hb, hba⟩) ?_
      rintro rfl
      exact hij.ne (φ.toPEquiv.inj ha hb)
    refine ⟨a, ha, b, hb, ?_, mem_inversions.2 ⟨hab, c, hc, d, hd, hdc⟩⟩
    rw [Option.mem_def] at ha hb
    simp [ha, hb]
  refine card_le_card_of_injOn (fun p ↦ ((φ p.1).getD p.1, (φ p.2).getD p.2)) ?_ ?_
  · intro p hp
    obtain ⟨a, -, b, -, he, hmem⟩ := key p hp
    simpa only [coe_filter, he, mem_coe] using hmem
  · intro p hp q hq he
    obtain ⟨a, ha, b, hb, hpe⟩ := key p hp
    obtain ⟨a', ha', b', hb', hqe⟩ := key q hq
    simp only [hpe.1, hqe.1, Prod.mk.injEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact Prod.ext (φ.toPEquiv.inj ha ha') (φ.toPEquiv.inj hb hb')

/-- Two strand diagrams are composable when the target of `φ` is the source of `ψ` and their
concatenation has no double crossing, that is, the inversion counts add:
`inv (φ.trans ψ) = inv φ + inv ψ`. The product of `φ` and `ψ` in the strands algebra is their
composite when they are composable and zero otherwise. -/
def Composable (φ ψ : StrandDiagram α) : Prop :=
  φ.target = ψ.source ∧ (φ.trans ψ).inversionCount = φ.inversionCount + ψ.inversionCount

theorem composable_iff {φ ψ : StrandDiagram α} :
    φ.Composable ψ ↔
      φ.target = ψ.source ∧ (φ.trans ψ).inversionCount = φ.inversionCount + ψ.inversionCount :=
  (Iff.rfl)

instance (φ ψ : StrandDiagram α) : Decidable (φ.Composable ψ) :=
  decidable_of_iff _ composable_iff.symm

theorem Composable.target_eq {φ ψ : StrandDiagram α} (h : φ.Composable ψ) :
    φ.target = ψ.source :=
  h.1

theorem Composable.inversionCount_trans {φ ψ : StrandDiagram α} (h : φ.Composable ψ) :
    (φ.trans ψ).inversionCount = φ.inversionCount + ψ.inversionCount :=
  h.2

/-- The two bracketings of a triple product in the strands algebra are nonzero under the same
condition: both say that `φ`, `ψ`, `χ` can be concatenated in turn and that
`inv (φ.trans ψ).trans χ = inv φ + inv ψ + inv χ`. -/
theorem trans_composable_and_composable_iff (φ ψ χ : StrandDiagram α) :
    (φ.trans ψ).Composable χ ∧ φ.Composable ψ ↔ φ.Composable (ψ.trans χ) ∧ ψ.Composable χ := by
  have h₁ := inversionCount_trans_le φ ψ
  have h₂ := inversionCount_trans_le ψ χ
  have h₃ := inversionCount_trans_le (φ.trans ψ) χ
  have h₄ := inversionCount_trans_le φ (ψ.trans χ)
  rw [trans_assoc] at h₃
  simp only [composable_iff]
  rw [trans_assoc]
  constructor
  · rintro ⟨⟨hT, hI⟩, hT', hI'⟩
    rw [target_trans_of_target_eq hT'] at hT
    refine ⟨⟨by rw [source_trans_of_target_eq hT, hT'], by omega⟩, hT, by omega⟩
  · rintro ⟨⟨hT, hI⟩, hT', hI'⟩
    rw [source_trans_of_target_eq hT'] at hT
    refine ⟨⟨by rw [target_trans_of_target_eq hT, hT'], by omega⟩, hT, by omega⟩

@[simp]
theorem composable_idOn_left_iff {s : Finset α} {φ : StrandDiagram α} :
    (idOn s).Composable φ ↔ s = φ.source := by
  refine ⟨fun h ↦ by simpa using h.target_eq, fun h ↦ ⟨by simpa using h, ?_⟩⟩
  rw [idOn_trans_of_eq_source h, inversionCount_idOn, zero_add]

@[simp]
theorem composable_idOn_right_iff {s : Finset α} {φ : StrandDiagram α} :
    φ.Composable (idOn s) ↔ φ.target = s := by
  refine ⟨fun h ↦ by simpa using h.target_eq, fun h ↦ ⟨by simpa using h, ?_⟩⟩
  rw [trans_idOn_of_target_eq h, inversionCount_idOn, add_zero]

end Finite

end StrandDiagram

end TauCeti
