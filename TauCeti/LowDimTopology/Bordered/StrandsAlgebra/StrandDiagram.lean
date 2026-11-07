/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.PEquiv
public import Mathlib.Data.Fintype.Prod
public import TauCeti.Data.Finset.Inversions

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
* `TauCeti.StrandDiagram.single`: the diagram with a single strand.
* `TauCeti.StrandDiagram.source`, `TauCeti.StrandDiagram.target`: the starting and ending points.
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

/-- The diagram with a single strand, from `i` up to `j`. -/
def single (i j : α) (h : i ≤ j) : StrandDiagram α where
  toPEquiv := PEquiv.single i j
  le_of_mem' _ _ hk := by
    obtain ⟨rfl, rfl⟩ := (PEquiv.mem_single_iff _ _ _ _).1 hk
    exact h

@[simp]
theorem single_apply (i j : α) (h : i ≤ j) (k : α) :
    single i j h k = if k = i then some j else none :=
  (rfl)

theorem mem_single {i j : α} {h : i ≤ j} {k l : α} : l ∈ single i j h k ↔ k = i ∧ l = j :=
  PEquiv.mem_single_iff _ _ _ _

@[simp]
theorem single_trans_single {i j k : α} (hij : i ≤ j) (hjk : j ≤ k) :
    (single i j hij).trans (single j k hjk) = single i k (hij.trans hjk) :=
  toPEquiv_injective (PEquiv.single_trans_single _ _ _)

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

/-- The starting point of a strand of `φ` lies outside any set disjoint from the source. -/
theorem notMem_of_mem_of_disjoint_source {φ : StrandDiagram α} {U : Finset α}
    (hs : Disjoint φ.source U) {i j : α} (hij : j ∈ φ i) : i ∉ U :=
  disjoint_left.1 hs (mem_source.2 ⟨j, hij⟩)

/-- The end point of a strand of `φ` lies outside any set disjoint from the target. -/
theorem notMem_of_mem_of_disjoint_target {φ : StrandDiagram α} {U : Finset α}
    (ht : Disjoint φ.target U) {i j : α} (hij : j ∈ φ i) : j ∉ U :=
  disjoint_left.1 ht (mem_target.2 ⟨i, hij⟩)

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
`φ j < φ i`. These are the inversions (`Finset.inversions`) of `φ` on its source. -/
def inversions (φ : StrandDiagram α) : Finset (α × α) :=
  φ.source.inversions fun i ↦ (φ i).getD i

theorem inversions_def (φ : StrandDiagram α) :
    φ.inversions = φ.source.inversions fun i ↦ (φ i).getD i :=
  (rfl)

@[simp]
theorem mem_inversions {φ : StrandDiagram α} {p : α × α} :
    p ∈ φ.inversions ↔ p.1 < p.2 ∧ ∃ a ∈ φ p.1, ∃ b ∈ φ p.2, b < a := by
  rw [inversions_def, Finset.mem_inversions, mem_source, mem_source]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, h⟩
    rw [Option.mem_def] at ha hb
    exact ⟨hab, a, ha, b, hb, by simpa [ha, hb] using h⟩
  · rintro ⟨hab, a, ha, b, hb, h⟩
    rw [Option.mem_def] at ha hb
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, hab, by simpa [ha, hb] using h⟩

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

@[simp]
theorem source_single (i j : α) (h : i ≤ j) : (single i j h).source = {i} := by
  ext k
  rw [mem_source, mem_singleton]
  simp only [mem_single]
  exact ⟨fun ⟨_, hk, _⟩ ↦ hk, fun hk ↦ ⟨j, hk, rfl⟩⟩

@[simp]
theorem target_single (i j : α) (h : i ≤ j) : (single i j h).target = {j} := by
  ext l
  rw [mem_target, mem_singleton]
  simp only [mem_single]
  exact ⟨fun ⟨_, _, hl⟩ ↦ hl, fun hl ↦ ⟨i, rfl, hl⟩⟩

/-- A single strand has no crossing. -/
@[simp]
theorem inversionCount_single (i j : α) (h : i ≤ j) : (single i j h).inversionCount = 0 := by
  rw [inversionCount_def, card_eq_zero, eq_empty_iff_forall_notMem]
  rintro ⟨a, b⟩ hab
  obtain ⟨hlt, _, ha, _, hb, -⟩ := mem_inversions.1 hab
  rw [mem_single] at ha hb
  exact hlt.ne (ha.1.trans hb.1.symm)

/-- Two single strands meeting end to start are composable. -/
theorem composable_single_single {i j k : α} (hij : i ≤ j) (hjk : j ≤ k) :
    (single i j hij).Composable (single j k hjk) :=
  composable_iff.2 ⟨by simp, by simp [single_trans_single]⟩

end Finite

end StrandDiagram

end TauCeti
