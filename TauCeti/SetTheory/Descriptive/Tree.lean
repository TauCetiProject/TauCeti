/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.SetTheory.Descriptive.Tree
public import Mathlib.SetTheory.Ordinal.Rank
import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.Polish

/-!
# Well-founded descriptive trees, ordinal ranks, and analytic boundedness

A descriptive tree `T : Descriptive.tree A` (a prefix-closed set of finite sequences in `List A`) is
**well-founded** (`Descriptive.Tree.IsWellFounded T`) when its immediate-extension relation
`Descriptive.Tree.ChildRel T` has no infinite descending chain—equivalently, when `T` has no
infinite branch `f : ℕ → A` all of whose initial segments `List.ofFn (fun i : Fin n => f i)` lie in
`T`.

Each well-founded tree carries a canonical ordinal rank `Descriptive.Tree.rank T` in the universe
of `A`, defined from `Acc.rank` under `T.ChildRel` as `⨆ u : T, Order.succ (h.apply u).rank` (and
`0` on `⊥` or on ill-founded trees). When `[] ∈ T`, the root has the largest node rank in `T`,
yielding the standard
subtree recursion
`rank T = Order.succ (⨆ a : A, rank (subAt T [a]))`
(`Descriptive.Tree.IsWellFounded.rank_eq_succ_iSup`), and more generally at any node `x ∈ T` via
Mathlib's residual tree `Descriptive.Tree.subAt T x`. Over a countable alphabet `A`, every
well-founded tree on `A` has countable rank (`rank T < ω₁`).

The main theorem is the **Lusin–Sierpiński / Kunen–Martin boundedness theorem** for analytic
families of well-founded trees (`MeasureTheory.AnalyticSet.exists_treeRank_lt_omega_one`): if
`s ⊆ X` is analytic and `F : X → Descriptive.tree A` over a countable alphabet `A` assigns a
well-founded tree to each `x ∈ s` so that `{x : s | u ∈ F x.1}` is closed in `s` for every finite
sequence `u : List A`, then some countable ordinal `β < ω₁` strictly bounds `rank (F x)` across all
`x ∈ s`. Only relative closedness of node membership (upper semicontinuity), not clopenness, is
needed: pulling an unbounded family back along a continuous surjection `(ℕ → ℕ) → s` produces
nested Baire cylinders and a sequence `f : ℕ → A` whose initial segments belong to trees at
parameters converging to a limit `z*`, so closedness places the entire infinite branch in the tree
at `z*`.

## Main definitions

* `Descriptive.Tree.ChildRel`: immediate one-element extension on the nodes of a descriptive tree.
* `Descriptive.Tree.IsWellFounded`: well-foundedness of `ChildRel` on a descriptive tree.
* `Descriptive.Tree.rank`: ordinal rank of a descriptive tree (`0` on `⊥` and on ill-founded trees).

## Main results

* `Descriptive.Tree.isWellFounded_iff_forall_exists_notMem` and
  `Descriptive.Tree.not_isWellFounded_iff`: a tree is well-founded iff every `f : ℕ → A` has a
  finite prefix outside `T`.
* `Descriptive.Tree.IsWellFounded.rank_eq_succ_iSup` and
  `Descriptive.Tree.IsWellFounded.rank_subAt_eq_succ_iSup`: the subtree recursion for `rank`.
* `Descriptive.Tree.IsWellFounded.rank_lt_omega_one`: on a countable alphabet, every well-founded
  tree has rank strictly below `ω₁`.
* `Descriptive.Tree.exists_rank_lt_omega_one_of_nat_nat`: boundedness below `ω₁` for families of
  well-founded trees indexed by Baire space `ℕ → ℕ` with closed node-membership sets.
* `MeasureTheory.AnalyticSet.exists_treeRank_lt_omega_one` and
  `MeasureTheory.AnalyticSet.exists_treeRank_lt_omega_one_of_isClosed`: boundedness below `ω₁` for
  analytic families of well-founded trees.

## References

* Alexander S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Sections 2.B and 2.E (well-founded trees and their ranks) and Theorem 31.1
  (boundedness for analytic sets of well-founded trees).
* The Baire-cylinder descent for analytic families of well-founded trees also appears in Cameron
  Freer's `cameronfreer/infinitary-logic` (checkpoint `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  Apache-2.0), `InfinitaryLogic/Descriptive/BFSeparation.lean`; here it is proved as a general
  theorem for `Descriptive.tree A` over an arbitrary countable alphabet `A` assuming only relative
  closedness of node-membership sets.
-/

public section

universe u

open Cardinal Filter Function Ordinal Set TopologicalSpace Topology

namespace Descriptive.Tree

variable {A : Type u} {S T : tree A}

/-! ### Immediate extensions and well-foundedness -/

/-- Immediate one-element extension on the nodes of a descriptive tree `T`: `ChildRel T v u` holds
when `v` is obtained by appending a single symbol to `u`. -/
def ChildRel (T : tree A) (v u : T) : Prop :=
  ∃ a : A, v.1 = u.1 ++ [a]

/-- Unfolding lemma for `Descriptive.Tree.ChildRel`. -/
@[simp]
theorem childRel_iff {v u : T} : ChildRel T v u ↔ ∃ a : A, v.1 = u.1 ++ [a] :=
  Iff.rfl

/-- A descriptive tree `T` is **well-founded** when its immediate-extension relation `ChildRel T`
is well-founded (equivalently, `T` has no infinite branch). -/
def IsWellFounded (T : tree A) : Prop :=
  WellFounded (ChildRel T)

/-- Unfolding lemma for `Descriptive.Tree.IsWellFounded`. -/
theorem isWellFounded_iff : IsWellFounded T ↔ WellFounded (ChildRel T) :=
  Iff.rfl

/-- Every node of a well-founded descriptive tree is accessible under `ChildRel`. -/
theorem IsWellFounded.apply (hT : IsWellFounded T) (u : T) : Acc (ChildRel T) u :=
  WellFounded.apply hT u

/-- The empty tree is well-founded. -/
@[simp]
theorem isWellFounded_bot : IsWellFounded (⊥ : tree A) :=
  ⟨fun u => False.elim u.2⟩

/-- A subtree of a well-founded tree is well-founded. -/
theorem IsWellFounded.mono (hST : S ≤ T) (hT : IsWellFounded T) : IsWellFounded S := by
  let incl : S → T := fun u => ⟨u.1, hST u.2⟩
  exact Subrelation.wf (r := InvImage (ChildRel T) incl) (fun ⟨a, h⟩ => ⟨a, h⟩)
    (InvImage.wf incl hT)

/-- Every residual subtree `Tree.subAt T x` of a well-founded tree is well-founded. -/
theorem IsWellFounded.subAt (hT : IsWellFounded T) (x : List A) :
    IsWellFounded (Tree.subAt T x) := by
  let push : Tree.subAt T x → T := fun u => ⟨x ++ u.1, u.2⟩
  refine Subrelation.wf (r := InvImage (ChildRel T) push) ?_ (InvImage.wf push hT)
  rintro v u ⟨a, h⟩
  exact ⟨a, by simp [push, h, List.append_assoc]⟩

/-- Any inaccessible node of `T` propagates inaccessibility back to all of its prefixes. -/
private theorem not_acc_of_append {x l : List A} (hxl : x ++ l ∈ T)
    (h : ¬ Acc (ChildRel T) ⟨x ++ l, hxl⟩) :
    ¬ Acc (ChildRel T) ⟨x, mem_of_append hxl⟩ := by
  induction l generalizing x with
  | nil => simpa using h
  | cons a ls ih =>
    have hxl' : (x ++ [a]) ++ ls ∈ T := by simpa [List.append_assoc] using hxl
    have hxa : ¬ Acc (ChildRel T) ⟨x ++ [a], mem_of_append hxl'⟩ :=
      ih hxl' (by simpa [List.append_assoc] using h)
    exact fun hx => hxa (hx.inv ⟨a, rfl⟩)

/-- A well-founded tree admits no infinite branch: every sequence `f : ℕ → A` has a finite initial
segment outside `T`. -/
theorem IsWellFounded.exists_notMem (hT : IsWellFounded T) (f : ℕ → A) :
    ∃ n, List.ofFn (fun i : Fin n => f i) ∉ T := by
  by_contra! hmem
  let u : ℕ → T := fun n => ⟨List.ofFn (fun i : Fin n => f i), hmem n⟩
  have hstep (n : ℕ) : ChildRel T (u (n + 1)) (u n) := by
    refine ⟨f n, ?_⟩
    dsimp [u]
    rw [List.ofFn_succ', List.concat_eq_append]
    simp
  exact (wellFounded_iff_isEmpty_descending_chain.mp hT).false ⟨u, hstep⟩

/-- **Infinite-branch characterization of ill-foundedness.** A descriptive tree fails to be
well-founded precisely when some `f : ℕ → A` has every finite initial segment in `T`. -/
theorem not_isWellFounded_iff :
    ¬ IsWellFounded T ↔ ∃ f : ℕ → A, ∀ n, List.ofFn (fun i : Fin n => f i) ∈ T := by
  refine ⟨fun hnot => ?_, fun ⟨f, hf⟩ hT => ?_⟩
  · have hex : ∃ u : T, ¬ Acc (ChildRel T) u := by
      by_contra! hall
      exact hnot ⟨hall⟩
    obtain ⟨u₀, hu₀⟩ := hex
    have hnil : [] ∈ T := mem_of_prefix List.nil_prefix u₀.2
    have hroot : ¬ Acc (ChildRel T) ⟨[], hnil⟩ :=
      not_acc_of_append (x := []) (l := u₀.1) (by simp) (by simp [hu₀])
    obtain ⟨c, hc0, hstep⟩ := not_acc_iff_exists_descending_chain.mp hroot
    choose f hf using hstep
    have hpath (n : ℕ) : (c n).1 = List.ofFn (fun i : Fin n => f i) := by
      induction n with
      | zero => simp [hc0]
      | succ n ih =>
        rw [hf n, ih, List.ofFn_succ', List.concat_eq_append]
        simp
    exact ⟨f, fun n => hpath n ▸ (c n).2⟩
  · obtain ⟨n, hn⟩ := hT.exists_notMem f
    exact hn (hf n)

/-- **Infinite-branch characterization of well-foundedness.** A descriptive tree is well-founded
precisely when every `f : ℕ → A` has a finite initial segment outside `T`. -/
theorem isWellFounded_iff_forall_exists_notMem :
    IsWellFounded T ↔ ∀ f : ℕ → A, ∃ n, List.ofFn (fun i : Fin n => f i) ∉ T := by
  rw [← not_iff_not, not_isWellFounded_iff]
  push Not
  rfl

/-! ### Ordinal rank of a descriptive tree -/

open scoped Classical in
/-- The **ordinal rank** of a descriptive tree `T` on `A`: for a well-founded tree, the supremum of
`Order.succ` of the `ChildRel`-ranks of its nodes (`0` when `T = ⊥`), and `0` if `T` is not
well-founded. -/
noncomputable def rank (T : tree A) : Ordinal.{u} :=
  if h : IsWellFounded T then ⨆ u : T, Order.succ (h.apply u).rank else 0

/-- An ill-founded tree has rank `0` by convention. -/
theorem rank_of_not_isWellFounded (h : ¬ IsWellFounded T) : rank T = 0 := by
  simp [rank, h]

/-- On a well-founded tree, `rank T` unfolds to the supremum of successor node ranks. -/
theorem IsWellFounded.rank_eq_iSup (hT : IsWellFounded T) :
    rank T = ⨆ u : T, Order.succ (hT.apply u).rank := by
  simp [rank, hT]

/-- The empty tree has rank `0`. -/
@[simp]
theorem rank_bot : rank (⊥ : tree A) = 0 := by
  rw [isWellFounded_bot.rank_eq_iSup]
  exact le_antisymm (Ordinal.iSup_le fun u => False.elim u.2) zero_le

/-- Any tree not containing the root `[]` is empty and therefore has rank `0`. -/
theorem rank_eq_zero_of_notMem (h : [] ∉ T) : rank T = 0 := by
  rw [tree_eq_bot.mpr h, rank_bot]

/-- A residual subtree `Tree.subAt T x` at a sequence `x ∉ T` is empty and therefore has rank `0`.
-/
theorem rank_subAt_eq_zero_of_notMem {x : List A} (h : x ∉ T) : rank (Tree.subAt T x) = 0 :=
  rank_eq_zero_of_notMem (by simpa using h)

/-- A nonempty well-founded tree has positive rank. -/
theorem IsWellFounded.rank_pos (hT : IsWellFounded T) (h : [] ∈ T) : 0 < rank T := by
  rw [hT.rank_eq_iSup]
  exact zero_le.trans_lt ((Order.lt_succ _).trans_le
    (Ordinal.le_iSup (fun u : T => Order.succ (hT.apply u).rank) ⟨[], h⟩))

/-- At any node `x ∈ T` of a well-founded tree, the residual subtree `Tree.subAt T x` has positive
rank. -/
theorem IsWellFounded.rank_subAt_pos (hT : IsWellFounded T) {x : List A} (hx : x ∈ T) :
    0 < rank (Tree.subAt T x) :=
  (hT.subAt x).rank_pos (by simpa using hx)

/-- A well-founded tree has rank `0` iff it is empty. -/
@[simp]
theorem IsWellFounded.rank_eq_zero_iff (hT : IsWellFounded T) : rank T = 0 ↔ T = ⊥ := by
  refine ⟨fun h0 => ?_, fun hbot => hbot ▸ rank_bot⟩
  rw [tree_eq_bot]
  exact fun h => (hT.rank_pos h).ne' h0

/-- Deeper nodes in a well-founded tree have smaller or equal `ChildRel`-rank. -/
private theorem nodeRank_le_of_append (hT : IsWellFounded T) {x l : List A} (hxl : x ++ l ∈ T) :
    (hT.apply ⟨x ++ l, hxl⟩).rank ≤ (hT.apply ⟨x, mem_of_append hxl⟩).rank := by
  induction l generalizing x with
  | nil => simp
  | cons a ls ih =>
    have hxl' : (x ++ [a]) ++ ls ∈ T := by simpa [List.append_assoc] using hxl
    have hle : (hT.apply ⟨x ++ (a :: ls), hxl⟩).rank ≤
        (hT.apply ⟨x ++ [a], mem_of_append hxl'⟩).rank := by
      simpa [List.append_assoc] using ih hxl'
    have hlt : (hT.apply ⟨x ++ [a], mem_of_append hxl'⟩).rank <
        (hT.apply ⟨x, mem_of_append hxl⟩).rank :=
      (hT.apply ⟨x, mem_of_append hxl⟩).rank_lt_of_rel ⟨a, rfl⟩
    exact hle.trans hlt.le

/-- On a nonempty well-founded tree, `rank T` is the successor of the root's `ChildRel`-rank. -/
private theorem rank_eq_succ_root (hT : IsWellFounded T) (h : [] ∈ T) :
    rank T = Order.succ (hT.apply ⟨[], h⟩).rank := by
  rw [hT.rank_eq_iSup]
  refine le_antisymm (Ordinal.iSup_le fun u => Order.succ_le_succ ?_)
    (Ordinal.le_iSup (fun u : T => Order.succ (hT.apply u).rank) ⟨[], h⟩)
  simpa using nodeRank_le_of_append hT (x := []) (l := u.1) (by simp)

/-- Node rank in the residual tree `Tree.subAt T x` equals node rank at the shifted node in `T`. -/
private theorem nodeRank_subAt_eq (hT : IsWellFounded T) (x : List A) (u : Tree.subAt T x) :
    ((hT.subAt x).apply u).rank = (hT.apply ⟨x ++ u.1, u.2⟩).rank := by
  induction u using (hT.subAt x).induction with
  | h u ih =>
    rw [((hT.subAt x).apply u).rank_eq, (hT.apply ⟨x ++ u.1, u.2⟩).rank_eq]
    refine le_antisymm (Ordinal.iSup_le fun v => ?_) (Ordinal.iSup_le fun w => ?_)
    · obtain ⟨a, hv⟩ := v.2
      have hw : ChildRel T ⟨x ++ v.1, v.1.2⟩ ⟨x ++ u.1, u.2⟩ :=
        ⟨a, by simp [hv, List.append_assoc]⟩
      have hih : (((hT.subAt x).apply u).inv v.2).rank = (hT.apply ⟨x ++ v.1, v.1.2⟩).rank :=
        ih v.1 v.2
      rw [hih]
      exact Ordinal.le_iSup
        (fun w : {w : T // ChildRel T w ⟨x ++ u.1, u.2⟩} =>
          Order.succ ((hT.apply ⟨x ++ u.1, u.2⟩).inv w.2).rank)
        ⟨⟨x ++ v.1, v.1.2⟩, hw⟩
    · obtain ⟨a, hw⟩ := w.2
      have hmem : u.1 ++ [a] ∈ Tree.subAt T x := by
        rw [mem_subAt, ← List.append_assoc, ← hw]
        exact w.1.2
      let v : Tree.subAt T x := ⟨u.1 ++ [a], hmem⟩
      have hv : ChildRel (Tree.subAt T x) v u := ⟨a, rfl⟩
      have hweq : (⟨x ++ v.1, v.2⟩ : T) = w.1 :=
        Subtype.ext (by simp [v, List.append_assoc, hw])
      have hle := Ordinal.le_iSup
        (fun v' : {v' : Tree.subAt T x // ChildRel (Tree.subAt T x) v' u} =>
          Order.succ (((hT.subAt x).apply u).inv v'.2).rank)
        ⟨v, hv⟩
      have hih : (((hT.subAt x).apply u).inv hv).rank = (hT.apply w.1).rank := by
        simpa only [hweq] using ih v hv
      exact hih ▸ hle

/-- **Subtree recursion at the root.** On a nonempty well-founded tree `T`, the rank of `T` is the
successor of the supremum of the ranks of its immediate residual subtrees `Tree.subAt T [a]`. -/
theorem IsWellFounded.rank_eq_succ_iSup (hT : IsWellFounded T) (h : [] ∈ T) :
    rank T = Order.succ (⨆ a : A, rank (Tree.subAt T [a])) := by
  rw [rank_eq_succ_root hT h, Order.succ_eq_succ_iff, (hT.apply ⟨[], h⟩).rank_eq]
  refine le_antisymm (Ordinal.iSup_le fun v => ?_) (Ordinal.iSup_le fun a => ?_)
  · obtain ⟨a, hv⟩ := v.2
    have ha : [] ∈ Tree.subAt T [a] := by simpa [hv] using v.1.2
    have hveq : (⟨[a] ++ ([] : List A), ha⟩ : T) = v.1 := Subtype.ext (by simp [hv])
    have hrw : rank (Tree.subAt T [a]) = Order.succ (hT.apply v.1).rank := by
      rw [rank_eq_succ_root (hT.subAt [a]) ha, nodeRank_subAt_eq hT [a] ⟨[], ha⟩, hveq]
    exact hrw ▸ Ordinal.le_iSup (fun b : A => rank (Tree.subAt T [b])) a
  · by_cases ha : [a] ∈ T
    · have ha' : [] ∈ Tree.subAt T [a] := by simpa using ha
      let v : T := ⟨[a], ha⟩
      have hv : ChildRel T v ⟨[], h⟩ := ⟨a, rfl⟩
      rw [rank_eq_succ_root (hT.subAt [a]) ha', nodeRank_subAt_eq hT [a] ⟨[], ha'⟩]
      exact Ordinal.le_iSup
        (fun w : {w : T // ChildRel T w ⟨[], h⟩} =>
          Order.succ ((hT.apply ⟨[], h⟩).inv w.2).rank)
        ⟨v, hv⟩
    · rw [rank_subAt_eq_zero_of_notMem ha]
      exact zero_le

/-- **Subtree recursion at any node.** On a well-founded tree `T`, for every `x ∈ T` the rank of
`Tree.subAt T x` is the successor of the supremum of the ranks of `Tree.subAt T (x ++ [a])`. -/
theorem IsWellFounded.rank_subAt_eq_succ_iSup (hT : IsWellFounded T) {x : List A} (hx : x ∈ T) :
    rank (Tree.subAt T x) = Order.succ (⨆ a : A, rank (Tree.subAt T (x ++ [a]))) := by
  have hnil : [] ∈ Tree.subAt T x := by simpa using hx
  simpa only [subAt_append] using (hT.subAt x).rank_eq_succ_iSup hnil

/-- Tree rank is monotone among subtrees of a well-founded tree. -/
theorem IsWellFounded.rank_mono (hST : S ≤ T) (hT : IsWellFounded T) : rank S ≤ rank T := by
  have hS : IsWellFounded S := hT.mono hST
  have hnode : ∀ u : S, (hS.apply u).rank ≤ (hT.apply ⟨u.1, hST u.2⟩).rank := by
    intro u
    induction u using hS.induction with
    | h u ih =>
      rw [(hS.apply u).rank_eq, (hT.apply ⟨u.1, hST u.2⟩).rank_eq]
      refine Ordinal.iSup_le fun v => ?_
      obtain ⟨a, hv⟩ := v.2
      exact (Order.succ_le_succ (ih v.1 v.2)).trans
        (Ordinal.le_iSup
          (fun w : {w : T // ChildRel T w ⟨u.1, hST u.2⟩} =>
            Order.succ ((hT.apply ⟨u.1, hST u.2⟩).inv w.2).rank)
          ⟨⟨v.1.1, hST v.1.2⟩, ⟨a, hv⟩⟩)
  rw [hS.rank_eq_iSup, hT.rank_eq_iSup]
  exact Ordinal.iSup_le fun u => (Order.succ_le_succ (hnode u)).trans
    (Ordinal.le_iSup (fun w : T => Order.succ (hT.apply w).rank) ⟨u.1, hST u.2⟩)

/-- **Countable-alphabet bound.** Every well-founded descriptive tree over a countable alphabet `A`
has ordinal rank strictly below `ω₁`. -/
theorem IsWellFounded.rank_lt_omega_one [Countable A] (hT : IsWellFounded T) : rank T < ω₁ := by
  have hnode : ∀ u : T, (hT.apply u).rank < ω₁ := by
    intro u
    induction u using hT.induction with
    | h u ih =>
      rw [(hT.apply u).rank_eq]
      exact Ordinal.iSup_lt_omega_one fun v =>
        (Cardinal.isSuccLimit_omega 1).succ_lt (ih v.1 v.2)
  rw [hT.rank_eq_iSup]
  exact Ordinal.iSup_lt_omega_one fun u =>
    (Cardinal.isSuccLimit_omega 1).succ_lt (hnode u)

/-! ### Boundedness for Baire-indexed and analytic families of well-founded trees -/

/-- Unboundedness of subtree ranks at a node `u` across a Baire-space cylinder `PiNat.cylinder z n`.
-/
private def RankUnboundedOnCylinder (F : (ℕ → ℕ) → tree A) (z : ℕ → ℕ) (n : ℕ) (u : List A) :
    Prop :=
  ∀ β : Ordinal.{u}, β < ω₁ → ∃ w ∈ PiNat.cylinder z n, β ≤ rank (Tree.subAt (F w) u)

/-- Refining a cylinder of length `n` to length `n + 1` preserves unboundedness at `u` for at least
one next coordinate `k : ℕ`, by regularity of `ω₁`. -/
private theorem exists_cylinder_succ_unbounded {F : (ℕ → ℕ) → tree A} {z : ℕ → ℕ} {n : ℕ}
    {u : List A} (hunb : RankUnboundedOnCylinder F z n u) :
    ∃ k : ℕ, RankUnboundedOnCylinder F (Function.update z n k) (n + 1) u := by
  by_contra hbdd
  simp only [RankUnboundedOnCylinder] at hbdd
  push Not at hbdd
  choose β hβ hlt using hbdd
  have hsup : ⨆ k : ℕ, β k < ω₁ := Ordinal.iSup_lt_omega_one hβ
  obtain ⟨w, hw, hle⟩ := hunb (⨆ k : ℕ, β k) hsup
  rw [← PiNat.iUnion_cylinder_update z n, mem_iUnion] at hw
  obtain ⟨k, hwk⟩ := hw
  exact (hlt k w hwk).not_ge ((Ordinal.le_iSup β k).trans hle)

/-- Extending the node `u` by one symbol `a : A` preserves unboundedness on a fixed cylinder for at
least one `a`, by the subtree rank recursion and regularity of `ω₁`. -/
private theorem exists_append_unbounded [Countable A] {F : (ℕ → ℕ) → tree A}
    (hwf : ∀ z, IsWellFounded (F z)) {z : ℕ → ℕ} {n : ℕ} {u : List A}
    (hunb : RankUnboundedOnCylinder F z n u) :
    ∃ a : A, RankUnboundedOnCylinder F z n (u ++ [a]) := by
  by_contra hbdd
  simp only [RankUnboundedOnCylinder] at hbdd
  push Not at hbdd
  choose γ hγ hlt using hbdd
  have hsup : ⨆ a : A, γ a < ω₁ := Ordinal.iSup_lt_omega_one hγ
  have hsucc : Order.succ (⨆ a : A, γ a) < ω₁ := (Cardinal.isSuccLimit_omega 1).succ_lt hsup
  have hsucc2 : Order.succ (Order.succ (⨆ a : A, γ a)) < ω₁ :=
    (Cardinal.isSuccLimit_omega 1).succ_lt hsucc
  obtain ⟨w, hw, hle⟩ := hunb _ hsucc2
  by_cases hu : u ∈ F w
  · rw [(hwf w).rank_subAt_eq_succ_iSup hu, Order.succ_le_succ_iff] at hle
    have hbound : ⨆ a : A, rank (Tree.subAt (F w) (u ++ [a])) ≤ ⨆ a : A, γ a :=
      Ordinal.iSup_le fun a => (hlt a w hw).le.trans (Ordinal.le_iSup γ a)
    exact (Order.lt_succ _).not_ge (hle.trans hbound)
  · rw [rank_subAt_eq_zero_of_notMem hu] at hle
    exact (Order.lt_succ (0 : Ordinal.{u})).not_ge
      (hle.trans' (Order.succ_le_succ zero_le))

/-- **A branch with unbounded witnesses.** If the subtree ranks of a family of well-founded trees
are unbounded on the whole Baire space at the root, there are a point `zStar` and a branch `branch`
such that, for every `m`, the `m`-th cylinder of `zStar` contains a point whose tree holds the
`m`-th prefix of `branch`. -/
private theorem exists_branch_of_rankUnboundedOnCylinder [Countable A] {F : (ℕ → ℕ) → tree A}
    (hwf : ∀ z, IsWellFounded (F z)) (hroot : RankUnboundedOnCylinder F (fun _ => 0) 0 []) :
    ∃ (zStar : ℕ → ℕ) (branch : ℕ → A), ∀ m : ℕ,
      ∃ w ∈ PiNat.cylinder zStar m, List.ofFn (fun i : Fin m => branch i) ∈ F w := by
  -- Simultaneously refine the Baire cylinder and extend the tree node one step at a time.
  let State := {q : (ℕ → ℕ) × ℕ × List A // RankUnboundedOnCylinder F q.1 q.2.1 q.2.2}
  have hstep : ∀ s : State,
      ∃ (k : ℕ) (a : A),
        RankUnboundedOnCylinder F (Function.update s.1.1 s.1.2.1 k) (s.1.2.1 + 1)
          (s.1.2.2 ++ [a]) := fun s => by
    obtain ⟨k, hk⟩ := exists_cylinder_succ_unbounded s.2
    obtain ⟨a, ha⟩ := exists_append_unbounded hwf hk
    exact ⟨k, a, ha⟩
  choose nextCoord nextSym nextUnb using hstep
  let next : State → State := fun s =>
    ⟨(Function.update s.1.1 s.1.2.1 (nextCoord s), s.1.2.1 + 1, s.1.2.2 ++ [nextSym s]),
      nextUnb s⟩
  let s₀ : State := ⟨(fun _ => 0, 0, []), hroot⟩
  let s : ℕ → State := fun n => next^[n] s₀
  have hlen (n : ℕ) : (s n).1.2.1 = n := by
    induction n with
    | zero => rfl
    | succ n ih => simp [s, next, Function.iterate_succ_apply', ih]
  have hs (n : ℕ) : s (n + 1) = next (s n) := Function.iterate_succ_apply' next n s₀
  let zStar : ℕ → ℕ := fun n => nextCoord (s n)
  let branch : ℕ → A := fun n => nextSym (s n)
  have hbranch (n : ℕ) : (s n).1.2.2 = List.ofFn (fun i : Fin n => branch i) := by
    induction n with
    | zero => simp [s, s₀]
    | succ n ih =>
      rw [hs n, List.ofFn_succ', List.concat_eq_append]
      simp [next, ih, branch]
  have hcyl (n : ℕ) : ∀ i < n, (s n).1.1 i = zStar i := by
    induction n with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i)
    | succ n ih =>
      intro i hi
      rw [hs n]
      simp only [next, hlen n]
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | rfl
      · rw [Function.update_of_ne hlt.ne, ih i hlt]
      · simp [zStar]
  -- At each stage `m`, unboundedness at `1 < ω₁` gives a point `w m` in the `m`-th cylinder of
  -- `zStar` whose tree contains the `m`-th prefix of `branch`.
  have h1 : (1 : Ordinal.{u}) < ω₁ := by
    simpa using (Cardinal.isSuccLimit_omega 1).succ_lt (Ordinal.omega_pos 1)
  have hwit (m : ℕ) :
      ∃ w ∈ PiNat.cylinder zStar m, List.ofFn (fun i : Fin m => branch i) ∈ F w := by
    obtain ⟨w, hw, hle⟩ := (s m).2 1 h1
    rw [hlen m] at hw
    rw [hbranch m] at hle
    refine ⟨w, PiNat.mem_cylinder_iff.mpr fun i hi => ?_, ?_⟩
    · exact (PiNat.mem_cylinder_iff.mp hw i hi).trans (hcyl m i hi)
    · by_contra hnot
      rw [rank_subAt_eq_zero_of_notMem hnot] at hle
      exact zero_lt_one.not_ge hle
  exact ⟨zStar, branch, hwit⟩

/-- **Boundedness on Baire space.** Let `F : (ℕ → ℕ) → tree A` be a family of well-founded trees
over a countable alphabet `A` such that `{z | u ∈ F z}` is closed in `ℕ → ℕ` for every finite
sequence `u : List A`. Then some countable ordinal `β < ω₁` strictly bounds `rank (F z)` across all
`z : ℕ → ℕ`. -/
theorem exists_rank_lt_omega_one_of_nat_nat [Countable A] (F : (ℕ → ℕ) → tree A)
    (hwf : ∀ z, IsWellFounded (F z)) (hcl : ∀ u : List A, IsClosed {z : ℕ → ℕ | u ∈ F z}) :
    ∃ β : Ordinal.{u}, β < ω₁ ∧ ∀ z, rank (F z) < β := by
  by_contra! hunb_root
  have hroot : RankUnboundedOnCylinder F (fun _ => 0) 0 [] := fun β hβ => by
    obtain ⟨w, hw⟩ := hunb_root β hβ
    exact ⟨w, by simp, by simpa using hw⟩
  obtain ⟨zStar, branch, hwit⟩ := exists_branch_of_rankUnboundedOnCylinder hwf hroot
  choose w hw_cyl hw_mem using hwit
  have htend : Tendsto w atTop (𝓝 zStar) :=
    tendsto_pi_nhds.mpr fun i => tendsto_atTop_of_eventually_const (i₀ := i + 1)
      fun m hm => PiNat.mem_cylinder_iff.mp (hw_cyl m) i (by omega)
  -- Closedness of `{z | u ∈ F z}` puts every finite prefix of `branch` into `F zStar`.
  have hall (n : ℕ) : List.ofFn (fun i : Fin n => branch i) ∈ F zStar := by
    refine (hcl _).mem_of_tendsto htend ?_
    filter_upwards [eventually_ge_atTop n] with m hm
    exact Fin.ofFn_take_eq_take_ofFn hm (fun i : Fin m => branch i) ▸ take_mem ⟨_, hw_mem m⟩
  obtain ⟨n, hn⟩ := (hwf zStar).exists_notMem branch
  exact hn (hall n)

end Descriptive.Tree

namespace MeasureTheory

open Descriptive Descriptive.Tree

/-- **Lusin–Sierpiński / Kunen–Martin boundedness theorem** (relative form). Let `s` be an analytic
subset of a topological space `X` and `F : X → Descriptive.tree A` a family of descriptive trees
over a countable alphabet `A : Type u`. Suppose `F x` is well-founded for every `x ∈ s` and
`{x : s | u ∈ F x.1}` is closed in the subspace `s` for every finite sequence `u : List A`. Then
some countable ordinal `β < ω₁` strictly bounds `rank (F x)` across all `x ∈ s`. -/
theorem AnalyticSet.exists_treeRank_lt_omega_one {X : Type*} [TopologicalSpace X] {A : Type u}
    [Countable A] {s : Set X} (hs : AnalyticSet s) (F : X → tree A)
    (hwf : ∀ x ∈ s, IsWellFounded (F x))
    (hcl : ∀ u : List A, IsClosed {x : s | u ∈ F x.1}) :
    ∃ β : Ordinal.{u}, β < ω₁ ∧ ∀ x ∈ s, rank (F x) < β := by
  obtain ⟨Y, _, _, f, hf, rfl⟩ := analyticSet_iff_exists_polishSpace_range.mp hs
  rcases isEmpty_or_nonempty Y with hY | hY
  · refine ⟨0, Ordinal.omega_pos 1, ?_⟩
    rintro _ ⟨y, rfl⟩
    exact isEmptyElim y
  · obtain ⟨g, hg, hsurj⟩ := PolishSpace.exists_nat_nat_continuous_surjective Y
    let toS : (ℕ → ℕ) → range f := fun z => ⟨f (g z), mem_range_self (g z)⟩
    have htoS : Continuous toS := (hf.comp hg).subtype_mk fun z => mem_range_self (g z)
    obtain ⟨β, hβ, hb⟩ := exists_rank_lt_omega_one_of_nat_nat (fun z => F (toS z).1)
      (fun z => hwf (toS z).1 (toS z).2)
      (fun u => (hcl u).preimage htoS)
    refine ⟨β, hβ, ?_⟩
    rintro _ ⟨y, rfl⟩
    obtain ⟨z, rfl⟩ := hsurj y
    exact hb z

/-- **Lusin–Sierpiński / Kunen–Martin boundedness theorem** (ambient-closed form). If `s ⊆ X` is
analytic, `F x` is well-founded for every `x ∈ s`, and `{x : X | u ∈ F x}` is closed in `X` for
every finite sequence `u : List A`, then some countable ordinal `β < ω₁` strictly bounds
`rank (F x)` across all `x ∈ s`. -/
theorem AnalyticSet.exists_treeRank_lt_omega_one_of_isClosed {X : Type*} [TopologicalSpace X]
    {A : Type u} [Countable A] {s : Set X} (hs : AnalyticSet s) (F : X → tree A)
    (hwf : ∀ x ∈ s, IsWellFounded (F x))
    (hcl : ∀ u : List A, IsClosed {x : X | u ∈ F x}) :
    ∃ β : Ordinal.{u}, β < ω₁ ∧ ∀ x ∈ s, rank (F x) < β :=
  hs.exists_treeRank_lt_omega_one F hwf fun u => (hcl u).preimage continuous_subtype_val

end MeasureTheory
