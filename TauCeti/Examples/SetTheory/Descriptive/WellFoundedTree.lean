/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.KleeneBrouwer

/-!
# Regression examples: bodies, tree ranks and the Kleene–Brouwer order

These examples exercise the tree API from a downstream module, through public statements only:

* the empty tree and the tree of the root alone have empty bodies; the second one detects a body
  that tests only the empty initial segment;
* the tree of constant-zero sequences has the zero sequence as its only branch, and the full tree
  has a branch;
* the empty tree has rank `0` and the root alone has rank `1`, so the rank is the strict supremum
  of the node ranks;
* the tree of strictly decreasing sequences of natural numbers is well-founded of rank `ω + 1`;
* the Kleene–Brouwer order puts a proper extension first, and otherwise lets the first difference
  decide.
-/

public section

open Descriptive Descriptive.Tree Ordinal

namespace TauCeti.WellFoundedTreeExamples

/-- The tree consisting of the root alone. -/
def rootTree : tree ℕ :=
  ⟨{[]}, fun _ _ h => by simp at h⟩

/-- Membership in the tree of the root alone. -/
theorem mem_rootTree {l : List ℕ} : l ∈ rootTree ↔ l = [] :=
  Iff.rfl

/-- The tree of the root alone has no branch. -/
theorem body_rootTree : body rootTree = ∅ :=
  Set.eq_empty_of_forall_notMem fun x hx => by
    simpa [initialSegment_succ, mem_rootTree] using mem_body.1 hx 1

-- The empty tree has empty body.
example : body (⊥ : tree ℕ) = ∅ := body_bot

-- The root alone has empty body: its initial segment of length `1` is not a node.
example : body rootTree = ∅ := body_rootTree

/-- The tree of constant-zero sequences. -/
def zeroTree : tree ℕ :=
  ⟨{l | ∀ a ∈ l, a = 0}, fun _ _ h b hb => h b (List.mem_append_left _ hb)⟩

-- The tree of constant-zero sequences has the zero sequence as its only branch.
example : body zeroTree = {fun _ => 0} := by
  ext x
  refine ⟨fun hx => funext fun n => mem_body.1 hx (n + 1) (x n) ?_, fun hx => mem_body.2 ?_⟩
  · simp [initialSegment_succ]
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    intro n a ha
    rw [initialSegment_def, List.mem_ofFn'] at ha
    obtain ⟨i, rfl⟩ := ha
    rfl

-- The full tree has a branch.
example : (body (⊤ : tree ℕ)).Nonempty :=
  ⟨fun _ => 0, mem_body.2 fun _ => by simp⟩

-- The empty tree has rank `0`.
example : rank (⊥ : tree ℕ) = 0 := rank_bot

-- The root alone has rank `1`: the supremum of the node ranks without the successor would be `0`.
example : rank rootTree = 1 := by
  have hwf : IsWellFounded rootTree := isWellFounded_iff_body_eq_empty.2 body_rootTree
  have hsub (a : ℕ) : subAt rootTree [a] = ⊥ := tree_eq_bot.2 (by simp [mem_rootTree])
  simp [hwf.rank_eq_succ_iSup (mem_rootTree.2 rfl), hsub]

/-- The predicate of the tree of strictly decreasing sequences of natural numbers below `m`. -/
def DecBelow (m : ℕ) (l : List ℕ) : Prop :=
  l.Pairwise (· > ·) ∧ ∀ a ∈ l, a < m

/-- The tree of strictly decreasing sequences of natural numbers below `m`. -/
def decBelow (m : ℕ) : tree ℕ :=
  ⟨{l | DecBelow m l}, fun _ _ h =>
    ⟨h.1.sublist (List.sublist_append_left _ _), fun b hb => h.2 b (List.mem_append_left _ hb)⟩⟩

/-- The tree of strictly decreasing sequences of natural numbers. -/
def decTree : tree ℕ :=
  ⟨{l | l.Pairwise (· > ·)}, fun _ _ h => h.sublist (List.sublist_append_left _ _)⟩

/-- Membership in the tree of strictly decreasing sequences below `m`. -/
theorem mem_decBelow {m : ℕ} {l : List ℕ} :
    l ∈ decBelow m ↔ l.Pairwise (· > ·) ∧ ∀ a ∈ l, a < m :=
  Iff.rfl

/-- Membership in the tree of strictly decreasing sequences. -/
theorem mem_decTree {l : List ℕ} : l ∈ decTree ↔ l.Pairwise (· > ·) :=
  Iff.rfl

/-- Below the node `[a]`, the decreasing sequences are those below `a`. -/
theorem subAt_decTree (a : ℕ) : subAt decTree [a] = decBelow a := by
  ext l
  simp only [mem_subAt, mem_decTree, mem_decBelow, List.singleton_append, List.pairwise_cons]
  exact and_comm

/-- Below a node `[a]` with `a < m`, the decreasing sequences below `m` are those below `a`. -/
theorem subAt_decBelow_of_lt {m a : ℕ} (ha : a < m) :
    subAt (decBelow m) [a] = decBelow a := by
  ext l
  simp only [mem_subAt, mem_decBelow, List.singleton_append, List.pairwise_cons, List.mem_cons,
    forall_eq_or_imp]
  exact ⟨fun h => ⟨h.1.2, h.1.1⟩, fun h => ⟨⟨h.2, h.1⟩, ha, fun b hb => (h.2 b hb).trans ha⟩⟩

/-- There is no node `[a]` with `m ≤ a` in the tree of decreasing sequences below `m`. -/
theorem subAt_decBelow_of_le {m a : ℕ} (ha : m ≤ a) : subAt (decBelow m) [a] = ⊥ :=
  tree_eq_bot.2 fun h => ((mem_decBelow.1 h).2 a (by simp)).not_ge ha

/-- The tree of strictly decreasing sequences has no branch. -/
theorem isWellFounded_decTree : IsWellFounded decTree := by
  refine isWellFounded_iff_body_eq_empty.2 (Set.eq_empty_of_forall_notMem fun x hx => ?_)
  have hstep (n : ℕ) : x (n + 1) < x n := by
    have h := mem_decTree.1 (mem_body.1 hx (n + 2))
    rw [initialSegment_succ, List.pairwise_append] at h
    exact h.2.2 (x n) (by simp [initialSegment_succ]) (x (n + 1)) (by simp)
  exact (wellFounded_iff_isEmpty_descending_chain.mp wellFounded_lt).false ⟨x, hstep⟩

/-- The tree of strictly decreasing sequences below `m` is well-founded. -/
theorem isWellFounded_decBelow (m : ℕ) : IsWellFounded (decBelow m) :=
  isWellFounded_decTree.mono fun _ h => (mem_decBelow.1 h).1

/-- The tree of strictly decreasing sequences below `a` has rank `a + 1`. -/
theorem rank_decBelow (a : ℕ) : rank (decBelow a) = Order.succ (a : Ordinal) := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    rw [(isWellFounded_decBelow a).rank_eq_succ_iSup (by simp [mem_decBelow])]
    congr 1
    refine le_antisymm (Ordinal.iSup_le fun b => ?_) ?_
    · rcases lt_or_ge b a with hb | hb
      · rw [subAt_decBelow_of_lt hb, ih b hb]
        exact Order.succ_le_of_lt (by exact_mod_cast hb)
      · rw [subAt_decBelow_of_le hb, rank_bot]
        exact zero_le
    · obtain _ | c := a
      · exact zero_le
      · refine le_trans ?_ (Ordinal.le_iSup _ c)
        rw [subAt_decBelow_of_lt c.lt_succ_self, ih c c.lt_succ_self]
        simp [Order.succ_eq_add_one]

-- The tree of strictly decreasing sequences is well-founded of rank `ω + 1`: its root has rank
-- `ω`, which would be the value of the supremum of the node ranks without the successor.
example : IsWellFounded decTree := isWellFounded_decTree

example : rank decTree = ω + 1 := by
  rw [isWellFounded_decTree.rank_eq_succ_iSup (by simp [mem_decTree]), Order.succ_eq_add_one]
  congr 1
  simp only [subAt_decTree, rank_decBelow]
  refine le_antisymm (Ordinal.iSup_le fun b => ?_) (Ordinal.omega0_le.2 fun n => ?_)
  · rw [Order.succ_eq_add_one, ← Nat.cast_succ]
    exact (Ordinal.natCast_lt_omega0 _).le
  · exact (Order.le_succ _).trans (Ordinal.le_iSup (fun b : ℕ => Order.succ (b : Ordinal)) n)

-- A proper extension comes first, unlike in the lexicographic order.
example : KBLT [0, 1] [0] := kbLT_of_prefix ⟨[1], rfl⟩ (by simp)

-- Otherwise the first difference decides.
example : KBLT [0, 5] [1] := kbLT_cons_cons_iff.2 (Or.inl zero_lt_one)

example : ¬ KBLT [1] [0, 5] := by
  simp [kbLT_cons_cons_iff]

end TauCeti.WellFoundedTreeExamples

end
