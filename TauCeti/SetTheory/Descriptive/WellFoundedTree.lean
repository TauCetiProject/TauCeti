/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.SetTheory.Descriptive.Tree

/-!
# Bodies of descriptive trees, strict extension and the tree representation of analytic sets

For a descriptive tree `T : Descriptive.tree A`, the **body** `Descriptive.Tree.body T` is the set
of infinite branches `x : ℕ → A`, the sequences all of whose initial segments
`Descriptive.Tree.initialSegment x n` lie in `T`. The names and statements of `initialSegment`,
`IsBranch` and `body` follow Mathlib PR #41946.

A tree is well-founded (`Descriptive.Tree.IsWellFounded`, defined through immediate extension in
`TauCeti.SetTheory.Descriptive.Tree`) exactly when its body is empty, and exactly when **strict
extension** `Descriptive.Tree.StrictExt T` is well-founded on its nodes; no finiteness of the
branching is needed. The rank `Descriptive.Tree.rank T` of a well-founded tree is also the strict
supremum of the strict-extension ranks of its nodes, and it is monotone along homomorphisms of
strict extension.

For a discrete alphabet the body of a tree is closed in `ℕ → A`, and the body of the tree of
initial segments of the points of a set `C` is the closure of `C`, so every closed subset of
`ℕ → A` is a body. Consequently every analytic subset of Cantor space `ℕ → Bool` is the projection
of the body of a tree on `Bool × ℕ`.

## Main definitions

* `Descriptive.Tree.initialSegment x n`: the list of the first `n` values of `x : ℕ → A`.
* `Descriptive.Tree.IsBranch T x` and `Descriptive.Tree.body T`: infinite branches and the body.
* `Descriptive.Tree.initialSegmentTree C`: the tree of initial segments of the points of `C`.
* `Descriptive.Tree.StrictExt T`: proper extension on the nodes of `T`.

## Main results

* `Descriptive.Tree.isWellFounded_iff_body_eq_empty` and
  `Descriptive.Tree.wellFounded_strictExt_iff`: a tree is well-founded iff its body is empty iff
  strict extension is well-founded on its nodes.
* `Descriptive.Tree.IsWellFounded.rank_eq_iSup_strictExt`: the rank of a well-founded tree is the
  strict supremum of the strict-extension ranks of its nodes.
* `Descriptive.Tree.IsWellFounded.rank_le_of_relHom`: rank is monotone along homomorphisms of
  strict extension.
* `Descriptive.Tree.isClosed_body` and `Descriptive.Tree.body_initialSegmentTree`: bodies are
  closed, and the body of the tree of initial segments of a set is its closure.
* `MeasureTheory.exists_tree_of_analyticSet_cantor`: the tree representation of analytic subsets
  of Cantor space.

## References

* Alexander S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Sections 2.A, 2.B, 2.E and 25.A.
* David Marker, *Lectures on infinitary model theory*, Chapter 9.
-/

public section

universe u

open Filter Function Set Topology

namespace Descriptive.Tree

variable {A : Type u} {S T : tree A}

/-! ### Initial segments, branches and bodies -/

/-- The list of the first `n` values of an infinite sequence. -/
@[expose] def initialSegment (x : ℕ → A) (n : ℕ) : List A :=
  List.ofFn fun i : Fin n ↦ x i

/-- Unfolding lemma for `Descriptive.Tree.initialSegment`. -/
theorem initialSegment_def (x : ℕ → A) (n : ℕ) :
    initialSegment x n = List.ofFn fun i : Fin n ↦ x i :=
  rfl

@[simp] lemma initialSegment_zero (x : ℕ → A) : initialSegment x 0 = [] := by
  rfl

@[simp] lemma length_initialSegment (x : ℕ → A) (n : ℕ) : (initialSegment x n).length = n := by
  simp [initialSegment]

/-- Passing from length `n` to length `n + 1` appends the next coordinate. -/
lemma initialSegment_succ (x : ℕ → A) (n : ℕ) :
    initialSegment x (n + 1) = initialSegment x n ++ [x n] := by
  simpa [initialSegment] using List.ofFn_succ' (fun i : Fin (n + 1) ↦ x i)

/-- Shorter initial segments are prefixes of longer ones. -/
theorem initialSegment_prefix_initialSegment (x : ℕ → A) {m n : ℕ} (h : m ≤ n) :
    initialSegment x m <+: initialSegment x n := by
  induction n, h using Nat.le_induction with
  | base => exact List.prefix_refl _
  | succ n _ ih => exact ih.trans (initialSegment_succ x n ▸ List.prefix_append _ _)

/-- Two sequences have the same initial segment of length `n` iff they agree below `n`. -/
theorem initialSegment_eq_initialSegment_iff {x y : ℕ → A} {n : ℕ} :
    initialSegment x n = initialSegment y n ↔ ∀ i < n, x i = y i := by
  simp only [initialSegment, List.ofFn_inj, funext_iff, Fin.forall_iff]

/-- An infinite sequence is a branch when every finite initial segment belongs to the tree. -/
@[expose] def IsBranch (T : tree A) (x : ℕ → A) : Prop :=
  ∀ n, initialSegment x n ∈ T

/-- Unfolding lemma for `Descriptive.Tree.IsBranch`. -/
theorem isBranch_iff {x : ℕ → A} : IsBranch T x ↔ ∀ n, initialSegment x n ∈ T :=
  Iff.rfl

/-- The body of a tree is the set of all its infinite branches. -/
@[expose] def body (T : tree A) : Set (ℕ → A) :=
  {x | IsBranch T x}

@[simp] lemma mem_body {x : ℕ → A} : x ∈ body T ↔ ∀ n, initialSegment x n ∈ T :=
  Iff.rfl

/-- A branch forces the root to belong to the tree. -/
lemma nil_mem_of_isBranch {x : ℕ → A} (hx : IsBranch T x) : [] ∈ T := by
  simpa using hx 0

/-- Inclusion of trees induces inclusion of their bodies. -/
@[gcongr] lemma body_mono (h : S ≤ T) : body S ⊆ body T := by
  intro x hx n
  exact h (hx n)

/-- The empty tree has empty body. -/
@[simp]
theorem body_bot : body (⊥ : tree A) = ∅ :=
  eq_empty_of_forall_notMem fun _ hx => nil_mem_of_isBranch hx

/-- A tree is well-founded exactly when it has no infinite branch. -/
theorem isWellFounded_iff_body_eq_empty : IsWellFounded T ↔ body T = ∅ := by
  rw [isWellFounded_iff_forall_exists_notMem, eq_empty_iff_forall_notMem]
  simp only [mem_body, not_forall]
  rfl

/-- The body of a tree is the intersection of the sets of sequences with a given initial segment
in the tree. -/
theorem body_eq_iInter (T : tree A) : body T = ⋂ n, {x | initialSegment x n ∈ T} := by
  ext x
  simp

/-- Over a discrete alphabet the body of a tree is closed. -/
theorem isClosed_body [TopologicalSpace A] [DiscreteTopology A] (T : tree A) :
    IsClosed (body T) := by
  rw [body_eq_iInter]
  refine isClosed_iInter fun n => ?_
  have hc : Continuous fun (x : ℕ → A) (i : Fin n) => x i :=
    continuous_pi fun i => continuous_apply (i : ℕ)
  exact (isClosed_discrete {v : Fin n → A | List.ofFn v ∈ T}).preimage hc

/-! ### The tree of initial segments of a set -/

/-- The tree of initial segments of the points of a set `C` of sequences. -/
def initialSegmentTree (C : Set (ℕ → A)) : tree A :=
  ⟨{l | ∃ x ∈ C, initialSegment x l.length = l}, by
    rintro l a ⟨x, hx, hxl⟩
    refine ⟨x, hx, ?_⟩
    rw [List.length_append, List.length_singleton, initialSegment_succ] at hxl
    exact List.append_inj_left' hxl rfl⟩

/-- Membership in `Descriptive.Tree.initialSegmentTree`. -/
@[simp]
theorem mem_initialSegmentTree {C : Set (ℕ → A)} {l : List A} :
    l ∈ initialSegmentTree C ↔ ∃ x ∈ C, initialSegment x l.length = l :=
  Iff.rfl

/-- Every point of `C` is a branch of the tree of initial segments of `C`. -/
theorem subset_body_initialSegmentTree (C : Set (ℕ → A)) : C ⊆ body (initialSegmentTree C) :=
  fun x hx n => ⟨x, hx, by rw [length_initialSegment]⟩

/-- Over a discrete alphabet, the body of the tree of initial segments of a set is its closure. -/
theorem body_initialSegmentTree [TopologicalSpace A] [DiscreteTopology A] (C : Set (ℕ → A)) :
    body (initialSegmentTree C) = closure C := by
  refine Subset.antisymm (fun x hx => ?_)
    (closure_minimal (subset_body_initialSegmentTree C) (isClosed_body _))
  choose y hyC hy using fun n => mem_initialSegmentTree.1 (hx n)
  refine mem_closure_of_tendsto (tendsto_pi_nhds.2 fun i => ?_)
    (Eventually.of_forall (f := atTop) hyC)
  refine tendsto_atTop_of_eventually_const (i₀ := i + 1) fun n hn => ?_
  have h := hy n
  rw [length_initialSegment, initialSegment_eq_initialSegment_iff] at h
  exact h i (by omega)

/-- Over a discrete alphabet, every closed set of sequences is the body of the tree of initial
segments of its points. -/
theorem _root_.IsClosed.body_initialSegmentTree [TopologicalSpace A] [DiscreteTopology A]
    {C : Set (ℕ → A)} (hC : IsClosed C) : body (initialSegmentTree C) = C := by
  rw [Descriptive.Tree.body_initialSegmentTree, hC.closure_eq]

/-! ### Strict extension -/

/-- Strict extension on the nodes of a tree: `StrictExt T y x` holds when `y` properly extends
`x`. -/
@[expose] def StrictExt (T : tree A) (y x : T) : Prop :=
  (x : List A) <+: y ∧ (x : List A) ≠ y

/-- Unfolding lemma for `Descriptive.Tree.StrictExt`. -/
theorem strictExt_iff {y x : T} : StrictExt T y x ↔ (x : List A) <+: y ∧ (x : List A) ≠ y :=
  Iff.rfl

/-- An immediate extension is a strict extension. -/
theorem ChildRel.strictExt {y x : T} (h : ChildRel T y x) : StrictExt T y x := by
  obtain ⟨a, ha⟩ := childRel_iff.1 h
  exact ⟨ha ▸ List.prefix_append _ _, fun h' => by simp [← h'] at ha⟩

/-- Node ranks do not increase along extensions. -/
private theorem nodeRank_append_le (hT : IsWellFounded T) (u : T) (l : List A)
    (hl : u.1 ++ l ∈ T) : (hT.apply ⟨u.1 ++ l, hl⟩).rank ≤ (hT.apply u).rank := by
  induction l generalizing u with
  | nil =>
    have heq : (⟨u.1 ++ [], hl⟩ : T) = u := Subtype.ext (by simp)
    rw [heq]
  | cons a l ih =>
    have hl' : (u.1 ++ [a]) ++ l ∈ T := by simpa using hl
    have heq : (⟨u.1 ++ a :: l, hl⟩ : T) = ⟨(u.1 ++ [a]) ++ l, hl'⟩ := Subtype.ext (by simp)
    rw [heq]
    exact (ih ⟨u.1 ++ [a], mem_of_append hl'⟩ hl').trans
      ((hT.apply u).rank_lt_of_rel (a := ⟨u.1 ++ [a], mem_of_append hl'⟩)
        (childRel_iff.2 ⟨a, rfl⟩)).le

/-- In a well-founded tree, node ranks strictly decrease along strict extension. -/
theorem IsWellFounded.rank_lt_of_strictExt (hT : IsWellFounded T) {y x : T}
    (h : StrictExt T y x) : (hT.apply y).rank < (hT.apply x).rank := by
  obtain ⟨⟨l, hl⟩, hne⟩ := h
  obtain _ | ⟨a, l⟩ := l
  · exact absurd (by simp [← hl]) hne
  have hy : (x.1 ++ [a]) ++ l ∈ T := by simp [hl]
  have heq : y = ⟨(x.1 ++ [a]) ++ l, hy⟩ := Subtype.ext (by simp [← hl])
  rw [heq]
  exact (nodeRank_append_le hT ⟨x.1 ++ [a], mem_of_append hy⟩ l hy).trans_lt
    ((hT.apply x).rank_lt_of_rel (a := ⟨x.1 ++ [a], mem_of_append hy⟩)
      (childRel_iff.2 ⟨a, rfl⟩))

/-- Strict extension is well-founded on the nodes of a well-founded tree. -/
theorem IsWellFounded.wellFounded_strictExt (hT : IsWellFounded T) :
    WellFounded (StrictExt T) :=
  Subrelation.wf (fun h => hT.rank_lt_of_strictExt h)
    (InvImage.wf (fun u : T => (hT.apply u).rank) wellFounded_lt)

/-- **Strict extension and bodies.** A tree has no infinite branch exactly when strict extension
is well-founded on its nodes. No finiteness of the branching is needed. -/
theorem wellFounded_strictExt_iff (T : tree A) : WellFounded (StrictExt T) ↔ body T = ∅ := by
  refine ⟨fun hwf => eq_empty_of_forall_notMem fun x hx => ?_, fun h =>
    (isWellFounded_iff_body_eq_empty.2 h).wellFounded_strictExt⟩
  let c : ℕ → T := fun n => ⟨initialSegment x n, hx n⟩
  have hstep (n : ℕ) : StrictExt T (c (n + 1)) (c n) :=
    ⟨initialSegment_prefix_initialSegment x n.le_succ, fun h => by
      simpa [c] using congrArg List.length h⟩
  exact (wellFounded_iff_isEmpty_descending_chain.mp hwf).false ⟨c, hstep⟩

/-- In a well-founded tree, the strict-extension rank of a node is its immediate-extension rank.
-/
theorem IsWellFounded.rank_strictExt_eq (hT : IsWellFounded T) (u : T) :
    (hT.wellFounded_strictExt.apply u).rank = (hT.apply u).rank := by
  induction u using hT.wellFounded_strictExt.induction with
  | h u ih =>
    refine le_antisymm ?_ ?_
    · rw [(hT.wellFounded_strictExt.apply u).rank_eq]
      refine Ordinal.iSup_le fun v => ?_
      rw [ih v.1 v.2]
      exact Order.succ_le_of_lt (hT.rank_lt_of_strictExt v.2)
    · rw [(hT.apply u).rank_eq]
      refine Ordinal.iSup_le fun v => ?_
      have hv : StrictExt T v.1 u := v.2.strictExt
      have h := (hT.wellFounded_strictExt.apply u).rank_lt_of_rel hv
      rw [ih v.1 hv] at h
      exact Order.succ_le_of_lt h

/-- The rank of a well-founded tree is the strict supremum of the strict-extension ranks of its
nodes. -/
theorem IsWellFounded.rank_eq_iSup_strictExt (hT : IsWellFounded T) :
    rank T = ⨆ u : T, Order.succ (hT.wellFounded_strictExt.apply u).rank := by
  simp only [hT.rank_strictExt_eq, hT.rank_eq_iSup]

/-- A tree with a homomorphism of strict extension into a well-founded tree is well-founded. -/
theorem IsWellFounded.of_relHom (hT : IsWellFounded T) (f : StrictExt S →r StrictExt T) :
    IsWellFounded S :=
  isWellFounded_iff_body_eq_empty.2 <|
    (wellFounded_strictExt_iff S).1 (RelHomClass.wellFounded f hT.wellFounded_strictExt)

/-- **Monotonicity of rank.** A homomorphism of strict extension into a well-founded tree, injective
or not, does not increase the rank. -/
theorem IsWellFounded.rank_le_of_relHom (hT : IsWellFounded T) (f : StrictExt S →r StrictExt T) :
    rank S ≤ rank T := by
  have hS := hT.of_relHom f
  have hnode (u : S) : (hS.wellFounded_strictExt.apply u).rank ≤
      (hT.wellFounded_strictExt.apply (f u)).rank := by
    induction u using hS.wellFounded_strictExt.induction with
    | h u ih =>
      rw [(hS.wellFounded_strictExt.apply u).rank_eq]
      exact Ordinal.iSup_le fun v => Order.succ_le_of_lt <| (ih v.1 v.2).trans_lt
        ((hT.wellFounded_strictExt.apply (f u)).rank_lt_of_rel (f.map_rel v.2))
  rw [hS.rank_eq_iSup_strictExt, hT.rank_eq_iSup_strictExt]
  exact Ordinal.iSup_le fun u => (Order.succ_le_succ (hnode u)).trans (Ordinal.le_iSup
    (fun w : T => Order.succ (hT.wellFounded_strictExt.apply w).rank) (f u))

end Descriptive.Tree

namespace MeasureTheory

open Descriptive Descriptive.Tree

/-- **Tree representation of analytic sets in Cantor space.** Every analytic set `A ⊆ ℕ → Bool` is
the projection of the body of a tree on `Bool × ℕ`: `x ∈ A` iff some `y : ℕ → ℕ` makes the paired
sequence `n ↦ (x n, y n)` a branch. -/
theorem exists_tree_of_analyticSet_cantor {A : Set (ℕ → Bool)} (hA : AnalyticSet A) :
    ∃ T : tree (Bool × ℕ), A = {x | ∃ y : ℕ → ℕ, (fun n => (x n, y n)) ∈ body T} := by
  obtain ⟨β, _, _, f₀, hf₀, rfl⟩ := analyticSet_iff_exists_polishSpace_range.1 hA
  rcases isEmpty_or_nonempty β with hβ | hβ
  · exact ⟨⊥, by simpa using hβ⟩
  obtain ⟨g, hg, hgs⟩ := PolishSpace.exists_nat_nat_continuous_surjective β
  have hrange : range f₀ = range (f₀ ∘ g) := (hgs.range_comp f₀).symm
  rw [hrange]
  have hf : Continuous (f₀ ∘ g) := hf₀.comp hg
  set f := f₀ ∘ g
  let G : Set (ℕ → Bool × ℕ) := {z | f (fun n => (z n).2) = fun n => (z n).1}
  have hG : IsClosed G := isClosed_eq
    (hf.comp (continuous_pi fun n => continuous_snd.comp (continuous_apply n)))
    (continuous_pi fun n => continuous_fst.comp (continuous_apply n))
  refine ⟨initialSegmentTree G, ?_⟩
  rw [hG.body_initialSegmentTree]
  ext x
  simp [G, eq_comm]

end MeasureTheory
