/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.Order.Fin.Basic
import Mathlib.Order.Lattice.Nat
import TauCeti.Data.Fin.Tuple.Sort

/-!
# Comparison trees

A comparison tree on `n` items with outputs in `α` is a binary tree whose inner nodes each compare
two items and whose leaves carry outputs. It is the model in which lower bounds for sorting and
selection by pairwise comparisons are proved: such a bound says that every tree solving a problem
has a long branch.

A node `CompTree.node i j l r` asks whether item `i` is smaller than item `j`; the inputs for which
it is follow `l`, all others, ties included, follow `r`. A tree is evaluated on any
`x : Fin n → β` with `β` a linear order, `x i` being the value of item `i`. Its output
`CompTree.eval` is the label of the leaf reached, its cost `CompTree.cost` is the number of nodes
passed on the way, and its depth `CompTree.depth` is the largest number of nodes on any branch,
whether or not some input follows that branch.

Only the relative order of the values matters: composing the input with a strictly monotone map
changes neither output nor cost. Hence on an input with pairwise different values a tree behaves as
on the ranking `(Tuple.sort x).symm` of that input, which gives item `i` the number of items with a
smaller value as its rank (`Tuple.val_sort_symm_apply`). Composing with a strictly antitone map, in
particular reversing a ranking, amounts to swapping the two items at every node
(`CompTree.reverse`).

## Main definitions

* `TauCeti.CompTree n α`: comparison trees on `n` items with outputs in `α`.
* `TauCeti.CompTree.eval`, `TauCeti.CompTree.cost`: the output and the number of comparisons made
  on an input.
* `TauCeti.CompTree.depth`: the largest number of comparisons on any branch.
* `TauCeti.CompTree.reverse`: the tree in which every comparison `(i, j)` becomes `(j, i)`.

## Main results

* `TauCeti.CompTree.cost_le_depth`: the cost on every input is at most the depth.
* `TauCeti.CompTree.eval_comp_of_strictMono`, `TauCeti.CompTree.cost_comp_of_strictMono`: output
  and cost are invariant under strictly monotone maps of the values.
* `TauCeti.CompTree.eval_sort_symm`, `TauCeti.CompTree.cost_sort_symm`: on an injective input,
  output and cost are those on its ranking.
* `TauCeti.CompTree.exists_prune`: for a nonempty set `A` of inputs, some tree has the same output
  and the same cost as `t` on every input in `A`, and its depth is the largest cost of `t` on `A`.
* `TauCeti.CompTree.eval_reverse`, `TauCeti.CompTree.cost_reverse`: the reversed tree on a ranking
  `σ` behaves as the original tree on the reversed ranking `i ↦ n - 1 - σ i`.

## References

* Jeff Erickson, *Algorithms*, lecture notes, Lecture 12, "Lower Bounds", §12.2 and §12.5
  (revision of Fall 2013): the comparison tree model.
-/

public section

namespace TauCeti

universe u

/-- A comparison tree on `n` items with outputs in `α`. A leaf `leaf a` outputs `a`. A node
`node i j l r` compares item `i` with item `j`: inputs in which item `i` is smaller than item `j`
continue in `l`, all other inputs continue in `r`. -/
inductive CompTree (n : ℕ) (α : Type u) : Type u
  /-- The leaf with output `a`. -/
  | leaf (a : α)
  /-- The node comparing item `i` with item `j`, continuing in `l` when item `i` is smaller and in
  `r` otherwise. -/
  | node (i j : Fin n) (l r : CompTree n α)

namespace CompTree

variable {n : ℕ} {α : Type u} {β γ : Type*} [LinearOrder β] [LinearOrder γ]

/-- The output of a comparison tree on the input `x : Fin n → β`, where `x i` is the value of
item `i`: the label of the leaf reached by following, at every node `node i j l r`, the subtree
`l` when `x i < x j` and the subtree `r` otherwise. -/
def eval : CompTree n α → (Fin n → β) → α
  | leaf a, _ => a
  | node i j l r, x => if x i < x j then l.eval x else r.eval x

/-- The cost of a comparison tree on the input `x : Fin n → β`: the number of nodes on the branch
that `x` follows, that is, the number of comparisons made on `x`. -/
def cost : CompTree n α → (Fin n → β) → ℕ
  | leaf _, _ => 0
  | node i j l r, x => (if x i < x j then l.cost x else r.cost x) + 1

/-- The depth of a comparison tree: the largest number of nodes on a branch, including branches
that no input follows. -/
def depth : CompTree n α → ℕ
  | leaf _ => 0
  | node _ _ l r => max l.depth r.depth + 1

/-- The reversal of a comparison tree: every comparison `(i, j)` is replaced by `(j, i)`, keeping
the two subtrees in place. -/
def reverse : CompTree n α → CompTree n α
  | leaf a => leaf a
  | node i j l r => node j i l.reverse r.reverse

@[simp]
theorem eval_leaf (a : α) (x : Fin n → β) : (leaf a : CompTree n α).eval x = a := by
  rw [eval]

@[simp]
theorem eval_node (i j : Fin n) (l r : CompTree n α) (x : Fin n → β) :
    (node i j l r).eval x = if x i < x j then l.eval x else r.eval x := by
  rw [eval]

@[simp]
theorem cost_leaf (a : α) (x : Fin n → β) : (leaf a : CompTree n α).cost x = 0 := by
  rw [cost]

@[simp]
theorem cost_node (i j : Fin n) (l r : CompTree n α) (x : Fin n → β) :
    (node i j l r).cost x = (if x i < x j then l.cost x else r.cost x) + 1 := by
  rw [cost]

@[simp]
theorem depth_leaf (a : α) : (leaf a : CompTree n α).depth = 0 := by
  rw [depth]

@[simp]
theorem depth_node (i j : Fin n) (l r : CompTree n α) :
    (node i j l r).depth = max l.depth r.depth + 1 := by
  rw [depth]

@[simp]
theorem reverse_leaf (a : α) : (leaf a : CompTree n α).reverse = leaf a := by
  rw [reverse]

@[simp]
theorem reverse_node (i j : Fin n) (l r : CompTree n α) :
    (node i j l r).reverse = node j i l.reverse r.reverse := by
  rw [reverse]

/-- The number of comparisons made on any input is at most the depth. -/
theorem cost_le_depth (t : CompTree n α) (x : Fin n → β) : t.cost x ≤ t.depth := by
  induction t with
  | leaf a => simp
  | node i j l r ihl ihr =>
    simp only [cost_node, depth_node]
    split_ifs <;> omega

/-! ### Invariance under order-preserving and order-reversing maps -/

/-- Composing the input with a strictly monotone map does not change the output. -/
theorem eval_comp_of_strictMono {f : β → γ} (hf : StrictMono f) (t : CompTree n α)
    (x : Fin n → β) : t.eval (f ∘ x) = t.eval x := by
  induction t with
  | leaf a => simp
  | node i j l r ihl ihr => simp [hf.lt_iff_lt, ihl, ihr]

/-- Composing the input with a strictly monotone map does not change the cost. -/
theorem cost_comp_of_strictMono {f : β → γ} (hf : StrictMono f) (t : CompTree n α)
    (x : Fin n → β) : t.cost (f ∘ x) = t.cost x := by
  induction t with
  | leaf a => simp
  | node i j l r ihl ihr => simp [hf.lt_iff_lt, ihl, ihr]

/-- On an input with pairwise different values, the output is the output on the ranking of the
input, which gives item `i` the number of items with a smaller value as its rank
(`Tuple.val_sort_symm_apply`). -/
theorem eval_sort_symm {x : Fin n → β} (hx : Function.Injective x) (t : CompTree n α) :
    t.eval ⇑(Tuple.sort x).symm = t.eval x := by
  have h : (x ∘ Tuple.sort x) ∘ ⇑(Tuple.sort x).symm = x := by
    ext i
    simp
  rw [← t.eval_comp_of_strictMono (Tuple.strictMono_comp_sort hx), h]

/-- On an input with pairwise different values, the cost is the cost on the ranking of the input,
which gives item `i` the number of items with a smaller value as its rank
(`Tuple.val_sort_symm_apply`). -/
theorem cost_sort_symm {x : Fin n → β} (hx : Function.Injective x) (t : CompTree n α) :
    t.cost ⇑(Tuple.sort x).symm = t.cost x := by
  have h : (x ∘ Tuple.sort x) ∘ ⇑(Tuple.sort x).symm = x := by
    ext i
    simp
  rw [← t.cost_comp_of_strictMono (Tuple.strictMono_comp_sort hx), h]

/-- Reversing a tree twice gives it back. -/
@[simp]
theorem reverse_reverse (t : CompTree n α) : t.reverse.reverse = t := by
  induction t with
  | leaf a => simp
  | node i j l r ihl ihr => simp [ihl, ihr]

/-- Reversal of comparison trees is an involution. -/
theorem reverse_involutive : Function.Involutive (reverse : CompTree n α → CompTree n α) :=
  reverse_reverse

/-- Reversal does not change the depth. -/
@[simp]
theorem depth_reverse (t : CompTree n α) : t.reverse.depth = t.depth := by
  induction t with
  | leaf a => simp
  | node i j l r ihl ihr => simp [ihl, ihr]

/-- Composing the input with a strictly antitone map gives the output of the reversed tree. -/
theorem eval_comp_of_strictAnti {f : β → γ} (hf : StrictAnti f) (t : CompTree n α)
    (x : Fin n → β) : t.eval (f ∘ x) = t.reverse.eval x := by
  induction t with
  | leaf a => simp
  | node i j l r ihl ihr => simp [hf.lt_iff_gt, ihl, ihr]

/-- Composing the input with a strictly antitone map gives the cost of the reversed tree. -/
theorem cost_comp_of_strictAnti {f : β → γ} (hf : StrictAnti f) (t : CompTree n α)
    (x : Fin n → β) : t.cost (f ∘ x) = t.reverse.cost x := by
  induction t with
  | leaf a => simp
  | node i j l r ihl ihr => simp [hf.lt_iff_gt, ihl, ihr]

/-- The output of the reversed tree on a ranking `σ` is the output of the tree on the reversed
ranking `i ↦ n - 1 - σ i`. -/
theorem eval_reverse (t : CompTree n α) (σ : Equiv.Perm (Fin n)) :
    t.reverse.eval ⇑σ = t.eval ⇑(σ.trans Fin.revPerm) := by
  have hrev : ⇑(σ.trans Fin.revPerm) = Fin.rev ∘ ⇑σ := by
    ext i
    simp
  rw [hrev, t.eval_comp_of_strictAnti Fin.rev_strictAnti]

/-- The cost of the reversed tree on a ranking `σ` is the cost of the tree on the reversed ranking
`i ↦ n - 1 - σ i`. -/
theorem cost_reverse (t : CompTree n α) (σ : Equiv.Perm (Fin n)) :
    t.reverse.cost ⇑σ = t.cost ⇑(σ.trans Fin.revPerm) := by
  have hrev : ⇑(σ.trans Fin.revPerm) = Fin.rev ∘ ⇑σ := by
    ext i
    simp
  rw [hrev, t.cost_comp_of_strictAnti Fin.rev_strictAnti]

/-! ### Pruning -/

/-- For every set `A` of inputs there is a tree with the same output and cost as `t` on `A` whose
depth is at most every bound on the costs of `t` on `A`; the output `a` labels the leaf used when
`A` is empty. -/
private theorem exists_eqOn_depth_le (a : α) (t : CompTree n α) (A : Set (Fin n → β)) :
    ∃ t' : CompTree n α, (∀ x ∈ A, t'.eval x = t.eval x ∧ t'.cost x = t.cost x) ∧
      ∀ k, (∀ x ∈ A, t.cost x ≤ k) → t'.depth ≤ k := by
  induction t generalizing A with
  | leaf b => exact ⟨leaf b, fun _ _ => ⟨rfl, rfl⟩, fun k _ => by simp⟩
  | node i j l r ihl ihr =>
    obtain ⟨l', hl, hl'⟩ := ihl {x ∈ A | x i < x j}
    obtain ⟨r', hr, hr'⟩ := ihr {x ∈ A | ¬x i < x j}
    rcases A.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
    · exact ⟨leaf a, by simp, fun k _ => by simp⟩
    refine ⟨node i j l' r', fun x hx => ?_, fun k hk => ?_⟩
    · by_cases h : x i < x j
      · simp [h, hl x ⟨hx, h⟩]
      · simp [h, hr x ⟨hx, h⟩]
    · -- Every branch below the node is one comparison shorter than the bound `k ≥ 1`.
      have h₀ := hk x₀ hx₀
      rw [cost_node] at h₀
      have hl'' := hl' (k - 1) fun x hx => by
        have := hk x hx.1
        simp only [cost_node, hx.2, ite_true] at this
        omega
      have hr'' := hr' (k - 1) fun x hx => by
        have := hk x hx.1
        simp only [cost_node, hx.2, ite_false] at this
        omega
      rw [depth_node]
      omega

/-- Pruning: for a nonempty set `A` of inputs there is a tree with the same output and the same
cost as `t` on every input in `A` whose depth is the largest cost of `t` on an input in `A`. -/
theorem exists_prune (t : CompTree n α) {A : Set (Fin n → β)} (hA : A.Nonempty) :
    ∃ t' : CompTree n α, (∀ x ∈ A, t'.eval x = t.eval x ∧ t'.cost x = t.cost x) ∧
      ∃ x ∈ A, (∀ y ∈ A, t.cost y ≤ t.cost x) ∧ t'.depth = t.cost x := by
  have hbdd : BddAbove ((fun x => t.cost x) '' A) :=
    ⟨t.depth, by rintro _ ⟨x, -, rfl⟩; exact t.cost_le_depth x⟩
  obtain ⟨x, hx, hxs⟩ := Nat.sSup_mem (hA.image _) hbdd
  have hmax : ∀ y ∈ A, t.cost y ≤ t.cost x := fun y hy =>
    (le_csSup hbdd ⟨y, hy, rfl⟩).trans_eq hxs.symm
  obtain ⟨t', ht', hdepth⟩ := exists_eqOn_depth_le (t.eval x) t A
  refine ⟨t', ht', x, hx, hmax, le_antisymm (hdepth _ hmax) ?_⟩
  exact (ht' x hx).2 ▸ t'.cost_le_depth x

end CompTree

end TauCeti
