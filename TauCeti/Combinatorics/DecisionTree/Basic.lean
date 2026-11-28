/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Order.Lattice.Nat

/-!
# Decision trees and decision-tree complexity

A decision tree on `n` Boolean variables is a binary tree whose inner nodes each query one
variable and whose leaves carry an output in `Bool`. It computes a Boolean function
`f : (Fin n → Bool) → Bool` when the leaf that each input reaches carries the value of `f` at that
input. The decision-tree complexity `D(f)` is the least depth of a tree that computes `f`, that
is, the number of queries that suffice to find the value of `f` at the worst input.

Every Boolean function is computed by the tree that queries all variables in order and carries
the values of `f` at its leaves, so `D(f) ≤ n`. A tree of depth `0` is a leaf, so `D(f) = 0`
exactly when `f` is constant. A variable may be queried twice on a path.

## Main definitions

* `TauCeti.DecisionTree n`: decision trees on `n` Boolean variables.
* `TauCeti.DecisionTree.eval`: the output of a tree on an input.
* `TauCeti.DecisionTree.depth`: the largest number of queries on a path from the root to a leaf.
* `TauCeti.decisionTreeDepth f`: the least depth `D(f)` of a tree that computes `f`.

## Main results

* `TauCeti.DecisionTree.exists_eval_eq_and_depth_eq`: every Boolean function on `n` variables is
  computed by a tree of depth `n`.
* `TauCeti.decisionTreeDepth_le_iff`: `D(f) ≤ d` exactly when a tree of depth at most `d`
  computes `f`.
* `TauCeti.DecisionTree.exists_eval_eq_and_depth_eq_decisionTreeDepth`: some tree of depth
  `D(f)` computes `f`.
* `TauCeti.decisionTreeDepth_le`: `D(f) ≤ n`.
* `TauCeti.decisionTreeDepth_eq_zero_iff`: `D(f) = 0` exactly when `f` is constant.

## References

* Harry Buhrman and Ronald de Wolf, *Complexity measures and decision tree complexity: a
  survey*, Theoretical Computer Science 288 (2002), 21–43, §3.1.
-/

public section

namespace TauCeti

/-- A decision tree on `n` Boolean variables. A leaf `leaf b` outputs `b`. A node `node i t₀ t₁`
queries the variable `i` and continues in `t₀` when it is `false` and in `t₁` when it is
`true`. -/
inductive DecisionTree (n : ℕ) : Type
  /-- The leaf with output `b`. -/
  | leaf (b : Bool)
  /-- The node that queries the variable `i`, continuing in `t₀` when it is `false` and in `t₁`
  when it is `true`. -/
  | node (i : Fin n) (t₀ t₁ : DecisionTree n)

namespace DecisionTree

variable {n : ℕ}

/-- The output of a decision tree on the input `x : Fin n → Bool`: the label of the leaf reached
by following, at every node `node i t₀ t₁`, the subtree `t₁` when `x i` is `true` and the subtree
`t₀` otherwise. -/
def eval : DecisionTree n → (Fin n → Bool) → Bool
  | leaf b, _ => b
  | node i t₀ t₁, x => if x i then t₁.eval x else t₀.eval x

/-- The depth of a decision tree: the largest number of nodes on a path from the root to a
leaf, including paths that no input follows. -/
def depth : DecisionTree n → ℕ
  | leaf _ => 0
  | node _ t₀ t₁ => max t₀.depth t₁.depth + 1

/-- The output of a leaf is its label. -/
@[simp]
theorem eval_leaf (b : Bool) (x : Fin n → Bool) : (leaf b : DecisionTree n).eval x = b := by
  rw [eval]

/-- A node follows its second subtree when the queried variable is `true` and its first
subtree otherwise. -/
@[simp]
theorem eval_node (i : Fin n) (t₀ t₁ : DecisionTree n) (x : Fin n → Bool) :
    (node i t₀ t₁).eval x = if x i then t₁.eval x else t₀.eval x := by
  rw [eval]

/-- A leaf has depth `0`. -/
@[simp]
theorem depth_leaf (b : Bool) : (leaf b : DecisionTree n).depth = 0 := by
  rw [depth]

/-- The depth of a node is one more than the larger depth of its two subtrees. -/
@[simp]
theorem depth_node (i : Fin n) (t₀ t₁ : DecisionTree n) :
    (node i t₀ t₁).depth = max t₀.depth t₁.depth + 1 := by
  rw [depth]

/-- A decision tree has depth `0` exactly when it is a leaf. -/
theorem depth_eq_zero_iff {T : DecisionTree n} : T.depth = 0 ↔ ∃ b, T = leaf b := by
  cases T <;> simp

/-- The tree that queries the variables of `l` in order, starting from the partial input `x₀`,
and puts at each leaf the value of `f` at `x₀` updated by the answers on the path. -/
private def queryList (f : (Fin n → Bool) → Bool) :
    List (Fin n) → (Fin n → Bool) → DecisionTree n
  | [], x₀ => leaf (f x₀)
  | i :: l, x₀ =>
    node i (queryList f l (Function.update x₀ i false)) (queryList f l (Function.update x₀ i true))

private theorem eval_queryList (f : (Fin n → Bool) → Bool) (l : List (Fin n))
    (x₀ x : Fin n → Bool) :
    (queryList f l x₀).eval x = f fun j => if j ∈ l then x j else x₀ j := by
  induction l generalizing x₀ with
  | nil => simp [queryList]
  | cons i l ih =>
    have key : (fun j => if j ∈ l then x j else Function.update x₀ i (x i) j) =
        fun j => if j ∈ i :: l then x j else x₀ j := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp
      · simp [hj]
    rw [← key]
    cases hx : x i <;> simp [queryList, ih, hx]

private theorem depth_queryList (f : (Fin n → Bool) → Bool) (l : List (Fin n))
    (x₀ : Fin n → Bool) : (queryList f l x₀).depth = l.length := by
  induction l generalizing x₀ with
  | nil => simp [queryList]
  | cons i l ih => simp [queryList, ih]

/-- Every Boolean function on `n` variables is computed by a decision tree of depth `n`: the tree
that queries all variables in order. -/
theorem exists_eval_eq_and_depth_eq (f : (Fin n → Bool) → Bool) :
    ∃ T : DecisionTree n, T.eval = f ∧ T.depth = n := by
  refine ⟨queryList f (List.finRange n) fun _ => false, ?_, by simp [depth_queryList]⟩
  ext x
  simp [eval_queryList]

end DecisionTree

open DecisionTree

variable {n : ℕ}

/-- The decision-tree complexity `D(f)` of a Boolean function `f` on `n` variables: the least
depth of a decision tree that computes `f`. -/
noncomputable def decisionTreeDepth (f : (Fin n → Bool) → Bool) : ℕ :=
  sInf {d | ∃ T : DecisionTree n, T.eval = f ∧ T.depth ≤ d}

/-- `D(f) ≤ d` exactly when a decision tree of depth at most `d` computes `f`. -/
theorem decisionTreeDepth_le_iff {f : (Fin n → Bool) → Bool} {d : ℕ} :
    decisionTreeDepth f ≤ d ↔ ∃ T : DecisionTree n, T.eval = f ∧ T.depth ≤ d := by
  have hne : {d | ∃ T : DecisionTree n, T.eval = f ∧ T.depth ≤ d}.Nonempty :=
    let ⟨T, hT, hd⟩ := exists_eval_eq_and_depth_eq f
    ⟨n, T, hT, hd.le⟩
  refine ⟨fun h => ?_, fun h => Nat.sInf_le h⟩
  obtain ⟨T, hT, hd⟩ := Nat.sInf_mem hne
  exact ⟨T, hT, hd.trans h⟩

/-- The decision-tree complexity of the function that a tree computes is at most the depth of
the tree. -/
theorem DecisionTree.decisionTreeDepth_eval_le_depth (T : DecisionTree n) :
    decisionTreeDepth T.eval ≤ T.depth :=
  decisionTreeDepth_le_iff.2 ⟨T, rfl, le_rfl⟩

/-- Some decision tree of depth exactly `D(f)` computes `f`. -/
theorem DecisionTree.exists_eval_eq_and_depth_eq_decisionTreeDepth
    (f : (Fin n → Bool) → Bool) :
    ∃ T : DecisionTree n, T.eval = f ∧ T.depth = decisionTreeDepth f := by
  obtain ⟨T, rfl, hd⟩ := decisionTreeDepth_le_iff.1 (le_refl (decisionTreeDepth f))
  exact ⟨T, rfl, le_antisymm hd T.decisionTreeDepth_eval_le_depth⟩

/-- The decision-tree complexity of a Boolean function on `n` variables is at most `n`. -/
theorem decisionTreeDepth_le (f : (Fin n → Bool) → Bool) : decisionTreeDepth f ≤ n :=
  let ⟨T, hT, hd⟩ := exists_eval_eq_and_depth_eq f
  decisionTreeDepth_le_iff.2 ⟨T, hT, hd.le⟩

/-- The decision-tree complexity of a Boolean function is `0` exactly when the function is
constant. -/
theorem decisionTreeDepth_eq_zero_iff {f : (Fin n → Bool) → Bool} :
    decisionTreeDepth f = 0 ↔ ∃ b, f = fun _ => b := by
  rw [← Nat.le_zero, decisionTreeDepth_le_iff]
  constructor
  · rintro ⟨T, rfl, hd⟩
    obtain ⟨b, rfl⟩ := depth_eq_zero_iff.1 (Nat.le_zero.1 hd)
    exact ⟨b, by ext x; simp⟩
  · rintro ⟨b, rfl⟩
    exact ⟨leaf b, by ext x; simp, by simp⟩

/-- A constant Boolean function has decision-tree complexity `0`. -/
@[simp]
theorem decisionTreeDepth_const (b : Bool) :
    decisionTreeDepth (fun _ : Fin n → Bool => b) = 0 :=
  decisionTreeDepth_eq_zero_iff.2 ⟨b, rfl⟩

end TauCeti
