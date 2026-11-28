/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.ComparisonTree.Complexity
public import TauCeti.Combinatorics.ComparisonTree.Counting
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

/-!
# Examples of comparison trees

The tree on two items that compares item `0` with item `1` has depth `1` and outputs the smaller
item on inputs with different values; a tie follows the second subtree. A tree whose root compares
an item with itself sends every input to its second subtree, so its cost can stay below its depth
on every input: a lower bound on the depth is weaker than a lower bound on the cost.

For comparison complexity, a leaf does not sort two items, since it has one output and there are
two rankings, and a problem in which every output is correct has comparison complexity `0`.

For the counting bounds, the hypothesis that the outputs differ is needed: a leaf gives the
Kraft sum `2` on two inputs. The tree that compares `(0, 1)`, then `(1, 2)` and, where needed,
`(0, 2)` gives six different outputs on the six rankings of three items, with the costs
`2, 3, 3, 3, 3, 2`.
-/

public section

namespace TauCeti.Examples.ComparisonTree

open TauCeti CompTree

/-- The tree on two items that compares item `0` with item `1` and outputs the smaller one. -/
abbrev compareTwo : CompTree 2 (Fin 2) :=
  node 0 1 (leaf 0) (leaf 1)

example : compareTwo.depth = 1 := by simp [compareTwo]

example : compareTwo.eval ![(5 : ℕ), 7] = 0 := by simp [compareTwo]

example : compareTwo.eval ![(7 : ℕ), 5] = 1 := by simp [compareTwo]

/-- A tie follows the second subtree. -/
example : compareTwo.eval ![(5 : ℕ), 5] = 1 := by simp [compareTwo]

/-- A tree whose root compares item `0` with itself; its first subtree is never entered. -/
abbrev selfCompare : CompTree 2 (Fin 2) :=
  node 0 0 compareTwo (leaf 1)

example : selfCompare.depth = 2 := by simp [selfCompare, compareTwo]

/-- The cost of `selfCompare` is `1` on every input, below its depth `2`. -/
example {β : Type*} [LinearOrder β] (x : Fin 2 → β) : selfCompare.cost x = 1 := by
  simp [selfCompare]

/-- Sorting two items: all rankings are admissible and the only correct output is the ranking. -/
abbrev sortTwo : Equiv.Perm (Fin 2) → Equiv.Perm (Fin 2) → Prop :=
  fun σ τ => τ = σ

/-- A leaf does not sort two items: it has one output and there are two rankings. -/
example (τ : Equiv.Perm (Fin 2)) :
    ¬(leaf τ : CompTree 2 (Equiv.Perm (Fin 2))).Solves .univ sortTwo := by
  intro h
  have h₁ := solves_iff.1 h 1 (Set.mem_univ _)
  have h₂ := solves_iff.1 h (Equiv.swap 0 1) (Set.mem_univ _)
  simp only [eval_leaf, sortTwo] at h₁ h₂
  exact absurd (h₁.symm.trans h₂) (by decide)

/-- When every output is correct for every ranking, the comparison complexity is `0`. -/
example {n : ℕ} {α : Type*} (a : α) :
    IsComparisonComplexity (.univ : Set (Equiv.Perm (Fin n))) (fun _ (_ : α) => True) 0 :=
  ⟨⟨leaf a, solves_iff.2 fun _ _ => trivial, by simp⟩,
    fun _ _ => ⟨1, Set.mem_univ _, Nat.zero_le _⟩⟩

/-- The hypothesis on the outputs of `sum_two_inv_pow_cost_le_one` is needed: a leaf gives the
sum `2` on two inputs. -/
example :
    ∑ x ∈ ({![0], ![1]} : Finset (Fin 1 → ℕ)), (2⁻¹ : ℝ) ^ (leaf 0 : CompTree 1 ℕ).cost x = 2 := by
  rw [Finset.sum_pair (by decide)]
  norm_num [cost_leaf]

/-- The tree that compares `(0, 1)`, then `(1, 2)` and, where needed, `(0, 2)` gives six different
outputs on the six rankings of three items, with the costs `2, 3, 3, 3, 3, 2`. -/
example (t : CompTree 3 ℕ) (ht : t = node 0 1 (node 1 2 (leaf 0) (node 0 2 (leaf 1) (leaf 2)))
      (node 1 2 (node 0 2 (leaf 3) (leaf 4)) (leaf 5))) :
    [![0, 1, 2], ![0, 2, 1], ![1, 2, 0], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]].map t.eval =
        [0, 1, 2, 3, 4, 5] ∧
      [![0, 1, 2], ![0, 2, 1], ![1, 2, 0], ![1, 0, 2], ![2, 0, 1], ![2, 1, 0]].map t.cost =
        [2, 3, 3, 3, 3, 2] := by
  subst ht
  simp [eval_node, eval_leaf, cost_node, cost_leaf]

end TauCeti.Examples.ComparisonTree
