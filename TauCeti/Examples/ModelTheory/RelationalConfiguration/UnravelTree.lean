/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.RelationalConfiguration.GraphClass
public import TauCeti.ModelTheory.RelationalConfiguration.UnravelTree

/-!
# Checks for the tagged tree of an unravelled graph code

The Checks of the tagged tree order `TauCeti.RelationalConfiguration.unravelTreeRel χ` on
`List ℚ × Option ℕ`, for a colouring `χ` of `List ℚ`.

* For `χ(x) = 0`, the tags of `x` other than `(x, some 0)` are pairwise incomparable: above
  `(x, some 0)` lie only leaves, a subtree of height `2`. For `χ(x) = 1`,
  `(x, some 0) < (x, some 1) < (x, some 2)` is a chain, of height `3`.
* The surplus tags `(x, some m)`, `m > χ(x) + 1`, are leaves directly above `(x, some 0)`: they are
  maximal, and no node lies strictly between. Keeping them changes no height; removing them would
  make the vertex set depend on the code.
* Without tags, the original nodes form the same tree, the prefix order, for every colouring, so
  the tags carry all of the information.
* The constant-true code of the language of graphs, outside `graphClass`, colours every node of
  length `1` differently from every simple graph: its diagonal bit is true, while a simple graph
  has no loops.
-/

public section

namespace TauCeti.Examples.UnravelTree

open FirstOrder FirstOrder.Language TauCeti.RelationalConfiguration

variable {χ : List ℚ → ℕ} (x : List ℚ)

/-- For `χ(x) = 0`, two distinct tags of `x` other than `(x, some 0)` are incomparable. -/
theorem not_unravelTreeRel_of_colour_eq_zero (h : χ x = 0) {m m' : ℕ} (hm : 0 < m)
    (hne : m ≠ m') : ¬ unravelTreeRel χ (x, some m) (x, some m') := by
  rw [unravelTreeRel_some_some, tagLE_iff, h]
  omega

/-- For `χ(x) = 1`, the tags `(x, some 0) < (x, some 1) < (x, some 2)` form a chain. -/
theorem unravelTreeRel_chain_of_colour_eq_one (h : χ x = 1) :
    unravelTreeRel χ (x, some 0) (x, some 1) ∧ unravelTreeRel χ (x, some 1) (x, some 2) := by
  simp [unravelTreeRel_some_some, tagLE_iff, h]

/-- The height differs: `(x, some 1) < (x, some 2)` holds for `χ(x) = 1` and fails for
`χ(x) = 0`. -/
example : (unravelTreeRel (fun _ => 1) (x, some 1) (x, some 2)) ∧
    ¬ unravelTreeRel (fun _ => 0) (x, some 1) (x, some 2) :=
  ⟨(unravelTreeRel_chain_of_colour_eq_one x rfl).2,
    not_unravelTreeRel_of_colour_eq_zero x rfl one_pos (by decide)⟩

/-- A surplus tag `(x, some m)`, `m > χ(x) + 1`, is a leaf: nothing lies strictly above it. -/
theorem eq_of_unravelTreeRel_surplus {m : ℕ} (hm : χ x + 1 < m) {q : List ℚ × Option ℕ}
    (hq : unravelTreeRel χ (x, some m) q) : q = (x, some m) := by
  obtain ⟨y, _ | m'⟩ := q
  · exact absurd hq not_unravelTreeRel_some_none
  · obtain ⟨rfl, hle⟩ := unravelTreeRel_some_some.1 hq
    rw [tagLE_iff] at hle
    have : m' = m := by omega
    rw [this]

/-- A surplus tag lies directly above `(x, some 0)`: every node between them is one of the two. -/
theorem eq_or_eq_of_between_surplus {m : ℕ} (hm : χ x + 1 < m) {z : List ℚ × Option ℕ}
    (h₁ : unravelTreeRel χ (x, some 0) z) (h₂ : unravelTreeRel χ z (x, some m)) :
    z = (x, some 0) ∨ z = (x, some m) := by
  obtain ⟨y, _ | k⟩ := z
  · exact absurd h₁ not_unravelTreeRel_some_none
  · obtain ⟨rfl, -⟩ := unravelTreeRel_some_some.1 h₁
    obtain ⟨-, hle⟩ := unravelTreeRel_some_some.1 h₂
    rw [tagLE_iff] at hle
    rcases hle with rfl | rfl | hle
    · exact Or.inr rfl
    · exact Or.inl rfl
    · omega

/-- Without tags, the original nodes form the prefix order for every colouring. -/
theorem unravelTreeRel_none_none_iff (χ' : List ℚ → ℕ) (y : List ℚ) :
    unravelTreeRel χ (x, none) (y, none) ↔ unravelTreeRel χ' (x, none) (y, none) := by
  simp

/-- **The constant-true code is coloured unlike any simple graph.** At a node of length `1`, the
diagonal bit of the constant-true code is true, and that of a simple graph is false. -/
theorem unravelColor_mk_true_ne {c : RelationalConfiguration Language.graph ℕ}
    (hc : c ∈ graphClass) (q r : ℚ) :
    unravelColor (RelationalConfiguration.mk fun _ => true) [q] ≠ unravelColor c [r] := by
  intro h
  have := congrArg Prod.snd ((unravelColor_eq_iff.1 h).2 0 (by simp) 0 (by simp))
  rw [unravelBits_snd, unravelBits_snd, RelationalConfiguration.eval_mk,
    (isSimpleGraph_iff.1 (mem_graphClass.1 hc)).2] at this
  exact Bool.noConfusion this

end TauCeti.Examples.UnravelTree
