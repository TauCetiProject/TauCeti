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

Examples and sanity checks for the tagged tree order
`TauCeti.RelationalConfiguration.unravelTreeRel χ` on `List ℚ × Option ℕ`, for a colouring `χ` of
`List ℚ`.

* The tags `(x, some 0) ≤ (x, some 1) ≤ ⋯ ≤ (x, some (χ(x) + 1))` form a chain of `χ(x) + 2`
  tags, starting at `(x, some 0)`. For `χ(x) = 0`, the tags of `x` other than `(x, some 0)` are
  pairwise incomparable. For `χ(x) = 1`, `(x, some 0) ≤ (x, some 1) ≤ (x, some 2)` is a chain.
* The surplus tags `(x, some m)`, `m > χ(x) + 1`, are leaves directly above `(x, some 0)`: they are
  maximal, and no node lies strictly between. Keeping them changes no height; removing them would
  make the vertex set depend on the code.
* Without tags, the original nodes form the same tree, the prefix order, for every colouring, so
  the tags carry all of the information.
* The constant-true code of the language of graphs, outside `graphClass`, colours every node of
  length `1` with a colour that occurs at no node of any simple graph.
-/

public section

namespace TauCeti.Examples.UnravelTree

open FirstOrder FirstOrder.Language TauCeti.RelationalConfiguration

variable {χ : List ℚ → ℕ} (x : List ℚ)

/-- For `χ(x) = 0`, two distinct tags of `x` other than `(x, some 0)` are incomparable. -/
theorem not_unravelTreeRel_of_color_eq_zero (h : χ x = 0) {m m' : ℕ} (hm : 0 < m)
    (hne : m ≠ m') : ¬ unravelTreeRel χ (x, some m) (x, some m') := by
  rw [unravelTreeRel_some_some, tagLE_iff, h]
  omega

/-- The tags `(x, some m)` with `m ≤ χ(x) + 1` form a chain: `(x, some m) ≤ (x, some m')` for
`m ≤ m' ≤ χ(x) + 1`. These are the `χ(x) + 2` tags `(x, some 0) ≤ ⋯ ≤ (x, some (χ(x) + 1))`,
starting at `(x, some 0)`. -/
theorem unravelTreeRel_some_some_of_le {m m' : ℕ} (h : m ≤ m') (h' : m' ≤ χ x + 1) :
    unravelTreeRel χ (x, some m) (x, some m') :=
  unravelTreeRel_some_some.2 ⟨rfl, by rw [tagLE_iff]; omega⟩

/-- For `χ(x) = 1`, the tags `(x, some 0) < (x, some 1) < (x, some 2)` form a chain. -/
theorem unravelTreeRel_chain_of_color_eq_one (h : χ x = 1) :
    unravelTreeRel χ (x, some 0) (x, some 1) ∧ unravelTreeRel χ (x, some 1) (x, some 2) := by
  simp [unravelTreeRel_some_some, tagLE_iff, h]

/-- The comparison `(x, some 1) ≤ (x, some 2)` holds for `χ(x) = 1` and fails for `χ(x) = 0`. -/
example : (unravelTreeRel (fun _ => 1) (x, some 1) (x, some 2)) ∧
    ¬ unravelTreeRel (fun _ => 0) (x, some 1) (x, some 2) :=
  ⟨(unravelTreeRel_chain_of_color_eq_one x rfl).2,
    not_unravelTreeRel_of_color_eq_zero x rfl one_pos (by decide)⟩

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

/-- Without tags, the comparison of two original nodes does not depend on the colouring: for every
colouring it is the prefix order `x <+: y` of `unravelTreeRel_none_left`. -/
theorem unravelTreeRel_none_none_congr_color (χ' : List ℚ → ℕ) (y : List ℚ) :
    unravelTreeRel χ (x, none) (y, none) ↔ unravelTreeRel χ' (x, none) (y, none) := by
  simp

/-- **At nodes of length `1`, the constant-true code has a colour that no simple graph has at any
node.** For every `c ∈ graphClass` and every node `y`, the colour of `[q]` under the constant-true
code differs from the colour of `y` under `c`. -/
theorem unravelColor_mk_true_ne {c : RelationalConfiguration Language.graph ℕ}
    (hc : c ∈ graphClass) (q : ℚ) (y : List ℚ) :
    unravelColor (RelationalConfiguration.mk fun _ => true) [q] ≠ unravelColor c y := by
  intro h
  have := congrArg Prod.snd ((unravelColor_eq_iff.1 h).2 0 (by simp) 0 (by simp))
  rw [unravelBits_snd, unravelBits_snd, RelationalConfiguration.eval_mk,
    (isSimpleGraph_iff.1 (mem_graphClass.1 hc)).2] at this
  exact Bool.noConfusion this

end TauCeti.Examples.UnravelTree
