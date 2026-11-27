/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.PositiveSteps

/-!
# Checks: positive steps of walks

* The closed walk `0 → e₁ → e₃ → 0` in the edge graph of the white face `W(0)` has `2` positive
  steps and its reverse has `1`, adding up to its length `3`; counting every dart would give `3`
  both ways.
* The one-dart walk `0 → e₃` has `1` positive step, and the height `H_{M₁} = x` of the
  all-type-1 tiling rises by `1` along it, so the bound `H(v) − H(u) ≤ positiveSteps p` is sharp
  there. With Gorin's positive directions `(1, 0)`, `(0, 1)`, `(−1, −1)` this step would be
  negative and count `0`, and the bound would fail.
* In the unit hexagon, the six faces round `0`, the walk `(−1, 0) → 0 → (1, 0)` has `2` positive
  steps; counting instead the darts from `u + e_k` to `u` would give `0`. Every height function
  on the hexagon therefore rises by `0`, `1` or `2` from `(−1, 0)` to `(1, 0)`.
-/

public section

namespace TauCeti.Examples.PositiveStepsChecks

open TauCeti SimpleGraph

/-- The white face `W(0)`. -/
abbrev whiteZero : Set TriFace := {⟨(0, 0), true⟩}

theorem mem_regionEdges_whiteZero (k : Fin 3) :
    (⟨if k = 1 then (1, 0) else (0, 0), k⟩ : TriEdge) ∈ regionEdges whiteZero := by
  refine mem_regionEdges.2 ⟨_, Set.mem_singleton _, ?_⟩
  have := TriFace.edge_mem_edges ⟨(0, 0), true⟩ k
  simpa using this

/-- `0 → e₁` along the edge `⟨(0, 0), 0⟩` (direction `e₁`). -/
theorem adj₁ : (regionGraph whiteZero).Adj (0, 0) (1, 0) := by
  simpa using adj_of_mem_regionEdges (mem_regionEdges_whiteZero 0)

/-- `e₁ → e₃` along the edge `⟨(1, 0), 1⟩` (direction `e₂`). -/
theorem adj₂ : (regionGraph whiteZero).Adj (1, 0) (1, 1) := by
  simpa using adj_of_mem_regionEdges (mem_regionEdges_whiteZero 1)

/-- `0 → e₃` along the edge `⟨(0, 0), 2⟩` (direction `e₃`). -/
theorem adj₃ : (regionGraph whiteZero).Adj (0, 0) (1, 1) := by
  simpa using adj_of_mem_regionEdges (mem_regionEdges_whiteZero 2)

/-- The closed walk `0 → e₁ → e₃ → 0` round `W(0)`. -/
abbrev triangleWalk : (regionGraph whiteZero).Walk (0, 0) (0, 0) :=
  .cons adj₁ (.cons adj₂ (.cons adj₃.symm .nil))

/-- The walk round `W(0)` has `2` positive steps. -/
example : positiveSteps triangleWalk = 2 := by
  simp [isPositiveStep_iff]

/-- Its reverse has `1`. -/
example : positiveSteps triangleWalk.reverse = 1 := by
  simp [Walk.reverse_cons, isPositiveStep_iff]

/-- Together they make the length `3`. -/
example : positiveSteps triangleWalk + positiveSteps triangleWalk.reverse = 3 :=
  positiveSteps_add_positiveSteps_reverse _

/-- The one-dart walk `0 → e₃` has `1` positive step. -/
example : positiveSteps (.cons adj₃ .nil : (regionGraph whiteZero).Walk (0, 0) (1, 1)) = 1 := by
  simp [isPositiveStep_iff]

/-- `H_{M₁} = x` is a height function on `W(0)`. -/
theorem isHeightFunctionOn_fst : IsHeightFunctionOn whiteZero Prod.fst := by
  rw [isHeightFunctionOn_def]
  rintro ⟨v, k⟩ -
  fin_cases k <;> simp [latticeDir_zero, latticeDir_one, latticeDir_two]

/-- `H_{M₁} = x` rises by `1` along `0 → e₃`, the number of positive steps of that walk; a count
giving this step `0` would violate the bound. -/
example : ((1, 1) : ℤ × ℤ).1 - ((0, 0) : ℤ × ℤ).1 = 1 ∧
    ((1, 1) : ℤ × ℤ).1 - ((0, 0) : ℤ × ℤ).1 ≤
      positiveSteps (.cons adj₃ .nil : (regionGraph whiteZero).Walk (0, 0) (1, 1)) :=
  ⟨rfl, isHeightFunctionOn_fst.sub_le_positiveSteps _⟩

/-- The unit hexagon: the six faces round `0`. -/
abbrev unitHexagon : Set TriFace := vertexFaces (0, 0)

/-- `(−1, 0) → 0` along the edge `⟨(−1, 0), 0⟩` (direction `e₁`) of `W(−1, 0)`. -/
theorem adj_hex₁ : (regionGraph unitHexagon).Adj (-1, 0) (0, 0) := by
  have h : (⟨(-1, 0), 0⟩ : TriEdge) ∈ regionEdges unitHexagon :=
    mem_regionEdges.2 ⟨⟨(-1, 0), true⟩, by simp [unitHexagon], by simp⟩
  simpa using adj_of_mem_regionEdges h

/-- `0 → (1, 0)` along the edge `⟨(0, 0), 0⟩` (direction `e₁`) of `W(0)`. -/
theorem adj_hex₂ : (regionGraph unitHexagon).Adj (0, 0) (1, 0) := by
  have h : (⟨(0, 0), 0⟩ : TriEdge) ∈ regionEdges unitHexagon :=
    mem_regionEdges.2 ⟨⟨(0, 0), true⟩, by simp [unitHexagon], by simp⟩
  simpa using adj_of_mem_regionEdges h

/-- In the unit hexagon the walk `(−1, 0) → 0 → (1, 0)` has `2` positive steps, and its reverse,
whose darts go from `u + e₁` to `u`, has none. -/
example :
    positiveSteps (.cons adj_hex₁ (.cons adj_hex₂ .nil) :
        (regionGraph unitHexagon).Walk (-1, 0) (1, 0)) = 2 ∧
      positiveSteps (.cons adj_hex₁ (.cons adj_hex₂ .nil) :
        (regionGraph unitHexagon).Walk (-1, 0) (1, 0)).reverse = 0 := by
  constructor
  · simp [isPositiveStep_iff]
  · simp [Walk.reverse_cons, isPositiveStep_iff]

/-- Every height function on the unit hexagon rises by `0`, `1` or `2` from `(−1, 0)` to
`(1, 0)`. -/
example {H : ℤ × ℤ → ℤ} (hH : IsHeightFunctionOn unitHexagon H) :
    0 ≤ H (1, 0) - H (-1, 0) ∧ H (1, 0) - H (-1, 0) ≤ 2 := by
  let p : (regionGraph unitHexagon).Walk (-1, 0) (1, 0) := .cons adj_hex₁ (.cons adj_hex₂ .nil)
  have h₁ := hH.sub_le_positiveSteps p
  have h₂ := hH.neg_positiveSteps_reverse_le_sub p
  simp only [p, positiveSteps_cons, positiveSteps_nil, Walk.reverse_cons, Walk.reverse_nil,
    Walk.nil_append, Walk.cons_append, isPositiveStep_iff] at h₁ h₂
  norm_num at h₁ h₂
  omega

end TauCeti.Examples.PositiveStepsChecks
