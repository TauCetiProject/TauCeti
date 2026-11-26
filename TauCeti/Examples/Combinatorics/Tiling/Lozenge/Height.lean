/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Height
import Mathlib.Tactic.FinCases

/-!
# Checks: heights of plane lozenge tilings

* The tilings `M₁`, `M₂`, `M₃` by lozenges of a single type, where `M_j` is
  `typeTiling (j - 1) = {e | e.k = j - 1}` (the field `e.k` counts directions from `0`), have
  heights `H_{M₁} = x`, `H_{M₂} = y` and `H_{M₃} = 0`.
* `H(x, y) = ⌊(x + y)/2⌋` is a height function, and its tiling has no lozenge of type 3, since
  `H(v + e₃) − H(v) = 1` everywhere.
* `H(x, y) = x + y` is not a height function: its increment along `e₃` is `2`.
-/

public section

namespace TauCeti.Examples.LozengeHeightChecks

open TauCeti

/-- The plane tiling by lozenges of the single type `j`: the edges of direction `j`. -/
def typeTiling (j : Fin 3) : Set TriEdge :=
  {e | e.k = j}

@[simp] theorem mem_typeTiling {j : Fin 3} {e : TriEdge} : e ∈ typeTiling j ↔ e.k = j :=
  Iff.rfl

/-- Every face has exactly one edge of each direction, so `typeTiling j` is a plane tiling. -/
theorem isTiling_typeTiling (j : Fin 3) : IsTiling Set.univ (typeTiling j) := by
  rw [isTiling_univ_iff]
  intro f
  rw [TriFace.existsUnique_mem_edges_iff]
  exact ⟨j, mem_typeTiling.2 (TriFace.edge_k f j), fun k hk => by simpa using hk⟩

/-- The height of a single-type tiling is the given function once it has the right increments
and vanishes at `0`. -/
theorem tilingHeight_typeTiling_eq {j : Fin 3} {g : ℤ × ℤ → ℤ}
    (hg : ∀ e : TriEdge, heightCochain (typeTiling j) e = g e.target - g e.v) (hg0 : g 0 = 0) :
    tilingHeight (typeTiling j) = g :=
  ((isTiling_typeTiling j).eq_tilingHeight (isCochainPrimitiveOn_univ_iff.2 hg) hg0).symm

theorem heightCochain_typeTiling (j : Fin 3) (e : TriEdge) :
    heightCochain (typeTiling j) e =
      if e.k = j then 1 - neutralIncrement e else neutralIncrement e := by
  by_cases h : e.k = j
  · simp only [heightCochain_of_mem (mem_typeTiling.2 h), h, ↓reduceIte]
  · simp only [heightCochain_of_notMem (mt mem_typeTiling.1 h), h, ↓reduceIte]

/-- `H_{M₁}(x, y) = x`. -/
example : tilingHeight (typeTiling 0) = fun v => v.1 := by
  refine tilingHeight_typeTiling_eq (fun ⟨v, k⟩ => ?_) rfl
  rw [heightCochain_typeTiling]
  fin_cases k <;> simp

/-- `H_{M₂}(x, y) = y`. -/
example : tilingHeight (typeTiling 1) = fun v => v.2 := by
  refine tilingHeight_typeTiling_eq (fun ⟨v, k⟩ => ?_) rfl
  rw [heightCochain_typeTiling]
  fin_cases k <;> simp

/-- `H_{M₃} = 0`. -/
example : tilingHeight (typeTiling 2) = 0 := by
  refine tilingHeight_typeTiling_eq (fun ⟨v, k⟩ => ?_) rfl
  rw [heightCochain_typeTiling]
  fin_cases k <;> simp

/-- `⌊(x + y)/2⌋`, a height function with no lozenge of type 3. -/
def halfSumHeight (v : ℤ × ℤ) : ℤ :=
  (v.1 + v.2) / 2

theorem halfSumHeight_apply (v : ℤ × ℤ) : halfSumHeight v = (v.1 + v.2) / 2 := by
  rw [halfSumHeight]

/-- `⌊(x + y)/2⌋` is a height function. -/
theorem isHeightFunction_halfSumHeight : IsHeightFunction halfSumHeight := by
  rw [isHeightFunction_def]
  rintro ⟨⟨x, y⟩, k⟩
  fin_cases k <;> simp [halfSumHeight] <;> omega

/-- The tiling of `⌊(x + y)/2⌋` has no lozenge of type 3. -/
example (e : TriEdge) (he : e ∈ tilingOfHeight halfSumHeight) : e.k ≠ 2 := by
  obtain ⟨⟨x, y⟩, k⟩ := e
  rw [mem_tilingOfHeight] at he
  rintro rfl
  simp [halfSumHeight] at he
  omega

/-- `x + y` is not a height function: its increment along `e₃` is `2`. -/
example : ¬ IsHeightFunction fun v => v.1 + v.2 := fun h => by
  rcases isHeightFunction_def.1 h ⟨0, 2⟩ with h | h <;> simp at h

end TauCeti.Examples.LozengeHeightChecks
