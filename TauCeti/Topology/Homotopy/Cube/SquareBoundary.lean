/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.TransAt
import Mathlib.Tactic.FinCases

/-!
# The boundary loop of the square

The boundary of the square `I^(Fin 2)` is a circle. This file parametrizes it by the loop
`TauCeti.squareBoundaryLoop` based at the corner `0`, which runs once around the boundary,
counterclockwise for the orientation in which coordinate `0` comes first. It is the concatenation
of the four edges of the square (`TauCeti.squareBoundaryLoop_def`).

## Main declarations

* `TauCeti.squareEdge₀`, `TauCeti.squareEdge₁`, `TauCeti.squareEdge₂`, `TauCeti.squareEdge₃`: the
  bottom, right, top and left edges of the square, traversed counterclockwise.
* `TauCeti.squareBoundaryLoop`: the counterclockwise boundary loop of the square.
* `TauCeti.squareBoundaryLoop_def`: it is the concatenation of the four edges.
* `TauCeti.squareBoundaryLoop_mem_boundary`: it runs along the boundary of the square.
* `TauCeti.firstHalf_squareEdge₀`, `TauCeti.secondHalf_squareEdge₃` and their analogues: the maps
  `TauCeti.Cube.firstHalf 0` and `TauCeti.Cube.secondHalf 0` of the square onto its halves send
  the edges of the square to halves of edges, edges, or the seam `y 0 = 1 / 2`.
-/

public section

open scoped unitInterval Topology

namespace TauCeti

/-- The bottom edge `y 1 = 0` of the square, from `0` to `![1, 0]`. -/
def squareEdge₀ : Path (0 : I^Fin 2) ![1, 0] where
  toFun t := ![t, 0]
  source' := by ext i; fin_cases i <;> rfl
  target' := rfl

/-- The right edge `y 0 = 1` of the square, from `![1, 0]` to `![1, 1]`. -/
def squareEdge₁ : Path (![1, 0] : I^Fin 2) ![1, 1] where
  toFun t := ![1, t]
  source' := rfl
  target' := rfl

/-- The top edge `y 1 = 1` of the square, from `![1, 1]` to `![0, 1]`. -/
def squareEdge₂ : Path (![1, 1] : I^Fin 2) ![0, 1] where
  toFun t := ![σ t, 1]
  source' := by simp
  target' := by simp

/-- The left edge `y 0 = 0` of the square, from `![0, 1]` to `0`. -/
def squareEdge₃ : Path (![0, 1] : I^Fin 2) 0 where
  toFun t := ![0, σ t]
  source' := by simp
  target' := by ext i; fin_cases i <;> simp

@[simp]
theorem squareEdge₀_apply (t : I) : squareEdge₀ t = ![t, 0] :=
  (rfl)

@[simp]
theorem squareEdge₁_apply (t : I) : squareEdge₁ t = ![1, t] :=
  (rfl)

@[simp]
theorem squareEdge₂_apply (t : I) : squareEdge₂ t = ![σ t, 1] :=
  (rfl)

@[simp]
theorem squareEdge₃_apply (t : I) : squareEdge₃ t = ![0, σ t] :=
  (rfl)

/-- The bottom edge of the square lies on its boundary. -/
theorem squareEdge₀_mem_boundary (t : I) : squareEdge₀ t ∈ Cube.boundary (Fin 2) :=
  ⟨1, Or.inl rfl⟩

/-- The right edge of the square lies on its boundary. -/
theorem squareEdge₁_mem_boundary (t : I) : squareEdge₁ t ∈ Cube.boundary (Fin 2) :=
  ⟨0, Or.inr rfl⟩

/-- The top edge of the square lies on its boundary. -/
theorem squareEdge₂_mem_boundary (t : I) : squareEdge₂ t ∈ Cube.boundary (Fin 2) :=
  ⟨1, Or.inr rfl⟩

/-- The left edge of the square lies on its boundary. -/
theorem squareEdge₃_mem_boundary (t : I) : squareEdge₃ t ∈ Cube.boundary (Fin 2) :=
  ⟨0, Or.inl rfl⟩

/-- The loop running once around the boundary of the square `I^(Fin 2)`, counterclockwise for
the orientation in which coordinate `0` comes first: from the corner `0` along the edge
`y 1 = 0`, then up the edge `y 0 = 1`, back along the edge `y 1 = 1` and down the edge `y 0 = 0`. -/
noncomputable def squareBoundaryLoop : Path (0 : I^Fin 2) 0 :=
  squareEdge₀.trans <| squareEdge₁.trans <| squareEdge₂.trans squareEdge₃

/-- The boundary loop of the square is the concatenation of its four edges. -/
theorem squareBoundaryLoop_def :
    squareBoundaryLoop = squareEdge₀.trans (squareEdge₁.trans (squareEdge₂.trans squareEdge₃)) :=
  (rfl)

/-- The boundary loop of the square runs along the boundary. -/
theorem squareBoundaryLoop_mem_boundary (t : I) :
    squareBoundaryLoop t ∈ Cube.boundary (Fin 2) := by
  have h := Set.mem_range_self (f := squareBoundaryLoop) t
  rw [squareBoundaryLoop_def, Path.trans_range, Path.trans_range, Path.trans_range] at h
  rcases h with ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩ | ⟨r, hr⟩ <;> rw [squareBoundaryLoop_def, ← hr]
  exacts [squareEdge₀_mem_boundary r, squareEdge₁_mem_boundary r, squareEdge₂_mem_boundary r,
    squareEdge₃_mem_boundary r]

/-! ### The halves of the square -/

/-- The first half of the square meets the bottom edge in its first half. -/
theorem firstHalf_squareEdge₀ (t : I) :
    Cube.firstHalf 0 (squareEdge₀ t) =
      squareEdge₀ (Set.projIcc 0 1 zero_le_one ((t : ℝ) / 2)) := by
  ext j; fin_cases j <;> simp [Cube.firstHalf_apply]

/-- The second half of the square meets the bottom edge in its second half. -/
theorem secondHalf_squareEdge₀ (t : I) :
    Cube.secondHalf 0 (squareEdge₀ t) =
      squareEdge₀ (Set.projIcc 0 1 zero_le_one (((t : ℝ) + 1) / 2)) := by
  ext j; fin_cases j <;> simp [Cube.secondHalf_apply]

/-- The first half of the square meets the top edge in its second half. -/
theorem firstHalf_squareEdge₂ (t : I) :
    Cube.firstHalf 0 (squareEdge₂ t) =
      squareEdge₂ (σ (Set.projIcc 0 1 zero_le_one ((σ t : ℝ) / 2))) := by
  ext j; fin_cases j <;> simp [Cube.firstHalf_apply]

/-- The second half of the square meets the top edge in its first half. -/
theorem secondHalf_squareEdge₂ (t : I) :
    Cube.secondHalf 0 (squareEdge₂ t) =
      squareEdge₂ (σ (Set.projIcc 0 1 zero_le_one (((σ t : ℝ) + 1) / 2))) := by
  ext j; fin_cases j <;> simp [Cube.secondHalf_apply]

/-- The left edge of the first half of the square is the left edge of the square. -/
theorem firstHalf_squareEdge₃ (t : I) :
    Cube.firstHalf 0 (squareEdge₃ t) = squareEdge₃ t := by
  ext j; fin_cases j <;> simp

/-- The right edge of the second half of the square is the right edge of the square. -/
theorem secondHalf_squareEdge₁ (t : I) :
    Cube.secondHalf 0 (squareEdge₁ t) = squareEdge₁ t := by
  ext j; fin_cases j <;> simp

/-- The left edge of the second half of the square is the seam, the right edge of the first half,
traversed backwards. -/
theorem secondHalf_squareEdge₃ (t : I) :
    Cube.secondHalf 0 (squareEdge₃ t) = Cube.firstHalf 0 (squareEdge₁ (σ t)) := by
  ext j; fin_cases j <;> simp

end TauCeti
