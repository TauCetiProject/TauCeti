/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.HomotopyGroup
public import TauCeti.Topology.Homotopy.HomotopyGroup.TransAt
public import TauCeti.Topology.Circle.Degree
import Mathlib.Tactic.FinCases
import TauCeti.Topology.Path.Map

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
* `TauCeti.degree_squareBoundaryLoop_map`: a continuous map from the square to the circle has
  degree zero along the boundary loop.
* `TauCeti.degree_squareBoundaryLoop_map'_eq_add`: the degree of a map to the circle along the
  boundary loop of the square is the sum of its degrees along the boundary loops of the halves.
-/

public section

open Set
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

/-! ### Maps from the square to the circle -/

/-- A continuous map `G` from the square to the circle has degree zero along the boundary loop of
the square: the loop contracts through the square to its corner. -/
theorem degree_squareBoundaryLoop_map {G : (I^Fin 2) → Circle} (hG : Continuous G) :
    Circle.degree (squareBoundaryLoop.map hG) = 0 := by
  let K : C(I × I, Circle) := ⟨fun p ↦ G fun i ↦ σ p.1 * squareBoundaryLoop p.2 i, by fun_prop⟩
  refine (Circle.degree_eq_of_homotopy _ (Path.refl (G 0)) K
    (fun t ↦ ?_) (fun t ↦ ?_) (fun s ↦ ?_)).trans (Circle.degree_refl _)
  · simp only [K, ContinuousMap.coe_mk, unitInterval.symm_zero, one_mul, Path.map_coe,
      Function.comp_apply]
  · simp only [K, ContinuousMap.coe_mk, unitInterval.symm_one, zero_mul, Path.refl_apply,
      ← Pi.zero_def]
  · simp only [K, ContinuousMap.coe_mk, Path.source, Path.target]

/-- **Subdivision of the square.** Let `H` be a map from the square to the circle, continuous on
a set `U` that contains the boundary of the square and the boundaries of its two halves
`Cube.firstHalf 0` and `Cube.secondHalf 0`. The degree of `H` along the boundary loop of the square
is the sum of its degrees along the boundary loops of the halves: these run along the seam
`y 0 = 1 / 2` in opposite directions, so the angles swept along the seam cancel, and the halves of
the bottom and top edges add up. -/
theorem degree_squareBoundaryLoop_map'_eq_add {H : (I^Fin 2) → Circle} {U : Set (I^Fin 2)}
    (hH : ContinuousOn H U) (hb : Cube.boundary (Fin 2) ⊆ U)
    (hl : MapsTo (Cube.firstHalf 0) (Cube.boundary (Fin 2)) U)
    (hr : MapsTo (Cube.secondHalf 0) (Cube.boundary (Fin 2)) U) :
    Circle.degree (squareBoundaryLoop.map' (hH.mono (range_subset_iff.2 fun t ↦
        hb (squareBoundaryLoop_mem_boundary t)))) =
      Circle.degree ((squareBoundaryLoop.map (Cube.continuous_firstHalf 0)).map'
          (hH.mono (range_subset_iff.2 fun t ↦ hl (squareBoundaryLoop_mem_boundary t)))) +
        Circle.degree ((squareBoundaryLoop.map (Cube.continuous_secondHalf 0)).map'
          (hH.mono (range_subset_iff.2 fun t ↦ hr (squareBoundaryLoop_mem_boundary t)))) := by
  have hm {a b : I^Fin 2} {c : Path a b} (hc : ∀ t, c t ∈ U) : ContinuousOn H (range c) :=
    hH.mono (range_subset_iff.2 hc)
  -- Images of paths along the boundary of the square in the two halves.
  have hl' {a b : I^Fin 2} {c : Path a b} (hc : ∀ t, c t ∈ Cube.boundary (Fin 2)) (t : I) :
      c.map (Cube.continuous_firstHalf 0) t ∈ U := by
    rw [Path.map_coe, Function.comp_apply]
    exact hl (hc t)
  have hr' {a b : I^Fin 2} {c : Path a b} (hc : ∀ t, c t ∈ Cube.boundary (Fin 2)) (t : I) :
      c.map (Cube.continuous_secondHalf 0) t ∈ U := by
    rw [Path.map_coe, Function.comp_apply]
    exact hr (hc t)
  have hb' {a b : I^Fin 2} {c : Path a b} (hc : ∀ t, c t ∈ Cube.boundary (Fin 2)) (t : I) :
      c t ∈ U :=
    hb (hc t)
  -- Continuous lifts of `H` along the edges of the square and the seam.
  obtain ⟨θB, hθB⟩ := Circle.exists_lift (squareEdge₀.map' (hm (hb' squareEdge₀_mem_boundary)))
  obtain ⟨θR, hθR⟩ := Circle.exists_lift (squareEdge₁.map' (hm (hb' squareEdge₁_mem_boundary)))
  obtain ⟨θT, hθT⟩ := Circle.exists_lift (squareEdge₂.map' (hm (hb' squareEdge₂_mem_boundary)))
  obtain ⟨θL, hθL⟩ := Circle.exists_lift (squareEdge₃.map' (hm (hb' squareEdge₃_mem_boundary)))
  obtain ⟨θS, hθS⟩ := Circle.exists_lift
    ((squareEdge₁.map (Cube.continuous_firstHalf 0)).map' (hm (hl' squareEdge₁_mem_boundary)))
  -- The angle swept along each piece, read off from the lifts along the edges and the seam.
  have F₀ := Circle.angleChange_eq_sub _ θB.continuous hθB
  have F₁ := Circle.angleChange_eq_sub _ θR.continuous hθR
  have F₂ := Circle.angleChange_eq_sub _ θT.continuous hθT
  have F₃ := Circle.angleChange_eq_sub _ θL.continuous hθL
  have L₁ := Circle.angleChange_eq_sub _ θS.continuous hθS
  have L₀ := Circle.angleChange_map'_eq_sub_of_reparam hH (hl' squareEdge₀_mem_boundary)
    (hb' squareEdge₀_mem_boundary) θB.continuous hθB
    (r := fun t ↦ projIcc 0 1 zero_le_one ((t : ℝ) / 2)) (by fun_prop) fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, firstHalf_squareEdge₀]
  have R₀ := Circle.angleChange_map'_eq_sub_of_reparam hH (hr' squareEdge₀_mem_boundary)
    (hb' squareEdge₀_mem_boundary) θB.continuous hθB
    (r := fun t ↦ projIcc 0 1 zero_le_one (((t : ℝ) + 1) / 2)) (by fun_prop) fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, secondHalf_squareEdge₀]
  have L₂ := Circle.angleChange_map'_eq_sub_of_reparam hH (hl' squareEdge₂_mem_boundary)
    (hb' squareEdge₂_mem_boundary) θT.continuous hθT
    (r := fun t ↦ σ (projIcc 0 1 zero_le_one ((σ t : ℝ) / 2))) (by fun_prop) fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, firstHalf_squareEdge₂]
  have R₂ := Circle.angleChange_map'_eq_sub_of_reparam hH (hr' squareEdge₂_mem_boundary)
    (hb' squareEdge₂_mem_boundary) θT.continuous hθT
    (r := fun t ↦ σ (projIcc 0 1 zero_le_one (((σ t : ℝ) + 1) / 2))) (by fun_prop) fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, secondHalf_squareEdge₂]
  have L₃ := Circle.angleChange_map'_eq_sub_of_reparam hH (hl' squareEdge₃_mem_boundary)
    (hb' squareEdge₃_mem_boundary) θL.continuous hθL (r := id) continuous_id fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, firstHalf_squareEdge₃, id]
  have R₁ := Circle.angleChange_map'_eq_sub_of_reparam hH (hr' squareEdge₁_mem_boundary)
    (hb' squareEdge₁_mem_boundary) θR.continuous hθR (r := id) continuous_id fun t ↦ by
      rw [Path.map_coe, Function.comp_apply, secondHalf_squareEdge₁, id]
  have R₃ := Circle.angleChange_map'_eq_sub_of_reparam hH (hr' squareEdge₃_mem_boundary)
    (hl' squareEdge₁_mem_boundary) θS.continuous hθS (r := σ) unitInterval.continuous_symm
    fun t ↦ by
      rw [Path.map_coe, Path.map_coe, Function.comp_apply, Function.comp_apply,
        secondHalf_squareEdge₃]
  -- Each boundary loop is a concatenation of four pieces. The angles along the seam cancel, and
  -- the halves of the bottom and top edges add up.
  have key :
      Circle.angleChange (squareBoundaryLoop.map' (hm (hb' squareBoundaryLoop_mem_boundary))) =
      Circle.angleChange ((squareBoundaryLoop.map (Cube.continuous_firstHalf 0)).map'
          (hm (hl' squareBoundaryLoop_mem_boundary))) +
        Circle.angleChange ((squareBoundaryLoop.map (Cube.continuous_secondHalf 0)).map'
          (hm (hr' squareBoundaryLoop_mem_boundary))) := by
    simp only [squareBoundaryLoop_def, Path.map_trans, Path.map'_trans, Circle.angleChange_trans]
    rw [F₀, F₁, F₂, F₃, L₀, L₁, L₂, L₃, R₀, R₁, R₂, R₃]
    norm_num [unitInterval.symm_zero, unitInterval.symm_one]
    ring
  rw [Circle.angleChange_eq_degree_mul, Circle.angleChange_eq_degree_mul,
    Circle.angleChange_eq_degree_mul, ← add_mul] at key
  exact_mod_cast mul_right_cancel₀ (by positivity : (2 * Real.pi : ℝ) ≠ 0) key

end TauCeti
