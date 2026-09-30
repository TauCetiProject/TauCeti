/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Basic
public import Mathlib.Topology.Category.TopCat.Basic

/-!
# Skeletal objects of relative CW complexes

The stages of a relative CW complex's skeletal filtration, bundled as topological spaces.

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

open Metric Set Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X] [T2Space X]
  {D : Set X} (C : Set X) [RelCWComplex C D]

/-- The `n`-th stage of the skeletal filtration, as an object of `TopCat`. -/
abbrev skeletonObj (n : ℕ) : TopCat.{w} := TopCat.of (skeletonLT C (n : ℕ∞) : Set X)

variable {C}

/-- The characteristic map of an `n`-cell sends the open unit ball into its open cell, which is
disjoint from `skeletonLT C n`. -/
lemma map_notMem_skeletonLT {n : ℕ} (j : cell C n) {y : Fin n → ℝ} (hy : ‖y‖ < 1) :
    map n j y ∉ (skeletonLT C (n : ℕ∞) : Set X) := fun h ↦
  (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left h ⟨y, mem_ball_zero_iff.2 hy, rfl⟩

omit [T2Space X] in
/-- Two points of open unit balls with the same image under characteristic maps of `n`-cells come
from the same cell and are equal. -/
lemma map_eq_map_iff {n : ℕ} {i j : cell C n} {y z : Fin n → ℝ} (hy : ‖y‖ < 1)
    (hz : ‖z‖ < 1) : map n i y = map n j z ↔ i = j ∧ y = z := by
  refine ⟨fun h ↦ ?_, fun ⟨hij, hyz⟩ ↦ hij ▸ hyz ▸ rfl⟩
  obtain rfl : i = j := by
    by_contra hne
    refine (disjoint_openCell_of_ne (by simpa using hne)).ne_of_mem
      ⟨y, mem_ball_zero_iff.2 hy, rfl⟩ ⟨z, mem_ball_zero_iff.2 hz, rfl⟩ h
  refine ⟨rfl, (map n i).injOn ?_ ?_ h⟩ <;> rw [source_eq] <;> simpa

/-- A point of `skeletonLT C (n + 1)` lies in `skeletonLT C n` or is the image of a point of the
open unit ball under the characteristic map of an `n`-cell. -/
lemma mem_skeletonLT_or_exists_map {n : ℕ} {x : X}
    (hx : x ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X)) :
    x ∈ (skeletonLT C (n : ℕ∞) : Set X) ∨
      ∃ (j : cell C n) (y : Fin n → ℝ), ‖y‖ < 1 ∧ map n j y = x := by
  rw [Nat.cast_succ, ← skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ] at hx
  obtain hx | hx := hx
  · exact .inl hx
  obtain ⟨j, y, hy, rfl⟩ := mem_iUnion.1 hx
  rcases (mem_closedBall_zero_iff.1 hy).lt_or_eq with hy | hy
  · exact .inr ⟨j, y, hy, rfl⟩
  · exact .inl (cellFrontier_subset_skeletonLT n j ⟨y, mem_sphere_zero_iff_norm.2 hy, rfl⟩)

/-- The characteristic map of a closed `n`-cell lands in the `(n + 1)`-skeleton. -/
lemma map_mem_skeletonLT_succ {n : ℕ} (j : cell C n) {y : Fin n → ℝ} (hy : ‖y‖ ≤ 1) :
    map n j y ∈ (skeletonLT C ((n + 1 : ℕ) : ℕ∞) : Set X) := by
  rw [Nat.cast_succ]
  exact closedCell_subset_skeletonLT n j ⟨y, mem_closedBall_zero_iff.2 hy, rfl⟩

end TauCeti
