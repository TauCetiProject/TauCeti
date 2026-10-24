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
Characteristic-map lemmas describe their continuity on the closed unit ball (bundled as
`TauCeti.cellMap`), how open cells sit outside the lower skeleton, how their coordinates are
unique, and how cells account for points in consecutive skeleta, so that a map sends
`skeletonLT C (n + 1)` into a set exactly when it does so on `skeletonLT C n` and on the closed
`n`-cells (`TauCeti.mapsTo_skeletonLT_succ_iff`).  Every point of the complex lies in some
skeleton above any given level.  With a single `0`-cell, the `0`-skeleton is the base together
with that point (`TauCeti.skeletonLT_one_eq_insert`).

The mathematical source is Hatcher, *Algebraic Topology*, Section 2.2.
-/

public section

open Metric Set Topology Topology.RelCWComplex

universe w

namespace TauCeti

variable {X : Type w} [TopologicalSpace X]
  {D : Set X} {C : Set X} [RelCWComplex C D]

/-- The characteristic map of an `n`-cell is continuous on the closed unit ball, as a map out of
the subtype. -/
lemma continuous_map_closedBall {n : ℕ} (j : cell C n) :
    Continuous fun y : closedBall (0 : Fin n → ℝ) 1 ↦ map n j y :=
  (continuousOn n j).comp_continuous continuous_subtype_val fun y ↦ y.2

/-- The characteristic map of an `n`-cell, as a continuous map from the closed unit ball of
`Fin n → ℝ` into the complex. -/
def cellMap {n : ℕ} (j : cell C n) : C(closedBall (0 : Fin n → ℝ) 1, C) :=
  ⟨fun y ↦ ⟨map n j y, closedCell_subset_complex n j ⟨y, y.2, rfl⟩⟩,
    (continuous_map_closedBall j).subtype_mk _⟩

/-- The value of `TauCeti.cellMap` as a point of the complex. -/
lemma cellMap_apply {n : ℕ} (j : cell C n) (y : closedBall (0 : Fin n → ℝ) 1) :
    cellMap j y = ⟨map n j y, closedCell_subset_complex n j ⟨y, y.2, rfl⟩⟩ :=
  (rfl)

/-- The value of `TauCeti.cellMap` in the ambient space is the characteristic map. -/
@[simp]
lemma coe_cellMap_apply {n : ℕ} (j : cell C n) (y : closedBall (0 : Fin n → ℝ) 1) :
    (cellMap j y : X) = map n j y :=
  (rfl)

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

variable [T2Space X] (C)

/-- The `n`-th stage of the skeletal filtration, as an object of `TopCat`. -/
abbrev skeletonObj (n : ℕ) : TopCat.{w} := TopCat.of (skeletonLT C (n : ℕ∞) : Set X)

/-- If there are no cells of dimension at least `n`, the stage `skeletonLT C n` is the
whole relative CW complex, including its base. -/
lemma skeletonLT_eq_complex_of_isEmpty_cell (n : ℕ)
    (hn : ∀ m, n ≤ m → IsEmpty (cell C m)) :
    (skeletonLT C (n : ℕ∞) : Set X) = C := by
  refine Set.Subset.antisymm (skeletonLT C _).subset_complex ?_
  conv_lhs => rw [← union_iUnion_openCell_eq_complex (C := C)]
  refine Set.union_subset (skeletonLT C _).base_subset ?_
  refine Set.iUnion_subset fun m ↦ Set.iUnion_subset fun j ↦ ?_
  have hm : m < n := by
    by_contra h
    exact (hn m (Nat.le_of_not_gt h)).false j
  exact (openCell_subset_skeletonLT m j).trans
    (skeletonLT_mono (by exact_mod_cast hm))

/-- If there are no cells of dimension less than `n`, the stage `skeletonLT C n` is the base. -/
lemma skeletonLT_eq_base_of_isEmpty_cell (n : ℕ) (hn : ∀ m < n, IsEmpty (cell C m)) :
    (skeletonLT C (n : ℕ∞) : Set X) = D := by
  rw [← iUnion_openCell_eq_skeletonLT, union_eq_left]
  refine iUnion₂_subset fun m hm ↦ ?_
  have := hn m (by exact_mod_cast hm)
  simp

/-- If there is a single `0`-cell, the stage `skeletonLT C 1` is the base together with the point
of that cell. -/
lemma skeletonLT_one_eq_insert [Unique (cell C 0)] :
    (skeletonLT C 1 : Set X) = insert (map (C := C) 0 default 0) D := by
  rw [← iUnion_openCell_eq_skeletonLT, insert_eq, union_comm]
  congr 1
  ext y
  simp [openCell_zero_eq_singleton, Unique.exists_iff, eq_comm]

variable {C}

/-- The characteristic map of an `n`-cell sends the open unit ball into its open cell, which is
disjoint from `skeletonLT C n`. -/
lemma map_notMem_skeletonLT {n : ℕ} (j : cell C n) {y : Fin n → ℝ} (hy : ‖y‖ < 1) :
    map n j y ∉ (skeletonLT C (n : ℕ∞) : Set X) := fun h ↦
  (disjoint_skeletonLT_openCell le_rfl).notMem_of_mem_left h ⟨y, mem_ball_zero_iff.2 hy, rfl⟩

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

/-- A map out of a relative CW complex sends `skeletonLT C (n + 1)` into a set `T` exactly when
it sends `skeletonLT C n` into `T` and sends every closed `n`-cell, read through its
characteristic map, into `T`. -/
lemma mapsTo_skeletonLT_succ_iff {Y : Type*} {n : ℕ} {g : C → Y} {T : Set Y} :
    MapsTo g {x : C | (x : X) ∈ skeletonLT C ((n + 1 : ℕ) : ℕ∞)} T ↔
      MapsTo g {x : C | (x : X) ∈ skeletonLT C n} T ∧ ∀ (j : cell C n) y, g (cellMap j y) ∈ T := by
  refine ⟨fun h ↦ ⟨h.mono_left fun x hx ↦ skeletonLT_mono (by exact_mod_cast n.le_succ) hx,
    fun j y ↦ h (map_mem_skeletonLT_succ j (mem_closedBall_zero_iff.1 y.2))⟩,
    fun ⟨h, hcell⟩ x hx ↦ ?_⟩
  obtain hx' | ⟨j, y, hy, hxy⟩ := mem_skeletonLT_or_exists_map (x := (x : X)) hx
  · exact h hx'
  · convert hcell j ⟨y, mem_closedBall_zero_iff.2 hy.le⟩
    exact Subtype.ext hxy.symm

/-- Every point of a relative CW complex lies in some skeleton above any given level. -/
lemma exists_mem_skeletonLT_add (k : ℕ) {x : X} (hx : x ∈ C) :
    ∃ j : ℕ, x ∈ (skeletonLT C ((k + j : ℕ) : ℕ∞) : Set X) := by
  rw [← iUnion_skeletonLT_eq_complex (C := C), mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  exact ⟨j, skeletonLT_mono (by exact_mod_cast Nat.le_add_left j k) hj⟩

end TauCeti
