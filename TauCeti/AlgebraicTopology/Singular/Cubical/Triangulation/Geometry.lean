/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.Fin
public import TauCeti.Geometry.Convex.ConvexSpace.AffineMap
public import Mathlib.Geometry.Convex.ConvexSpace.ModuleTopology
public import Mathlib.Geometry.Convex.ConvexSpace.PathConnectedSpaceStdSimplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.Basic
public import TauCeti.Geometry.Convex.ConvexSpace.Topology
import Mathlib.Tactic

/-!
# Ordered simplices in the cube

The vertices follow the coordinate ordering specified by a permutation, from the all-zero
vertex to the all-one vertex. Faces common to two consecutive coordinate orderings agree as
actual affine simplex maps.

## Main definitions and results

* `Equiv.Perm.staircaseSimplex`: the actual ordered simplex in the coordinate cube.
* `Equiv.Perm.staircaseSimplex_mul_swap_face`: adjacent orderings share their internal face.
* `Equiv.Perm.staircaseSimplex_decompose_upper` and
  `Equiv.Perm.staircaseSimplex_snocFin_lower`: the exterior simplex faces are coordinate faces.
* `Equiv.Perm.staircaseSimplex_coordinatePermutation`: reindexing coordinates reindexes the order.
-/

public section

noncomputable section

open Equiv Convexity

namespace Equiv.Perm

/-- The staircase vertex after the first `k` coordinates in the order `π` have changed to
  one. -/
def staircaseVertex {n : ℕ} (π : Perm (Fin n)) (k : Fin (n + 1)) (j : Fin n) : ℝ :=
  if (π.symm j : ℕ) < (k : ℕ) then 1 else 0

/-- A staircase coordinate is one exactly after its step in the ordering. -/
@[simp]
lemma staircaseVertex_apply {n : ℕ} (π : Perm (Fin n)) (k : Fin (n + 1)) (j : Fin n) :
    staircaseVertex π k j = if (π.symm j : ℕ) < (k : ℕ) then 1 else 0 := by
  rfl

/-- The initial staircase vertex is zero. -/
@[simp]
lemma staircaseVertex_zero {n : ℕ} (π : Perm (Fin n)) : staircaseVertex π 0 = 0 := by
  ext j
  simp [staircaseVertex]

/-- The final staircase vertex is one in every coordinate. -/
@[simp]
lemma staircaseVertex_last {n : ℕ} (π : Perm (Fin n)) : staircaseVertex π (Fin.last n) = 1 := by
  ext j
  simp [staircaseVertex]

/-- Each coordinate of a staircase vertex lies in the closed unit interval. -/
lemma staircaseVertex_mem_Icc {n : ℕ} (π : Perm (Fin n)) (k : Fin (n + 1)) (j : Fin n) :
    staircaseVertex π k j ∈ Set.Icc (0 : ℝ) 1 := by
  simp only [staircaseVertex]
  split_ifs <;> simp

/-- Swapping adjacent steps changes only their intermediate vertex. -/
lemma staircaseVertex_mul_swap {n : ℕ} (π : Perm (Fin (n + 1))) (k : Fin n)
    {t : Fin (n + 2)} (ht : (t : ℕ) ≠ (k : ℕ) + 1) :
    staircaseVertex (π * swap k.castSucc k.succ) t = staircaseVertex π t := by
  ext j
  obtain ⟨i, rfl⟩ := π.surjective j
  have hi : (π * swap k.castSucc k.succ).symm (π i) = swap k.castSucc k.succ i := by
    apply (π * swap k.castSucc k.succ).injective
    simp [Perm.mul_apply]
  simp only [staircaseVertex, hi, Equiv.symm_apply_apply]
  rcases eq_or_ne i k.castSucc with rfl | h₁
  · rw [swap_apply_left]
    simp only [Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> first | rfl | omega
  rcases eq_or_ne i k.succ with rfl | h₂
  · rw [swap_apply_right]
    simp only [Fin.val_succ, Fin.val_castSucc]
    split_ifs <;> first | rfl | omega
  · rw [swap_apply_of_ne_of_ne h₁ h₂]

/-- The affine map from a simplex with the staircase vertices. -/
def affineStaircaseSimplex {n : ℕ} (π : Perm (Fin n)) :
    ConvexSpace.AffineMap ℝ (StdSimplex ℝ (Fin (n + 1))) (Fin n → ℝ) :=
  StdSimplex.affineMapMk (staircaseVertex π)

/-- The affine staircase simplex takes each simplex vertex to its prescribed cube vertex. -/
@[simp]
lemma affineStaircaseSimplex_single {n : ℕ} (π : Perm (Fin n)) (k : Fin (n + 1)) :
    affineStaircaseSimplex π (.single k) = staircaseVertex π k := by
  simp [affineStaircaseSimplex]

/-- The affine staircase simplex takes values in the coordinate cube. -/
lemma affineStaircaseSimplex_mem {n : ℕ} (π : Perm (Fin n))
    (w : StdSimplex ℝ (Fin (n + 1))) (j : Fin n) :
    affineStaircaseSimplex π w j ∈ Set.Icc (0 : ℝ) 1 := by
  rw [affineStaircaseSimplex, StdSimplex.affineMapMk_apply_eq_sum_of_fintype]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · exact Finset.sum_nonneg fun k _ ↦ mul_nonneg (w.nonneg k) (staircaseVertex_mem_Icc π k j).1
  · calc
      ∑ k, w.weights k * staircaseVertex π k j ≤ ∑ k, w.weights k * 1 :=
        Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left (staircaseVertex_mem_Icc π k j).2
          (w.nonneg k)
      _ = 1 := by simp

/-- The ordered affine simplex as a continuous map into the original cubical carrier. -/
def staircaseSimplex {n : ℕ} (π : Perm (Fin n)) :
    C(StdSimplex ℝ (Fin (n + 1)), Fin n → unitInterval) where
  toFun w j := ⟨affineStaircaseSimplex π w j, affineStaircaseSimplex_mem π w j⟩
  continuous_toFun := by
    apply continuous_pi
    intro j
    exact ((continuous_apply j : Continuous (fun z : Fin n → ℝ ↦ z j)).comp
      (StdSimplex.continuous_of_affineMap (affineStaircaseSimplex π))).subtype_mk _

/-- The real coordinate of the cube-valued simplex is its affine coordinate. -/
@[simp]
lemma staircaseSimplex_coe_apply {n : ℕ} (π : Perm (Fin n))
    (w : StdSimplex ℝ (Fin (n + 1))) (j : Fin n) :
    (staircaseSimplex π w j : ℝ) = affineStaircaseSimplex π w j := by
  rfl

/-- Composing an affine simplex with a simplex vertex map changes its vertex
  tuple. -/
lemma affineStaircaseSimplex_map {n m : ℕ} (π : Perm (Fin n)) (f : Fin (m + 1) → Fin (n + 1))
    (w : StdSimplex ℝ (Fin (m + 1))) :
    affineStaircaseSimplex π (w.map f) = StdSimplex.affineMapMk (staircaseVertex π ∘ f) w := by
  have h : (affineStaircaseSimplex π).comp (StdSimplex.affineMap f) =
      StdSimplex.affineMapMk (staircaseVertex π ∘ f) := by
    apply StdSimplex.affineMap_ext
    intro k
    simp [affineStaircaseSimplex]
  exact DFunLike.congr_fun h w

/-- Simplex maps with identical vertex tuples are equal as actual cube-valued maps. -/
lemma staircaseSimplex_map_eq {n m : ℕ} (π ρ : Perm (Fin n))
    (f : Fin (m + 1) → Fin (n + 1)) (h : staircaseVertex π ∘ f = staircaseVertex ρ ∘ f)
    (w : StdSimplex ℝ (Fin (m + 1))) :
    staircaseSimplex π (w.map f) = staircaseSimplex ρ (w.map f) := by
  funext j
  apply Subtype.ext
  simp only [staircaseSimplex_coe_apply]
  rw [affineStaircaseSimplex_map, affineStaircaseSimplex_map, h]

/-- The internal face shared by two consecutive coordinate orderings is literally equal. -/
lemma staircaseSimplex_mul_swap_face {n : ℕ} (π : Perm (Fin (n + 1))) (k : Fin n)
    (w : StdSimplex ℝ (Fin (n + 1))) :
    staircaseSimplex (π * swap k.castSucc k.succ) (w.map k.succ.castSucc.succAbove) =
      staircaseSimplex π (w.map k.succ.castSucc.succAbove) := by
  apply staircaseSimplex_map_eq
  funext t
  exact staircaseVertex_mul_swap π k (by
    have h := Fin.succAbove_ne k.succ.castSucc t
    intro e
    apply h
    exact Fin.ext e)

/-- After the first step, deleting its coordinate gives the smaller ordered simplex. -/
lemma staircaseVertex_decompose_succ {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n))
    (k : Fin (n + 1)) :
    staircaseVertex (consFin j π) k.succ = j.insertNth 1 (staircaseVertex π k) := by
  ext i
  refine Fin.succAboveCases j ?_ ?_ i
  · simp [staircaseVertex]
  · intro t
    obtain ⟨u, rfl⟩ := π.surjective t
    simp [staircaseVertex, consFin_symm_succAbove]

/-- The zeroth simplex face lies in the upper coordinate face chosen by the first step. -/
lemma staircaseSimplex_decompose_upper {n : ℕ} (j : Fin (n + 1)) (π : Perm (Fin n))
    (w : StdSimplex ℝ (Fin (n + 1))) :
    staircaseSimplex (consFin j π) (w.map Fin.succ) =
      j.insertNth 1 (staircaseSimplex π w) := by
  have h : StdSimplex.affineMapMk (staircaseVertex (consFin j π) ∘ Fin.succ) =
      (ConvexSpace.AffineMap.finInsertNth j 1).comp (affineStaircaseSimplex π) := by
    apply StdSimplex.affineMap_ext
    intro k
    simp [affineStaircaseSimplex, ConvexSpace.AffineMap.finInsertNth_apply,
      staircaseVertex_decompose_succ]
  funext i
  refine Fin.succAboveCases j ?_ ?_ i
  · apply Subtype.ext
    simp only [Fin.insertNth_apply_same]
    rw [staircaseSimplex_coe_apply]
    rw [affineStaircaseSimplex_map, h]
    simp [ConvexSpace.AffineMap.finInsertNth_apply]
  · intro k
    apply Subtype.ext
    simp only [Fin.insertNth_apply_succAbove]
    simp only [staircaseSimplex_coe_apply]
    rw [affineStaircaseSimplex_map, h]
    simp [ConvexSpace.AffineMap.finInsertNth_apply]

/-- Before the last step the distinguished coordinate remains zero. -/
lemma staircaseVertex_snocFin_castSucc {n : ℕ} (j : Fin (n + 1))
    (π : Perm (Fin n)) (k : Fin (n + 1)) :
    staircaseVertex (snocFin j π) k.castSucc = j.insertNth 0 (staircaseVertex π k) := by
  ext i
  refine Fin.succAboveCases j ?_ ?_ i
  · simp only [staircaseVertex, snocFin_symm_self, Fin.val_last, Fin.val_castSucc,
      Fin.insertNth_apply_same]
    rw [ite_eq_right (by omega)]
  · intro t
    obtain ⟨u, rfl⟩ := π.surjective t
    simp [staircaseVertex]

/-- The last simplex face lies in the lower coordinate face chosen by its last step. -/
lemma staircaseSimplex_snocFin_lower {n : ℕ} (j : Fin (n + 1))
    (π : Perm (Fin n)) (w : StdSimplex ℝ (Fin (n + 1))) :
    staircaseSimplex (snocFin j π) (w.map Fin.castSucc) =
      j.insertNth 0 (staircaseSimplex π w) := by
  have h : StdSimplex.affineMapMk (staircaseVertex (snocFin j π) ∘ Fin.castSucc) =
      (ConvexSpace.AffineMap.finInsertNth j 0).comp (affineStaircaseSimplex π) := by
    apply StdSimplex.affineMap_ext
    intro k
    simp [affineStaircaseSimplex, ConvexSpace.AffineMap.finInsertNth_apply,
      staircaseVertex_snocFin_castSucc]
  funext i
  refine Fin.succAboveCases j ?_ ?_ i
  · apply Subtype.ext
    simp only [Fin.insertNth_apply_same]
    rw [staircaseSimplex_coe_apply]
    rw [affineStaircaseSimplex_map, h]
    simp [ConvexSpace.AffineMap.finInsertNth_apply]
  · intro k
    apply Subtype.ext
    simp only [Fin.insertNth_apply_succAbove]
    simp only [staircaseSimplex_coe_apply]
    rw [affineStaircaseSimplex_map, h]
    simp [ConvexSpace.AffineMap.finInsertNth_apply]

/-- A coordinate permutation reindexes the staircase order by inverse left multiplication. -/
lemma staircaseVertex_coordinatePermutation {n : ℕ} (π τ : Perm (Fin n)) (k : Fin (n + 1)) :
    staircaseVertex (τ.symm * π) k = staircaseVertex π k ∘ τ := by
  ext j
  have h : (τ.symm * π).symm j = π.symm (τ j) := by
    apply (τ.symm * π).injective
    simp [Perm.mul_apply]
  simp [staircaseVertex, h]

/-- The corresponding coordinate permutation identity holds on the actual cube simplex. -/
lemma staircaseSimplex_coordinatePermutation {n : ℕ} (π τ : Perm (Fin n))
    (w : StdSimplex ℝ (Fin (n + 1))) :
    staircaseSimplex (τ.symm * π) w = staircaseSimplex π w ∘ τ := by
  have h : affineStaircaseSimplex (τ.symm * π) = (ConvexSpace.AffineMap.piPrecomp τ).comp
    (affineStaircaseSimplex
    π) := by
    apply StdSimplex.affineMap_ext
    intro k
    simpa only [ConvexSpace.AffineMap.coe_comp, Function.comp_apply,
      affineStaircaseSimplex_single, ConvexSpace.AffineMap.piPrecomp_apply,
      Function.comp_def] using staircaseVertex_coordinatePermutation π τ k
  funext j
  apply Subtype.ext
  simp only [Function.comp_apply, staircaseSimplex_coe_apply]
  simpa only [ConvexSpace.AffineMap.coe_comp, Function.comp_apply,
    ConvexSpace.AffineMap.piPrecomp_apply] using
      congrArg (fun z : Fin n → ℝ ↦ z j) (DFunLike.congr_fun h w)

/-- Coordinate permutation followed by an ordered simplex changes its permutation index. -/
lemma precomp_comp_staircaseSimplex {n : ℕ} (π τ : Perm (Fin n)) :
    ((ContinuousMap.precomp (X := fun _ ↦ unitInterval) ⇑τ)).comp (staircaseSimplex π) =
      staircaseSimplex (τ.symm * π) := by
  apply ContinuousMap.ext
  intro w
  exact (staircaseSimplex_coordinatePermutation π τ w).symm

/-- The unique interval staircase simplex is the native simplex-to-interval parameter. -/
lemma staircaseSimplex_one (w : StdSimplex ℝ (Fin 2)) :
    staircaseSimplex (1 : Perm (Fin 1)) w = fun _ ↦ StdSimplex.homeomorphI w := by
  funext j
  obtain rfl : j = 0 := Fin.eq_zero _
  apply Subtype.ext
  rw [staircaseSimplex_coe_apply]
  simp [affineStaircaseSimplex, StdSimplex.affineMapMk_apply_eq_sum_of_fintype,
    Fin.sum_univ_two, staircaseVertex, StdSimplex.homeomorphI_apply_coe]


end Equiv.Perm
