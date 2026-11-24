/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
public import Mathlib.Topology.Instances.Matrix
public import TauCeti.Algebra.BigOperators.Finset.Pairs

/-!
# Strict upper coordinates for skew-adjoint matrices

A continuous real linear map extends the strict upper entries of a matrix with entries in a real
star module, such as a real or complex matrix, to a skew-adjoint matrix with zero diagonal by
reflecting them with negative star.
-/

public section

noncomputable section

namespace TauCeti

open Matrix

variable {n : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] [StarAddMonoid E] [StarModule ℝ E]
  [TopologicalSpace E] [ContinuousNeg E] [ContinuousStar E]

/-- Extend strict upper coordinates to a skew-adjoint matrix with zero diagonal. -/
def skewAdjointOfStrictUpper :
    (FinStrictUpper n → E) →L[ℝ] Matrix (Fin n) (Fin n) E where
  toFun x := Matrix.of fun i j ↦
    if hij : i < j then x ⟨(i, j), hij⟩ else if hji : j < i then -star (x ⟨(j, i), hji⟩) else 0
  map_add' x y := by
    ext i j
    simp only [Matrix.of_apply, Matrix.add_apply]
    split_ifs <;> simp [neg_add_rev, add_comm]
  map_smul' c x := by
    ext i j
    simp only [Matrix.of_apply, Matrix.smul_apply]
    split_ifs <;> simp
  cont := continuous_matrix fun i j ↦ by
    simp only [Matrix.of_apply]
    split_ifs
    · exact continuous_apply _
    · exact (continuous_apply _).star.neg
    · exact continuous_const

/-- The extension on a strict upper entry is the given coordinate. -/
@[simp] theorem skewAdjointOfStrictUpper_apply_of_lt (x : FinStrictUpper n → E) {i j : Fin n}
    (h : i < j) : skewAdjointOfStrictUpper x i j = x ⟨(i, j), h⟩ := by
  simp [skewAdjointOfStrictUpper, h]

/-- The extension on a strict lower entry is the negative conjugate reflected coordinate. -/
@[simp] theorem skewAdjointOfStrictUpper_apply_of_gt (x : FinStrictUpper n → E) {i j : Fin n}
    (h : j < i) : skewAdjointOfStrictUpper x i j = -star (x ⟨(j, i), h⟩) := by
  simp [skewAdjointOfStrictUpper, h, h.not_gt]

/-- The skew-adjoint extension has zero diagonal. -/
@[simp] theorem skewAdjointOfStrictUpper_apply_diag (x : FinStrictUpper n → E) (i : Fin n) :
    skewAdjointOfStrictUpper x i i = 0 := by
  simp [skewAdjointOfStrictUpper]

/-- The strict upper extension is skew-adjoint. -/
theorem skewAdjointOfStrictUpper_mem (x : FinStrictUpper n → E) :
    skewAdjointOfStrictUpper x ∈ skewAdjoint (Matrix (Fin n) (Fin n) E) := by
  rw [skewAdjoint.mem_iff]
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, star_apply]
  · simp [star_apply]
  · simp [h, star_apply]

end TauCeti
