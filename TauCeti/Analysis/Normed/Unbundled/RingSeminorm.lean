/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
public import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Ring seminorms on pairs of algebras

A multiplicative cross-norm identity for two algebra maps transfers scalar homogeneity
from the source seminorm to the target. A contractive algebra map also forces both
seminorms to be at most one on the unit. These facts let cross-norm constructions avoid
assuming target homogeneity and unit bounds separately.
-/

public section

namespace RingSeminorm

variable {C A B : Type*}

/-- A contractive algebra map and a multiplicative cross-norm identity force both
seminorms to be at most one on the unit. -/
theorem apply_one_le_one_of_pair [CommSemiring C] [Ring A] [Ring B]
    [Algebra C A] [Algebra C B] (N : RingSeminorm A) (M : RingSeminorm B)
    (D L R : A →ₐ[C] B) (hD : ∀ x, M (D x) ≤ N x)
    (hLR : ∀ x y, M (L x * R y) = N x * N y) : N 1 ≤ 1 ∧ M 1 ≤ 1 := by
  have h := hD 1
  have h' := hLR 1 1
  simp only [map_one, mul_one] at h h'
  have hN : N 1 ≤ 1 := by nlinarith [apply_nonneg N 1]
  exact ⟨hN, h.trans hN⟩

/-- Homogeneity transfers to the target seminorm along a multiplicative cross-norm
identity when the source seminorm is homogeneous and at most one on the unit. -/
theorem smul_eq_of_pair [NormedField C] [Ring A] [Ring B]
    [Algebra C A] [Algebra C B] (N : RingSeminorm A) (M : RingSeminorm B)
    (hNsmul : ∀ (c : C) x, N (c • x) = ‖c‖ * N x)
    (L R : A →ₐ[C] B) (hLR : ∀ x y, M (L x * R y) = N x * N y) (hN1 : N 1 ≤ 1)
    (c : C) (x : B) : M (c • x) = ‖c‖ * M x := by
  have hscalar (a : C) : M (algebraMap C B a) ≤ ‖a‖ := by
    have h := hLR (a • (1 : A)) 1
    simp only [map_smul, map_one, mul_one, hNsmul] at h
    rw [Algebra.algebraMap_eq_smul_one, h]
    calc
      ‖a‖ * N 1 * N 1 ≤ ‖a‖ * 1 * 1 := by gcongr
      _ = ‖a‖ := by ring
  have hle (a : C) (b : B) : M (a • b) ≤ ‖a‖ * M b := by
    rw [Algebra.smul_def]
    exact (map_mul_le_mul M _ _).trans
      (mul_le_mul_of_nonneg_right (hscalar a) (apply_nonneg M _))
  refine (hle c x).antisymm ?_
  by_cases hc : c = 0
  · simp [hc]
  have h := hle c⁻¹ (c • x)
  rw [inv_smul_smul₀ hc, norm_inv] at h
  have hmul := mul_le_mul_of_nonneg_left h (norm_nonneg c)
  rwa [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hc), one_mul] at hmul

end RingSeminorm
