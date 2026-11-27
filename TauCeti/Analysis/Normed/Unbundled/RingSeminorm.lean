/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Unbundled.RingSeminorm
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Additional lemmas on ring seminorms

This file extends `Mathlib.Analysis.Normed.Unbundled.RingSeminorm` with general estimates for
`RingSeminorm` and ring seminorms on pairs of algebras.

A multiplicative cross-norm identity for two algebra maps transfers scalar homogeneity
from the source seminorm to the target. A contractive algebra map also forces both
seminorms to be at most one on the unit. These facts let cross-norm constructions avoid
assuming target homogeneity and unit bounds separately.

## Main results

* `RingSeminorm.map_add_pow_le_of_forall_map_pow_le`: geometric upper bounds on `μ (x ^ k)` and
  `μ (y ^ k)` yield a geometric upper bound on `μ ((x + y) ^ n)`.
* `RingSeminorm.apply_one_le_one_of_pair`: a contractive algebra map and a multiplicative
  cross-norm identity force both seminorms to be at most one on the unit.
* `RingSeminorm.smul_eq_of_pair`: homogeneity transfers along a multiplicative cross-norm
  identity when the source seminorm is homogeneous and at most one on the unit.
-/

public section

namespace RingSeminorm

section CommRing

variable {R : Type*} [CommRing R]

/-- Binomial power bound: geometric upper bounds on `μ (x ^ k)` and `μ (y ^ k)` yield a
geometric upper bound on `μ ((x + y) ^ n)`. -/
theorem map_add_pow_le_of_forall_map_pow_le (μ : RingSeminorm R) {x y : R} {Cx Cy a b : ℝ}
    (hCx : ∀ k, μ (x ^ k) ≤ Cx * a ^ k) (hCy : ∀ k, μ (y ^ k) ≤ Cy * b ^ k) (n : ℕ) :
    μ ((x + y) ^ n) ≤ Cx * Cy * (a + b) ^ n := by
  calc μ ((x + y) ^ n)
      = μ (∑ k ∈ Finset.range (n + 1), x ^ k * y ^ (n - k) * n.choose k) := by rw [add_pow]
    _ ≤ ∑ k ∈ Finset.range (n + 1), μ (x ^ k * y ^ (n - k) * n.choose k) :=
        Finset.map_sum_le_sum μ (Finset.range (n + 1)) _
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * (μ (x ^ k) * μ (y ^ (n - k))) := by
        gcongr with k
        have hchoose : μ (x ^ k * y ^ (n - k) * n.choose k) ≤
            (n.choose k : ℝ) * μ (x ^ k * y ^ (n - k)) := by
          simpa only [Finset.sum_const, Finset.card_range, ← nsmul_eq_mul', nsmul_eq_mul] using
            Finset.map_sum_le_sum μ (Finset.range (n.choose k)) (fun _ ↦ x ^ k * y ^ (n - k))
        exact hchoose.trans
          (mul_le_mul_of_nonneg_left (map_mul_le_mul μ _ _) (Nat.cast_nonneg _))
    _ ≤ ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * ((Cx * a ^ k) * (Cy * b ^ (n - k))) :=
        Finset.sum_le_sum fun k _ ↦ mul_le_mul_of_nonneg_left
          (mul_le_mul (hCx k) (hCy (n - k)) (apply_nonneg μ _) ((apply_nonneg μ _).trans (hCx k)))
          (Nat.cast_nonneg _)
    _ = Cx * Cy * ∑ k ∈ Finset.range (n + 1), a ^ k * b ^ (n - k) * n.choose k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        ring
    _ = Cx * Cy * (a + b) ^ n := by rw [← add_pow]

end CommRing

section Pair

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

end Pair

end RingSeminorm
