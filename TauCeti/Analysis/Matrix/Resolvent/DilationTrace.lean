/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Matrix.Block

/-!
# Traces of off-diagonal block resolvents

The two diagonal blocks of the resolvent of an off-diagonal matrix have the same trace when
the two index sets agree. On the imaginary axis the trace of a Hermitian off-diagonal
resolvent is purely imaginary. These properties let the expected resolvent equation for
shifted Gaussian matrices use a single scalar trace.
-/

public section

open scoped ComplexConjugate

namespace Matrix

variable {n m 𝕜 : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m] [CommRing 𝕜]

private theorem inv_fromBlocks_zero_add_smul_one (A : Matrix n m 𝕜) (B : Matrix m n 𝕜) (w : 𝕜) :
    let J := fromBlocks (1 : Matrix n n 𝕜) 0 0 (-1 : Matrix m m 𝕜)
    let H := fromBlocks 0 A B 0
    (H + w • 1)⁻¹ = -(J * (H - w • 1)⁻¹ * J) := by
  intro J H
  have hJ : J * J = 1 := by simp [J, fromBlocks_multiply, fromBlocks_one]
  have hJinv : J⁻¹ = J := inv_eq_left_inv hJ
  have hH : J * H * J = -H := by
    simp [J, H, fromBlocks_multiply, fromBlocks_neg]
  have hS : J * (H - w • 1) * J = -(H + w • 1) := by
    rw [Matrix.mul_sub, sub_mul, hH, Matrix.mul_smul, Matrix.mul_one, smul_mul_assoc, hJ,
      neg_add_rev, sub_eq_add_neg, add_comm]
  have h := congrArg (fun M : Matrix (n ⊕ m) (n ⊕ m) 𝕜 ↦ M⁻¹) hS
  rw [mul_inv_rev, mul_inv_rev, hJinv, ← Matrix.mul_assoc] at h
  have hneg : (-1 : Matrix (n ⊕ m) (n ⊕ m) 𝕜)⁻¹ = -1 := inv_eq_left_inv (by simp)
  rw [← neg_one_mul (H + w • 1), mul_inv_rev, hneg, Matrix.mul_neg, Matrix.mul_one] at h
  simpa using congrArg Neg.neg h.symm

/-- The diagonal blocks of the resolvent of an off-diagonal matrix with square blocks
have equal traces. This includes singular shifts, where the nonsingular inverse is zero. -/
theorem trace_toBlocks₁₁_inv_fromBlocks_zero_sub_smul_one_eq [IsDomain 𝕜]
    (A B : Matrix n n 𝕜) (w : 𝕜) :
    let R := (fromBlocks 0 A B 0 - w • 1)⁻¹
    R.toBlocks₁₁.trace = R.toBlocks₂₂.trace := by
  intro R
  let H := fromBlocks 0 A B 0
  by_cases hw : w = 0
  · by_cases hdet : IsUnit H.det
    · have hR : R = H⁻¹ := by simp only [R, H, hw, zero_smul, sub_zero]
      have hmul : H * R = 1 := hR ▸ mul_nonsing_inv H hdet
      have hmul' : R * H = 1 := hR ▸ nonsing_inv_mul H hdet
      have h12 : A * R.toBlocks₂₂ = 0 := by
        simpa [H, toBlocks₁₂_mul, toBlocks₁₂_one] using congrArg toBlocks₁₂ hmul
      have h21 : B * R.toBlocks₁₁ = 0 := by
        simpa [H, toBlocks₂₁_mul, toBlocks₂₁_one] using congrArg toBlocks₂₁ hmul
      have ha : R.toBlocks₂₁ * A = 1 := by
        simpa [H, toBlocks₂₂_mul, toBlocks₂₂_one] using congrArg toBlocks₂₂ hmul'
      have hb : R.toBlocks₁₂ * B = 1 := by
        simpa [H, toBlocks₁₁_mul, toBlocks₁₁_one] using congrArg toBlocks₁₁ hmul'
      have h₁ : R.toBlocks₁₁ = 0 := by
        rw [← one_mul R.toBlocks₁₁, ← hb, Matrix.mul_assoc, h21, Matrix.mul_zero]
      have h₂ : R.toBlocks₂₂ = 0 := by
        rw [← one_mul R.toBlocks₂₂, ← ha, Matrix.mul_assoc, h12, Matrix.mul_zero]
      rw [h₁, h₂]
    · have hR : R = H⁻¹ := by simp only [R, H, hw, zero_smul, sub_zero]
      rw [hR, nonsing_inv_apply_not_isUnit H hdet]
      rfl
  by_cases hu : IsUnit (H - w • 1).det
  · have hl := congrArg (fun M : Matrix (n ⊕ n) (n ⊕ n) 𝕜 ↦ M.toBlocks₁₁.trace)
      (mul_nonsing_inv (H - w • 1) hu)
    have hr := congrArg (fun M : Matrix (n ⊕ n) (n ⊕ n) 𝕜 ↦ M.toBlocks₂₂.trace)
      (nonsing_inv_mul (H - w • 1) hu)
    have hR : (H - w • 1)⁻¹ = R := rfl
    rw [hR] at hl hr
    simp only [sub_mul, smul_mul_assoc, Matrix.one_mul, H, toBlocks₁₁_sub, toBlocks₁₁_mul,
      toBlocks₁₁_smul, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.zero_mul, zero_add,
      trace_sub, trace_smul, smul_eq_mul, toBlocks₁₁_one] at hl
    simp only [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, H, toBlocks₂₂_sub,
      toBlocks₂₂_mul, toBlocks₂₂_smul, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
      Matrix.mul_zero, add_zero, trace_sub, trace_smul, smul_eq_mul, toBlocks₂₂_one] at hr
    rw [trace_mul_comm R.toBlocks₂₁ A] at hr
    apply mul_left_cancel₀ hw
    linear_combination hr - hl
  · have hR : (H - w • 1)⁻¹ = R := rfl
    rw [← hR, nonsing_inv_apply_not_isUnit _ hu]
    rfl

open Complex in
/-- At a purely imaginary shift the trace of the Hermitian dilation resolvent is purely
imaginary. -/
theorem re_trace_inv_fromBlocks_zero_conjTranspose_sub_smul_one
    (A : Matrix n m ℂ) (η : ℝ) :
    ((fromBlocks 0 A Aᴴ 0 - ((η : ℂ) * I) • 1)⁻¹.trace).re = 0 := by
  let H := fromBlocks 0 A Aᴴ 0
  let w := (η : ℂ) * I
  let R := (H - w • 1)⁻¹
  let J := fromBlocks (1 : Matrix n n ℂ) 0 0 (-1 : Matrix m m ℂ)
  have hH : Hᴴ = H := (isHermitian_zero.fromBlocks rfl isHermitian_zero).eq
  have hw : conj w = -w := by simp [w]
  have hJ : J * J = 1 := by simp [J, fromBlocks_multiply, fromBlocks_one]
  have hR : Rᴴ = -(J * R * J) := by
    simp only [R, conjTranspose_nonsing_inv, conjTranspose_sub, conjTranspose_smul, hH,
      conjTranspose_one, ← starRingEnd_apply, hw, neg_smul, sub_neg_eq_add]
    exact inv_fromBlocks_zero_add_smul_one A Aᴴ w
  have h := congrArg (fun M : Matrix (n ⊕ m) (n ⊕ m) ℂ ↦ M.trace.re) hR
  rw [trace_conjTranspose, trace_neg, trace_mul_cycle, hJ, Matrix.one_mul] at h
  simp only [Complex.star_def, Complex.conj_re, Complex.neg_re] at h
  exact eq_zero_of_neg_eq h.symm

end Matrix
