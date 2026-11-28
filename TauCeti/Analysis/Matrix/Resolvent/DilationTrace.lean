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
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Defs
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
theorem trace_toBlocks₁₁_inv_fromBlocks_zero_sub_smul_one_eq
    (A B : Matrix n n 𝕜) (w : 𝕜) :
    let R := (fromBlocks 0 A B 0 - w • 1)⁻¹
    R.toBlocks₁₁.trace = R.toBlocks₂₂.trace := by
  let H : Matrix (n ⊕ n) (n ⊕ n) (Polynomial 𝕜) :=
    fromBlocks 0 (A.map Polynomial.C) (B.map Polynomial.C) 0
  let S := H - (Polynomial.X : Polynomial 𝕜) • 1
  let C := S.adjugate
  -- The adjugate identities give equality after multiplying the traces by the indeterminate.
  have hl := congrArg (fun M : Matrix (n ⊕ n) (n ⊕ n) (Polynomial 𝕜) ↦ M.toBlocks₁₁.trace)
    (mul_adjugate S)
  have hr := congrArg (fun M : Matrix (n ⊕ n) (n ⊕ n) (Polynomial 𝕜) ↦ M.toBlocks₂₂.trace)
    (adjugate_mul S)
  change (S * C).toBlocks₁₁.trace = _ at hl
  change (C * S).toBlocks₂₂.trace = _ at hr
  simp only [S, sub_mul, smul_mul_assoc, Matrix.one_mul, H, toBlocks₁₁_sub, toBlocks₁₁_mul,
    toBlocks₁₁_smul, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₁₂, Matrix.zero_mul, zero_add,
    trace_sub, trace_smul, smul_eq_mul, toBlocks₁₁_one] at hl
  simp only [S, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, H, toBlocks₂₂_sub,
    toBlocks₂₂_mul, toBlocks₂₂_smul, toBlocks_fromBlocks₁₂, toBlocks_fromBlocks₂₂,
    Matrix.mul_zero, add_zero, trace_sub, trace_smul, smul_eq_mul, toBlocks₂₂_one] at hr
  rw [trace_mul_comm C.toBlocks₂₁ (A.map Polynomial.C)] at hr
  have hC : C.toBlocks₁₁.trace = C.toBlocks₂₂.trace :=
    Polynomial.isRegular_X.left (sub_right_inj.mp (hl.trans hr.symm))
  let e := Polynomial.evalRingHom w
  have hS : e.mapMatrix S = fromBlocks 0 A B 0 - w • 1 := by
    change (H - (Polynomial.X : Polynomial 𝕜) • 1).map e = _
    rw [Matrix.map_sub _ (map_sub _), Matrix.map_smul' _ _ _ (map_mul _),
      Matrix.map_one _ (map_zero _) (map_one _)]
    simp [H, fromBlocks_map, e, Function.comp_def]
  have h := congrArg e hC
  simp only [AddMonoidHom.map_trace, ← toBlocks₁₁_map, ← toBlocks₂₂_map] at h
  change (e.mapMatrix S.adjugate).toBlocks₁₁.trace = (e.mapMatrix S.adjugate).toBlocks₂₂.trace at h
  simp only [e.map_adjugate, hS] at h
  dsimp only
  rw [inv_def, toBlocks₁₁_smul, toBlocks₂₂_smul, trace_smul, trace_smul, h]

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
