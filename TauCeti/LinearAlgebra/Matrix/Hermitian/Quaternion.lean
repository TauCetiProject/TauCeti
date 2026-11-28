/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Quaternion
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Linarith
import TauCeti.Algebra.Quaternion.Basic
import TauCeti.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.LinearAlgebra.Matrix.Trace.Comp

/-!
# Skew-Hermitian quaternionic matrices

Establishes vanishing of the real part of the quadratic form `star v ⬝ᵥ (M *ᵥ v)` for
skew-Hermitian quaternionic matrices
(`Matrix.re_star_dotProduct_mulVec_self_eq_zero_of_skewHermitian`), and shows that for a
skew-Hermitian matrix `Aᴴ = -A` on a nonempty finite index type and any matrix `B`,
`(X * A * Xᴴ * B).trace.re` cannot remain strictly positive on all nonzero matrices `X`
(`Matrix.not_forall_re_trace_mul_mul_conjTranspose_mul_pos_of_skewHermitian`).
-/

public section

open scoped Matrix Quaternion

namespace Matrix

/-- The real part of the quadratic form of a skew-Hermitian quaternionic matrix vanishes. -/
theorem re_star_dotProduct_mulVec_self_eq_zero_of_skewHermitian {n : Type*} [Fintype n]
    {M : Matrix n n ℍ[ℝ]} (hM : Mᴴ = -M) (v : n → ℍ[ℝ]) :
    (star v ⬝ᵥ (M *ᵥ v)).re = 0 := by
  have hre := congrArg QuaternionAlgebra.re (star_dotProduct_mulVec_self_of_skewHermitian hM v)
  simp only [Quaternion.re_star, QuaternionAlgebra.re_neg] at hre
  linarith

/-- For a skew-Hermitian quaternionic matrix `Aᴴ = -A` on a nonempty finite index type and any
matrix `B`, there exists a nonzero matrix `X` with `(X * A * Xᴴ * B).trace.re ≤ 0`. -/
theorem exists_ne_zero_re_trace_mul_mul_conjTranspose_mul_le_zero_of_skewHermitian
    {n : Type*} [Fintype n] [Nonempty n] {A : Matrix n n ℍ[ℝ]} (hA : Aᴴ = -A)
    (B : Matrix n n ℍ[ℝ]) :
    ∃ X : Matrix n n ℍ[ℝ], X ≠ 0 ∧ (X * A * Xᴴ * B).trace.re ≤ 0 := by
  classical
  let i₀ : n := Classical.arbitrary n
  let v₀ : n → ℍ[ℝ] := fun _ ↦ 1
  set r : ℍ[ℝ] := star v₀ ⬝ᵥ (B *ᵥ v₀)
  set s : ℍ[ℝ] := star v₀ ⬝ᵥ (A *ᵥ v₀)
  by_cases h0 : (r * s).re ≤ 0
  · refine ⟨vecMulVec v₀ (star v₀),
      fun h ↦ by simpa [v₀, vecMulVec_apply] using congrFun (congrFun h i₀) i₀, ?_⟩
    have htr := LinearMap.comp_traceLinearMap_vecMulVec_mul_mul_conjTranspose_mul
      (rePart := QuaternionAlgebra.reₗ (-1) 0 (-1)) Quaternion.re_mul_comm A B v₀ v₀
    simp only [LinearMap.comp_apply, Matrix.traceLinearMap_apply,
      QuaternionAlgebra.reₗ_apply] at htr
    rwa [htr]
  · obtain ⟨q, hq0, _, hqconj⟩ := Quaternion.exists_pure_star_mul_mul_eq_neg_normSq_smul s
      (re_star_dotProduct_mulVec_self_eq_zero_of_skewHermitian hA v₀)
    let w₁ : n → ℍ[ℝ] := fun i ↦ v₀ i * q
    refine ⟨vecMulVec v₀ (star w₁), fun h ↦ hq0
      (by simpa [w₁, v₀, vecMulVec_apply] using congrFun (congrFun h i₀) i₀), ?_⟩
    have hw₁_quad : star w₁ ⬝ᵥ (A *ᵥ w₁) = star q * s * q := by
      simp only [dotProduct, mulVec, w₁, s, Pi.star_apply, star_mul, Finset.mul_sum,
        Finset.sum_mul, mul_assoc]
    have htr := LinearMap.comp_traceLinearMap_vecMulVec_mul_mul_conjTranspose_mul
      (rePart := QuaternionAlgebra.reₗ (-1) 0 (-1)) Quaternion.re_mul_comm A B v₀ w₁
    simp only [LinearMap.comp_apply, Matrix.traceLinearMap_apply,
      QuaternionAlgebra.reₗ_apply] at htr
    have hneg : (r * (-(Quaternion.normSq q • s))).re ≤ 0 := by
      simp only [mul_neg, QuaternionAlgebra.re_neg, mul_smul_comm, QuaternionAlgebra.re_smul,
        smul_eq_mul, neg_nonpos]
      exact mul_nonneg Quaternion.normSq_nonneg (lt_of_not_ge h0).le
    rwa [htr, show star v₀ ⬝ᵥ (B *ᵥ v₀) = r from rfl, hw₁_quad, hqconj]

/-- For a skew-Hermitian quaternionic matrix `Aᴴ = -A` on a nonempty finite index type and any
matrix `B`, `(X * A * Xᴴ * B).trace.re` cannot remain strictly positive on all nonzero matrices
`X`. -/
theorem not_forall_re_trace_mul_mul_conjTranspose_mul_pos_of_skewHermitian
    {n : Type*} [Fintype n] [Nonempty n] {A : Matrix n n ℍ[ℝ]} (hA : Aᴴ = -A)
    (B : Matrix n n ℍ[ℝ]) :
    ¬ ∀ X : Matrix n n ℍ[ℝ], X ≠ 0 → 0 < (X * A * Xᴴ * B).trace.re :=
  fun h ↦ let ⟨X, hX, hle⟩ :=
    exists_ne_zero_re_trace_mul_mul_conjTranspose_mul_le_zero_of_skewHermitian hA B
  not_lt.mpr hle (h X hX)

end Matrix
