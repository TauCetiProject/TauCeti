/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
import TauCeti.LinearAlgebra.Matrix.ConjTranspose
import TauCeti.LinearAlgebra.Matrix.Trace.Comp

/-!
# Trace of a Hermitian square

The trace of the square of a Hermitian complex matrix is the sum of its squared entry norms. The
trace of the product of a Hermitian and a skew-Hermitian matrix is purely imaginary
(`Matrix.IsHermitian.re_trace_mul_eq_zero_of_conjTranspose_eq_neg`). Over a commutative ring with
trivial star and torsion-free addition, `(X * A * Xᴴ * B).trace` vanishes on symmetric rank-one
matrices `X = vecMulVec v v` whenever `Aᴴ = -A`, so it cannot be everywhere positive on nonzero `X`
(`Matrix.not_forall_trace_mul_mul_conjTranspose_mul_pos_of_conjTranspose_eq_neg`).
-/

public section

namespace Matrix

/-- The trace of the square of a Hermitian complex matrix is its entrywise squared norm sum. -/
theorem IsHermitian.trace_mul_self_eq_sum_norm_sq {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (A * A).trace = ((∑ i, ∑ j, ‖A i j‖ ^ 2 : ℝ) : ℂ) := by
  classical
  simp only [trace, diag_apply, Matrix.mul_apply, Complex.ofReal_sum, Complex.ofReal_pow]
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  rw [← hA.apply j i, Complex.star_def, Complex.mul_conj']

/-- The trace `tr(H X)` of the product of a Hermitian matrix `H` and a skew-Hermitian matrix `X`
is purely imaginary. -/
theorem IsHermitian.re_trace_mul_eq_zero_of_conjTranspose_eq_neg {𝕜 ι : Type*} [RCLike 𝕜]
    [Fintype ι] {H X : Matrix ι ι 𝕜} (hH : H.IsHermitian) (hX : Xᴴ = -X) :
    RCLike.re (H * X).trace = 0 := by
  have h : star (H * X).trace = -(H * X).trace := by
    simp [← trace_conjTranspose, hH.eq, hX, trace_mul_comm X]
  have := congrArg RCLike.re h
  simp only [RCLike.star_def, RCLike.conj_re, map_neg] at this
  linarith

/-- For a skew-Hermitian matrix `Aᴴ = -A` over a commutative ring with trivial star and
torsion-free addition, and any matrix `B` and vector `v`,
`(vecMulVec v v * A * (vecMulVec v v)ᴴ * B).trace = 0`. -/
theorem trace_vecMulVec_mul_mul_conjTranspose_mul_eq_zero_of_conjTranspose_eq_neg
    {n R : Type*} [Fintype n] [CommRing R] [StarRing R] [TrivialStar R] [IsAddTorsionFree R]
    {A : Matrix n n R} (hA : Aᴴ = -A) (B : Matrix n n R) (v : n → R) :
    (vecMulVec v v * A * (vecMulVec v v)ᴴ * B).trace = 0 := by
  have h := LinearMap.comp_traceLinearMap_vecMulVec_mul_mul_conjTranspose_mul
    (rePart := (LinearMap.id : R →ₗ[R] R)) mul_comm A B v v
  simp only [star_trivial, LinearMap.id_comp, Matrix.traceLinearMap_apply] at h
  rw [h, dotProduct_mulVec_self_eq_zero_of_skewHermitian hA v, mul_zero, LinearMap.id_apply]

/-- For a skew-Hermitian matrix `Aᴴ = -A` on a nonempty finite index type over a nontrivial
commutative ring with trivial star and torsion-free addition, and any matrix `B`, there exists a
nonzero matrix `X` with `(X * A * Xᴴ * B).trace = 0`. -/
theorem exists_ne_zero_trace_mul_mul_conjTranspose_mul_eq_zero_of_conjTranspose_eq_neg
    {n R : Type*} [Fintype n] [Nonempty n] [CommRing R] [Nontrivial R] [StarRing R]
    [TrivialStar R] [IsAddTorsionFree R] {A : Matrix n n R} (hA : Aᴴ = -A)
    (B : Matrix n n R) :
    ∃ X : Matrix n n R, X ≠ 0 ∧ (X * A * Xᴴ * B).trace = 0 := by
  let i₀ : n := Classical.arbitrary n
  let v : n → R := fun _ ↦ 1
  refine ⟨vecMulVec v v,
    fun h ↦ by simpa [v, vecMulVec_apply] using congrFun (congrFun h i₀) i₀,
    trace_vecMulVec_mul_mul_conjTranspose_mul_eq_zero_of_conjTranspose_eq_neg hA B v⟩

/-- For a skew-Hermitian matrix `Aᴴ = -A` on a nonempty finite index type over a nontrivial
preordered commutative ring with trivial star and torsion-free addition, and any matrix `B`,
`(X * A * Xᴴ * B).trace` cannot be strictly positive on all nonzero matrices `X`. -/
theorem not_forall_trace_mul_mul_conjTranspose_mul_pos_of_conjTranspose_eq_neg
    {n R : Type*} [Fintype n] [Nonempty n] [CommRing R] [Nontrivial R] [Preorder R]
    [StarRing R] [TrivialStar R] [IsAddTorsionFree R] {A : Matrix n n R} (hA : Aᴴ = -A)
    (B : Matrix n n R) :
    ¬ ∀ X : Matrix n n R, X ≠ 0 → 0 < (X * A * Xᴴ * B).trace := by
  intro h
  obtain ⟨X, hX, h0⟩ :=
    exists_ne_zero_trace_mul_mul_conjTranspose_mul_eq_zero_of_conjTranspose_eq_neg hA B
  have hpos := h X hX
  rw [h0] at hpos
  exact lt_irrefl 0 hpos

end Matrix
