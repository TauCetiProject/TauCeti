/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Basis

/-!
# Postcomposed matrix traces and cyclic functionals

Defines `LinearMap.compMatrixTrace` (`rePart.comp (Matrix.traceLinearMap n R D)`, i.e.
`X ↦ rePart (Matrix.trace X)`), distinct from the quaternionic reduced trace when
`rePart = QuaternionAlgebra.reₗ (-1) 0 (-1)` (which gives half the reduced trace), and establishes
its cyclicity, positivity, column quadratic-form expansion, cyclic factorization, and rank-one
identity (`LinearMap.compMatrixTrace_rankOne_mul_conj`, giving `rePart` applied to the ordered
product `(star v ⬝ᵥ (V *ᵥ v)) * (star w ⬝ᵥ (U *ᵥ w))`).
-/

public section

open scoped Matrix

namespace LinearMap

section

variable {R D M : Type*} [CommSemiring R] [AddCommMonoid D] [Module R D]
  [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n]

/-- The matrix trace `Matrix.traceLinearMap n R D` postcomposed with `rePart : D →ₗ[R] M`. Over
`ℍ[ℝ]` with `rePart = QuaternionAlgebra.reₗ ...` this is the real-part trace (half the reduced
trace), not the unnormalized reduced trace. -/
abbrev compMatrixTrace (rePart : D →ₗ[R] M) : Matrix n n D →ₗ[R] M :=
  rePart.comp (Matrix.traceLinearMap n R D)

@[simp] theorem compMatrixTrace_apply (rePart : D →ₗ[R] M) (X : Matrix n n D) :
    rePart.compMatrixTrace X = rePart (Matrix.trace X) := rfl

end

/-- `rePart.compMatrixTrace` is cyclic whenever `rePart` is cyclic on `D`. -/
theorem compMatrixTrace_cyclic {R D M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring D]
    [Module R D] [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n] {rePart : D →ₗ[R] M}
    (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a)) (X Y : Matrix n n D) :
    rePart.compMatrixTrace (X * Y) = rePart.compMatrixTrace (Y * X) := by
  simp only [compMatrixTrace_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ hre_cyclic _ _

/-- `rePart.compMatrixTrace (X * star X) > 0` for every nonzero matrix `X`. -/
theorem compMatrixTrace_pos {D : Type*} [NonUnitalNonAssocSemiring D] [Module ℝ D] [StarRing D]
    {n : Type*} [Fintype n] {rePart : D →ₗ[ℝ] ℝ}
    (hre_pos : ∀ a : D, a ≠ 0 → 0 < rePart (a * star a)) {X : Matrix n n D} (hX : X ≠ 0) :
    0 < rePart.compMatrixTrace (X * star X) := by
  obtain ⟨i₀, j₀, hX₀⟩ : ∃ i j : n, X i j ≠ 0 := by
    by_contra h; push Not at h; exact hX (Matrix.ext h)
  have hnn (i j : n) : 0 ≤ rePart (X i j * star (X i j)) := by
    rcases eq_or_ne (X i j) 0 with h0 | hne <;> [simp [h0]; exact (hre_pos _ hne).le]
  simp only [compMatrixTrace_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, map_sum]
  exact Finset.sum_pos' (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn i j)
    ⟨i₀, Finset.mem_univ i₀, Finset.sum_pos' (fun j _ ↦ hnn i₀ j)
      ⟨j₀, Finset.mem_univ j₀, hre_pos _ hX₀⟩⟩

/-- Expansion of `rePart.compMatrixTrace (S * X * star X)` as a sum of column-wise quadratic
forms `star v ⬝ᵥ (S *ᵥ v)`. -/
theorem compMatrixTrace_mul_mul_star_eq_sum {D : Type*} [Semiring D] [Module ℝ D] [StarRing D]
    {n : Type*} [Fintype n] {rePart : D →ₗ[ℝ] ℝ}
    (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a)) (S X : Matrix n n D) :
    rePart.compMatrixTrace (S * X * star X) =
      ∑ m : n, rePart (star (fun j ↦ X j m) ⬝ᵥ (S *ᵥ fun j ↦ X j m)) := by
  simp only [compMatrixTrace_apply, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Finset.sum_mul, map_sum,
    dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ ↦ Finset.sum_congr rfl fun j _ ↦
    Finset.sum_congr rfl fun k _ ↦ by rw [hre_cyclic (S j k * X k m) (star (X j m))]

/-- Every cyclic `R`-linear map on `Matrix n n D` factors through `Matrix.trace` via a cyclic
`R`-linear map on `D`. -/
theorem exists_eq_comp_matrixTrace_of_cyclic {R D M : Type*} [CommSemiring R] [Semiring D]
    [Module R D] [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n]
    (t : Matrix n n D →ₗ[R] M) (hcyclic : ∀ X Y : Matrix n n D, t (X * Y) = t (Y * X)) :
    ∃ τ : D →ₗ[R] M, (∀ a b : D, τ (a * b) = τ (b * a)) ∧
      ∀ X : Matrix n n D, t X = τ (Matrix.trace X) := by
  classical
  rcases isEmpty_or_nonempty n with hempty | ⟨⟨i₀⟩⟩
  · exact ⟨0, fun _ _ ↦ rfl, fun X ↦ by simp [Subsingleton.elim X 0]⟩
  · let τ : D →ₗ[R] M := t.comp (Matrix.singleLinearMap R i₀ i₀)
    have hτ_apply (a : D) : τ a = t (Matrix.single i₀ i₀ a) := by simp [τ, Matrix.singleLinearMap]
    have hsingle_ne {i j : n} (hij : i ≠ j) (a : D) : t (Matrix.single i j a) = 0 := by
      have h1 : Matrix.single i j a = Matrix.single i j a * Matrix.single j j (1 : D) := by
        rw [Matrix.single_mul_single_same, mul_one]
      rw [h1, hcyclic]; simp [hij.symm]
    have hsingle_diag (i : n) (a : D) : t (Matrix.single i i a) = τ a := by
      have h1 : Matrix.single i i a = Matrix.single i i₀ a * Matrix.single i₀ i (1 : D) := by
        rw [Matrix.single_mul_single_same, mul_one]
      have h2 : Matrix.single i₀ i (1 : D) * Matrix.single i i₀ a = Matrix.single i₀ i₀ a := by
        rw [Matrix.single_mul_single_same, one_mul]
      rw [h1, hcyclic, h2, hτ_apply]
    refine ⟨τ, fun a b ↦ ?_, fun X ↦ ?_⟩
    · have hmul (x y : D) : Matrix.single i₀ i₀ (x * y) =
          Matrix.single i₀ i₀ x * Matrix.single i₀ i₀ y := by rw [Matrix.single_mul_single_same]
      rw [hτ_apply, hτ_apply, hmul, hmul, hcyclic]
    · conv_lhs => rw [Matrix.matrix_eq_sum_single X]
      simp only [map_sum, Matrix.trace, Matrix.diag_apply]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.sum_eq_single i (fun j _ hji ↦ hsingle_ne hji.symm (X i j))
        (fun hi ↦ absurd (Finset.mem_univ i) hi), hsingle_diag]

/-- Rank-one trace identity: for `X = Matrix.vecMulVec v (star w)`,
`rePart.compMatrixTrace (X * U * Xᴴ * V)` equals `rePart` applied to the ordered product
`(star v ⬝ᵥ (V *ᵥ v)) * (star w ⬝ᵥ (U *ᵥ w))`. -/
theorem compMatrixTrace_rankOne_mul_conj {R D M : Type*} [CommSemiring R]
    [NonUnitalSemiring D] [Module R D] [StarRing D] [AddCommMonoid M] [Module R M]
    {n : Type*} [Fintype n] {rePart : D →ₗ[R] M}
    (hre_cyclic : ∀ a b : D, rePart (a * b) = rePart (b * a))
    (U V : Matrix n n D) (v w : n → D) :
    rePart.compMatrixTrace (Matrix.vecMulVec v (star w) * U * (Matrix.vecMulVec v (star w))ᴴ * V) =
      rePart ((star v ⬝ᵥ (V *ᵥ v)) * (star w ⬝ᵥ (U *ᵥ w))) := by
  classical
  have hX : Matrix.vecMulVec v (star w) * U * (Matrix.vecMulVec v (star w))ᴴ * V =
      Matrix.vecMulVec v ((((star w) ᵥ* U) ⬝ᵥ w) • ((star v) ᵥ* V)) := by
    rw [mul_assoc (Matrix.vecMulVec v (star w) * U), Matrix.conjTranspose_vecMulVec,
      show star (star w) = w from funext fun i ↦ star_star (w i),
      Matrix.vecMulVec_mul w (star v) V, Matrix.vecMulVec_mul v (star w) U,
      Matrix.vecMulVec_mul_vecMulVec]
  rw [compMatrixTrace_apply, hX, Matrix.trace_vecMulVec]
  have htr : rePart (v ⬝ᵥ ((((star w) ᵥ* U) ⬝ᵥ w) • ((star v) ᵥ* V))) =
      rePart (((star v ᵥ* V) ⬝ᵥ v) * ((star w ᵥ* U) ⬝ᵥ w)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, map_sum]
    rw [Finset.sum_congr rfl fun i _ ↦ by rw [hre_cyclic, mul_assoc], ← map_sum,
      ← Finset.mul_sum, hre_cyclic]
  rw [htr, ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec]

end LinearMap
