/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.Pi
import Mathlib.Data.Matrix.Basis

/-!
# Postcomposed matrix traces and cyclic functionals

Cyclicity, positivity, column quadratic-form expansion, cyclic factorization, and rank-one identity
for `rePart.comp (Matrix.traceLinearMap n R D)`. Over `ℍ[ℝ]` with `QuaternionAlgebra.reₗ`, this is
the real-part trace (half the quaternionic reduced trace).
-/

public section

open scoped Matrix

namespace LinearMap

/-- `rePart.comp (Matrix.traceLinearMap n R D)` is cyclic whenever `rePart` is cyclic on `D`. -/
theorem comp_traceLinearMap_cyclic {R D M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring D]
    [Module R D] [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n] {rePart : D →ₗ[R] M}
    (hre_cyc : ∀ a b : D, rePart (a * b) = rePart (b * a)) (X Y : Matrix n n D) :
    (rePart.comp (Matrix.traceLinearMap n R D)) (X * Y) =
      (rePart.comp (Matrix.traceLinearMap n R D)) (Y * X) := by
  simp only [comp_apply, Matrix.traceLinearMap_apply, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, map_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ hre_cyc _ _

/-- `(rePart.comp (Matrix.traceLinearMap n R D)) (X * star X) > 0` for every nonzero matrix `X`. -/
theorem comp_traceLinearMap_mul_star_pos {R D M : Type*} [CommSemiring R]
    [NonUnitalNonAssocSemiring D] [Module R D] [StarRing D] [AddCommMonoid M] [PartialOrder M]
    [IsOrderedCancelAddMonoid M] [Module R M] {n : Type*} [Fintype n] {rePart : D →ₗ[R] M}
    (hre_pos : ∀ a : D, a ≠ 0 → 0 < rePart (a * star a)) {X : Matrix n n D} (hX : X ≠ 0) :
    0 < (rePart.comp (Matrix.traceLinearMap n R D)) (X * star X) := by
  obtain ⟨i₀, j₀, hX₀⟩ : ∃ i j : n, X i j ≠ 0 := by
    by_contra h; push Not at h; exact hX (Matrix.ext h)
  have hnn i j : 0 ≤ rePart (X i j * star (X i j)) := by
    rcases eq_or_ne (X i j) 0 with h0 | hne <;> [simp [h0]; exact (hre_pos _ hne).le]
  simp only [comp_apply, Matrix.traceLinearMap_apply, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, map_sum]
  refine Finset.sum_pos' (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ hnn i j)
    ⟨i₀, Finset.mem_univ i₀, Finset.sum_pos' (fun j _ ↦ hnn i₀ j)
      ⟨j₀, Finset.mem_univ j₀, hre_pos _ hX₀⟩⟩

/-- Expansion of `(rePart.comp (Matrix.traceLinearMap n R D)) (S * X * star X)` as a sum of
column-wise quadratic forms `star v ⬝ᵥ (S *ᵥ v)`. -/
theorem comp_traceLinearMap_mul_mul_star_eq_sum {R D M : Type*} [CommSemiring R]
    [NonUnitalNonAssocSemiring D] [Module R D] [StarRing D] [AddCommMonoid M] [Module R M]
    {n : Type*} [Fintype n] {rePart : D →ₗ[R] M}
    (hre_cyc : ∀ a b : D, rePart (a * b) = rePart (b * a)) (S X : Matrix n n D) :
    (rePart.comp (Matrix.traceLinearMap n R D)) (S * X * star X) =
      ∑ m : n, rePart (star (fun j ↦ X j m) ⬝ᵥ (S *ᵥ fun j ↦ X j m)) := by
  simp only [comp_apply, Matrix.traceLinearMap_apply, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, Finset.sum_mul,
    map_sum, dotProduct, Matrix.mulVec, Finset.mul_sum, Pi.star_apply]
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦
    Finset.sum_congr rfl fun _ _ ↦ hre_cyc _ _

/-- Every cyclic `R`-linear map on `Matrix n n D` factors through `Matrix.trace` via a cyclic
`R`-linear map on `D`. -/
theorem exists_eq_comp_matrixTrace_of_cyclic {R D M : Type*} [CommSemiring R] [Semiring D]
    [Module R D] [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n]
    (t : Matrix n n D →ₗ[R] M) (hcyc : ∀ X Y : Matrix n n D, t (X * Y) = t (Y * X)) :
    ∃ τ : D →ₗ[R] M, (∀ a b : D, τ (a * b) = τ (b * a)) ∧
      ∀ X : Matrix n n D, t X = τ (Matrix.trace X) := by
  classical
  rcases isEmpty_or_nonempty n with _ | ⟨⟨i₀⟩⟩
  · exact ⟨0, fun _ _ ↦ rfl, fun X ↦ by simp [Subsingleton.elim X 0]⟩
  · let τ : D →ₗ[R] M := t.comp (Matrix.singleLinearMap R i₀ i₀)
    have hτ a : τ a = t (Matrix.single i₀ i₀ a) := by simp [τ, Matrix.singleLinearMap]
    refine ⟨τ, fun a b ↦ by
        simp_rw [hτ, ← Matrix.single_mul_single_same (i := i₀) (j := i₀) (k := i₀), hcyc],
      fun X ↦ ?_⟩
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum, Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Finset.sum_eq_single i (fun j _ hji ↦ by
        rw [show Matrix.single i j (X i j) =
          Matrix.single i j (X i j) * Matrix.single j j 1 by simp, hcyc]; simp [hji])
      (fun hi ↦ absurd (Finset.mem_univ i) hi),
      show Matrix.single i i (X i i) = Matrix.single i i₀ (X i i) * Matrix.single i₀ i 1 by simp,
      hcyc, Matrix.single_mul_single_same, one_mul, hτ]

/-- Rank-one trace identity: for `X = Matrix.vecMulVec v (star w)`,
`(rePart.comp (Matrix.traceLinearMap n R D)) (X * U * Xᴴ * V)` equals `rePart` applied to the
ordered product `(star v ⬝ᵥ (V *ᵥ v)) * (star w ⬝ᵥ (U *ᵥ w))`. -/
theorem comp_traceLinearMap_vecMulVec_mul_mul_conjTranspose_mul {R D M : Type*} [CommSemiring R]
    [NonUnitalSemiring D] [Module R D] [StarRing D] [AddCommMonoid M] [Module R M]
    {n : Type*} [Fintype n] {rePart : D →ₗ[R] M}
    (hre_cyc : ∀ a b : D, rePart (a * b) = rePart (b * a)) (U V : Matrix n n D) (v w : n → D) :
    (rePart.comp (Matrix.traceLinearMap n R D))
        (Matrix.vecMulVec v (star w) * U * (Matrix.vecMulVec v (star w))ᴴ * V) =
      rePart ((star v ⬝ᵥ (V *ᵥ v)) * (star w ⬝ᵥ (U *ᵥ w))) := by
  classical
  have hX : Matrix.vecMulVec v (star w) * U * (Matrix.vecMulVec v (star w))ᴴ * V =
      Matrix.vecMulVec v ((((star w) ᵥ* U) ⬝ᵥ w) • ((star v) ᵥ* V)) := by
    simp only [Matrix.conjTranspose_vecMulVec, star_star]
    rw [Matrix.vecMulVec_mul, Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul,
      Matrix.smul_vecMul]
  rw [comp_apply, Matrix.traceLinearMap_apply, hX, Matrix.trace_vecMulVec,
    show rePart (v ⬝ᵥ ((((star w) ᵥ* U) ⬝ᵥ w) • ((star v) ᵥ* V))) =
        rePart (((star v ᵥ* V) ⬝ᵥ v) * ((star w ᵥ* U) ⬝ᵥ w)) by
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, map_sum]
      rw [Finset.sum_congr rfl fun i _ ↦ by rw [hre_cyc, mul_assoc], ← map_sum, ← Finset.mul_sum,
        hre_cyc],
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec]

end LinearMap
