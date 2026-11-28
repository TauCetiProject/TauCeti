/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Star.Pi
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Postcomposed matrix traces and cyclic functionals

Cyclicity, positivity, column quadratic-form expansion, cyclic factorization (existence,
uniqueness, single-entry recovery, and positivity), scalar-identity trace evaluation, and
rank-one identity for `rePart.comp (Matrix.traceLinearMap n R D)`. Over `ℍ[ℝ]` with
`QuaternionAlgebra.reₗ`, this is the real-part trace (half the quaternionic reduced trace).
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

/-- If `rePart (a * star a) > 0` for every nonzero `a : D`, then
`(rePart.comp (Matrix.traceLinearMap n R D)) (X * star X) > 0` for every nonzero matrix `X`. -/
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

/-- When `rePart` is cyclic (`∀ a b : D, rePart (a * b) = rePart (b * a)`),
`(rePart.comp (Matrix.traceLinearMap n R D)) (S * X * star X)` expands as a sum of column-wise
quadratic forms `star v ⬝ᵥ (S *ᵥ v)`. -/
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

/-- Every cyclic `R`-linear map on `Matrix n n D` factors through `Matrix.traceLinearMap n R D`
via a cyclic `R`-linear map on `D`. -/
theorem exists_eq_comp_traceLinearMap_of_cyclic {R D M : Type*} [CommSemiring R] [Semiring D]
    [Module R D] [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n]
    (t : Matrix n n D →ₗ[R] M) (hcyc : ∀ X Y : Matrix n n D, t (X * Y) = t (Y * X)) :
    ∃ τ : D →ₗ[R] M, (∀ a b : D, τ (a * b) = τ (b * a)) ∧
      t = τ.comp (Matrix.traceLinearMap n R D) := by
  classical
  rcases isEmpty_or_nonempty n with _ | ⟨⟨i₀⟩⟩
  · exact ⟨0, fun _ _ ↦ rfl, ext fun X ↦ by simp [Subsingleton.elim X 0]⟩
  · let τ : D →ₗ[R] M := t.comp (Matrix.singleLinearMap R i₀ i₀)
    have hτ a : τ a = t (Matrix.single i₀ i₀ a) := by simp [τ, Matrix.singleLinearMap]
    refine ⟨τ, fun a b ↦ by
        simp_rw [hτ, ← Matrix.single_mul_single_same (i := i₀) (j := i₀) (k := i₀), hcyc],
      ext fun X ↦ ?_⟩
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum, comp_apply, Matrix.traceLinearMap_apply, Matrix.trace, Matrix.diag_apply]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hsingle_off {j : n} :
        Matrix.single i j (X i j) = Matrix.single i j (X i j) * Matrix.single j j 1 := by simp
    have hsingle_diag :
        Matrix.single i i (X i i) = Matrix.single i i₀ (X i i) * Matrix.single i₀ i 1 := by simp
    rw [Finset.sum_eq_single i (fun j _ hji ↦ by rw [hsingle_off, hcyc]; simp [hji])
      (fun hi ↦ absurd (Finset.mem_univ i) hi),
      hsingle_diag, hcyc, Matrix.single_mul_single_same, one_mul, hτ]

/-- Recovering the factor `τ` from `t = τ.comp (Matrix.traceLinearMap n R D)` on any diagonal
matrix entry `Matrix.single i i a`. -/
theorem apply_eq_single_of_eq_comp_traceLinearMap {R D M : Type*} [CommSemiring R] [Semiring D]
    [Module R D] [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n] [DecidableEq n]
    {t : Matrix n n D →ₗ[R] M} {τ : D →ₗ[R] M}
    (ht : t = τ.comp (Matrix.traceLinearMap n R D)) (i : n) (a : D) :
    τ a = t (Matrix.single i i a) := by
  rw [ht, comp_apply, Matrix.traceLinearMap_apply, Matrix.trace_single_eq_same]

/-- For nonempty `n`, precomposition with `Matrix.traceLinearMap n R D` is injective. -/
theorem comp_traceLinearMap_injective {R D M : Type*} [CommSemiring R] [Semiring D] [Module R D]
    [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n] [Nonempty n] :
    Function.Injective (fun τ : D →ₗ[R] M ↦ τ.comp (Matrix.traceLinearMap n R D)) := by
  classical
  intro τ₁ τ₂ h
  ext a
  obtain ⟨i⟩ := ‹Nonempty n›
  rw [apply_eq_single_of_eq_comp_traceLinearMap
      (t := τ₁.comp (Matrix.traceLinearMap n R D)) rfl i a,
    LinearMap.congr_fun h (Matrix.single i i a),
    ← apply_eq_single_of_eq_comp_traceLinearMap
      (t := τ₂.comp (Matrix.traceLinearMap n R D)) rfl i a]

/-- For nonempty `n`, every cyclic `R`-linear map on `Matrix n n D` factors uniquely through
`Matrix.traceLinearMap n R D` via a cyclic `R`-linear map on `D`. -/
theorem existsUnique_eq_comp_traceLinearMap_of_cyclic {R D M : Type*} [CommSemiring R] [Semiring D]
    [Module R D] [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n] [Nonempty n]
    (t : Matrix n n D →ₗ[R] M) (hcyc : ∀ X Y : Matrix n n D, t (X * Y) = t (Y * X)) :
    ∃! τ : D →ₗ[R] M, (∀ a b : D, τ (a * b) = τ (b * a)) ∧
      t = τ.comp (Matrix.traceLinearMap n R D) := by
  obtain ⟨τ, hτ_cyc, hτ⟩ := exists_eq_comp_traceLinearMap_of_cyclic t hcyc
  exact ⟨τ, ⟨hτ_cyc, hτ⟩, fun τ' ⟨_, hτ'⟩ ↦ comp_traceLinearMap_injective (hτ'.symm.trans hτ)⟩

/-- Evaluating an `R`-linear map `τ : D →ₗ[R] M` on `Matrix.trace (c • (1 : Matrix n n D))`
scales `τ c` by `(Fintype.card n : R)`. -/
theorem map_trace_smul_one {R D M : Type*} [Semiring R] [NonAssocSemiring D] [Module R D]
    [AddCommMonoid M] [Module R M] {n : Type*} [Fintype n] [DecidableEq n]
    (τ : D →ₗ[R] M) (c : D) :
    τ (Matrix.trace (c • (1 : Matrix n n D))) = (Fintype.card n : R) • τ c := by
  have htr : Matrix.trace (c • (1 : Matrix n n D)) = Fintype.card n • c := by
    simp [Matrix.trace_smul, Nat.cast_comm]
  rw [htr, map_nsmul, Nat.cast_smul_eq_nsmul]

/-- A cyclic `R`-linear map `t : Matrix n n D →ₗ[R] R` with `0 < t 1` factors through
`Matrix.traceLinearMap n R D` via a cyclic `R`-linear map `τ` with `0 < τ 1`. -/
theorem exists_eq_comp_traceLinearMap_pos_of_cyclic {R D : Type*} [CommSemiring R] [LinearOrder R]
    [IsStrictOrderedRing R] [Semiring D] [Module R D] {n : Type*} [Fintype n] [DecidableEq n]
    (t : Matrix n n D →ₗ[R] R)
    (hcyc : ∀ X Y : Matrix n n D, t (X * Y) = t (Y * X)) (ht1 : 0 < t 1) :
    ∃ τ : D →ₗ[R] R, 0 < τ 1 ∧ (∀ a b : D, τ (a * b) = τ (b * a)) ∧
      t = τ.comp (Matrix.traceLinearMap n R D) := by
  obtain ⟨τ, hτ_cyc, hτ⟩ := exists_eq_comp_traceLinearMap_of_cyclic t hcyc
  have htpos : 0 < (Fintype.card n : R) * τ 1 := by
    have h := LinearMap.congr_fun hτ 1
    rw [comp_apply, Matrix.traceLinearMap_apply, ← one_smul D (1 : Matrix n n D),
      τ.map_trace_smul_one, smul_eq_mul] at h
    exact h ▸ by simpa using ht1
  exact ⟨τ, pos_of_mul_pos_right htpos (Nat.cast_nonneg _), hτ_cyc, hτ⟩

/-- Rank-one trace identity: when `rePart` is cyclic (`∀ a b : D, rePart (a * b) = rePart (b * a)`),
for `X = Matrix.vecMulVec v (star w)`,
`(rePart.comp (Matrix.traceLinearMap n R D)) (X * U * Xᴴ * V)` equals `rePart` applied to
`(star v ⬝ᵥ (V *ᵥ v)) * (star w ⬝ᵥ (U *ᵥ w))`. -/
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
  have hdot : rePart (v ⬝ᵥ ((((star w) ᵥ* U) ⬝ᵥ w) • ((star v) ᵥ* V))) =
      rePart (((star v ᵥ* V) ⬝ᵥ v) * ((star w ᵥ* U) ⬝ᵥ w)) := by
    simp only [dotProduct, Pi.smul_apply, smul_eq_mul, map_sum]
    rw [Finset.sum_congr rfl fun i _ ↦ by rw [hre_cyc, mul_assoc], ← map_sum, ← Finset.mul_sum,
      hre_cyc]
  rw [comp_apply, Matrix.traceLinearMap_apply, hX, Matrix.trace_vecMulVec, hdot,
    ← Matrix.dotProduct_mulVec, ← Matrix.dotProduct_mulVec]

end LinearMap
