/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic

/-!
# Principal congruence matrices and rational-denominator vectors

A matrix congruent to the identity modulo `N` fixes every row vector in
`(N⁻¹ℤ/ℤ)ⁿ`. The statements here give an actual integral translation between
the two vectors in any division ring, rather than passing to a quotient: writing the
matrix as `1 + N • B`, the translation of `a / N` is `a B`.
If `N` casts to zero, division by zero makes both vectors zero.
This is useful for transformation laws whose multipliers depend on integral translations.

This file also records that right multiplication by an integer matrix commutes with dividing a
vector by `N` (`Matrix.vecMul_div_map_intCast`).
-/

public section

namespace Matrix

/-- A matrix reducing to the identity modulo `N` is `1 + N • B` for an integral matrix `B`. -/
theorem exists_eq_one_add_smul_of_map_eq_one {ι : Type*} [DecidableEq ι]
    (M : Matrix ι ι ℤ) {N : ℕ} (hM : M.map (Int.castRingHom (ZMod N)) = 1) :
    ∃ B : Matrix ι ι ℤ, M = 1 + (N : ℤ) • B := by
  have hdiv : ∀ i j, (N : ℤ) ∣ M i j - (1 : Matrix ι ι ℤ) i j := by
    intro i j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [Matrix.one_apply, sub_eq_zero] using congr_fun₂ hM i j
  choose B hB using hdiv
  exact ⟨Matrix.of B, by ext i j; simp [← hB]⟩

/-- Multiplying a rational-denominator row vector `a / N` on the right by an integer matrix `M`
commutes with dividing by `N`: `(a / N) ᵥ* M = (a ᵥ* M) / N` in any division ring. -/
theorem vecMul_div_map_intCast {ι κ K : Type*} [Fintype ι] [DivisionRing K]
    (M : Matrix ι κ ℤ) (N : ℕ) (a : ι → ℤ) :
    (fun i ↦ (a i : K) / N) ᵥ* M.map (Int.castRingHom K) =
      fun j ↦ (((a ᵥ* M) j : ℤ) : K) / N := by
  ext j
  simp only [vecMul, dotProduct, Matrix.map_apply, eq_intCast, Int.cast_sum, Int.cast_mul,
    div_eq_mul_inv, Finset.sum_mul, mul_assoc]
  exact Finset.sum_congr rfl fun i _ ↦
    congrArg _ (Nat.commute_cast (M i j : K) N).inv_right₀.symm.eq

/-- The matrix `1 + N • B` carries `a / N` to `a / N + a B`, an explicit integral translation,
whenever `N` does not cast to zero. -/
theorem vecMul_div_eq_add_intCast_vecMul {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [DivisionRing K] (B : Matrix ι ι ℤ) {N : ℕ} (hN : (N : K) ≠ 0) (a : ι → ℤ) :
    (fun i ↦ (a i : K) / N) ᵥ* (1 + (N : ℤ) • B).map (Int.castRingHom K) =
      (fun i ↦ (a i : K) / N) + fun i ↦ ((a ᵥ* B) i : K) := by
  have hmat : (1 + (N : ℤ) • B).map (Int.castRingHom K) =
      1 + (N : K) • B.map (Int.castRingHom K) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.one_apply]
    split_ifs <;> simp
  rw [hmat, vecMul_add, vecMul_one]
  congr 1
  ext j
  simp only [vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply,
    Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp [div_eq_mul_inv, mul_assoc, hN]

/-- A matrix reducing to the identity modulo `N` carries `a / N` to itself plus an
integral vector in any division ring. If `N` casts to zero, the zero integral
vector witnesses the identity. -/
theorem exists_vecMul_div_eq_add_intCast {ι K : Type*} [Fintype ι] [DecidableEq ι]
    [DivisionRing K] (M : Matrix ι ι ℤ) {N : ℕ}
    (hM : M.map (Int.castRingHom (ZMod N)) = 1) (a : ι → ℤ) :
    ∃ s : ι → ℤ,
      (fun i ↦ (a i : K) / N) ᵥ* M.map (Int.castRingHom K) =
        (fun i ↦ (a i : K) / N) + fun i ↦ (s i : K) := by
  by_cases hN : (N : K) = 0
  · exact ⟨0, by ext j; simp [hN, vecMul, dotProduct]⟩
  obtain ⟨B, rfl⟩ := M.exists_eq_one_add_smul_of_map_eq_one hM
  exact ⟨a ᵥ* B, vecMul_div_eq_add_intCast_vecMul B hN a⟩

end Matrix
