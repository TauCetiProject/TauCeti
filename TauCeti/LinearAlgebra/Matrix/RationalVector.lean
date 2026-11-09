/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

/-!
# Principal congruence matrices on vectors with bounded denominator

A matrix congruent to the identity modulo `N` fixes every row vector in
`(N⁻¹ℤ/ℤ)ⁿ`. The statement here gives an actual integral translation between
the two vectors in any division ring, rather than passing to a quotient.
If `N` casts to zero, division by zero makes both vectors zero.
This is useful for transformation laws whose multipliers depend on integral translations.
-/

public section

namespace Matrix

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
  have hdiv : ∀ i j, (N : ℤ) ∣ M i j - (1 : Matrix ι ι ℤ) i j := by
    intro i j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    simpa [Matrix.one_apply, sub_eq_zero] using congr_fun₂ hM i j
  choose B hB using hdiv
  refine ⟨a ᵥ* B, ?_⟩
  have hentry (i j : ι) : M i j =
      (1 : Matrix ι ι ℤ) i j + N * B i j := by linarith [hB i j]
  have hmat : M.map (Int.castRingHom K) =
      1 + (N : K) • (Matrix.of B).map (Int.castRingHom K) := by
    ext i j
    simp [hentry, Matrix.one_apply]
  rw [hmat, vecMul_add, vecMul_one]
  congr 1
  ext j
  simp only [vecMul, dotProduct, Matrix.smul_apply, smul_eq_mul, Matrix.map_apply,
    Int.cast_sum, Int.cast_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp [div_eq_mul_inv, mul_assoc, hN]

end Matrix
