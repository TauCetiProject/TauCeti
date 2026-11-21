/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Modular
import TauCeti.Data.Int.Progression
import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.ModularGroup

/-!
# Reduction and Euclidean induction in `SL₂(ℤ)`

This file collects elementary reduction lemmas for matrices in `SL₂(ℤ)` with positive lower-left
entry:

* `Matrix.SpecialLinearGroup.exists_pos_odd_T_zpow_mul`: translating on the left by a nonnegative
  multiple of any natural divisor of the lower-left entry produces a positive odd upper-left entry.
* `Matrix.SpecialLinearGroup.coe_mul_T`: explicit matrix entries of `γ * T`.
* `Matrix.SpecialLinearGroup.induction_on_of_c_pos`: Euclidean induction on
  `{γ ∈ SL₂(ℤ) | 0 < γ 1 0}` from the base case `γ 1 0 = 1`, right translation `γ ↦ γ T`, and
  right inversion `γ ↦ γ S` when `0 < γ 1 1`.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Chapter IX.
* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
-/

public section

open Matrix Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

/-- If `m` divides the positive lower-left entry of `A`, a nonnegative multiple of `m`
translates its upper-left entry to a positive odd integer. -/
theorem exists_pos_odd_T_zpow_mul (A : SL(2, ℤ)) {m : ℕ}
    (hmc : (m : ℤ) ∣ A 1 0) (hc : 0 < A 1 0) :
    ∃ j : ℕ, 0 < (T ^ ((j : ℤ) * m) * A) 0 0 ∧
      Odd ((T ^ ((j : ℤ) * m) * A) 0 0) := by
  have hm : 0 < m := Nat.pos_of_ne_zero fun hm ↦ hc.ne' (by simpa [hm] using hmc)
  have hdet : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [det_fin_two] using A.det_coe
  have hodd : Odd (A 0 0) ∨ Odd ((m : ℤ) * A 1 0) := by
    by_cases ha : Odd (A 0 0)
    · exact Or.inl ha
    · right
      have hcodd : Odd (A 1 0) := by
        by_contra hn
        have heven := ((Int.not_odd_iff_even.mp ha).mul_right (A 1 1)).sub
          ((Int.not_odd_iff_even.mp hn).mul_left (A 0 1))
        rw [hdet] at heven
        exact Int.not_even_one heven
      have hmodd : Odd (m : ℤ) := by
        obtain ⟨t, ht⟩ := hmc
        rw [ht] at hcodd
        exact (Int.odd_mul.mp hcodd).1
      exact hmodd.mul hcodd
  obtain ⟨j, hj, hjodd⟩ := Int.exists_nat_add_mul_pos_odd (A 0 0)
    (mul_pos (Int.natCast_pos.mpr hm) hc) hodd
  refine ⟨j, ?_⟩
  simpa [coe_mul, coe_T_zpow, Matrix.mul_apply, Fin.sum_univ_two,
    mul_assoc] using And.intro hj hjodd

/-- Explicit matrix entries of `γ * T` for `γ ∈ SL(2, ℤ)`. -/
theorem coe_mul_T (γ : SL(2, ℤ)) :
    (↑(γ * T) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![γ 0 0, γ 0 0 + γ 0 1; γ 1 0, γ 1 0 + γ 1 1] := by
  simpa using coe_mul_T_zpow γ 1

/-- **Euclidean induction on `SL(2, ℤ)` with positive lower-left entry.** A property of matrices
`γ ∈ SL(2, ℤ)` with `0 < γ 1 0` holds whenever it holds at `γ 1 0 = 1`, is invariant under right
multiplication by `T`, and passes from `γ * S` back to `γ` when `0 < γ 1 1`. -/
theorem induction_on_of_c_pos (γ : SL(2, ℤ)) (hc : 0 < γ 1 0) {P : SL(2, ℤ) → Prop}
    (h_one : ∀ γ : SL(2, ℤ), γ 1 0 = 1 → P γ)
    (h_T : ∀ γ : SL(2, ℤ), 0 < γ 1 0 → (P (γ * T) ↔ P γ))
    (h_S : ∀ γ : SL(2, ℤ), 0 < γ 1 0 → 0 < γ 1 1 → P (γ * S) → P γ) :
    P γ := by
  have h_Tzpow (δ : SL(2, ℤ)) (hδ : 0 < δ 1 0) (n : ℤ) : P (δ * T ^ n) ↔ P δ := by
    induction n using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [zpow_add_one, ← mul_assoc, h_T _ (by rw [coe_mul_T_zpow]; simpa using hδ), ih]
    | pred k ih =>
      have hsub : δ * T ^ (-(k : ℤ) - 1) * T = δ * T ^ (-(k : ℤ)) := by
        rw [mul_assoc, ← zpow_add_one]
        simp
      rw [← h_T (δ * T ^ (-(k : ℤ) - 1)) (by rw [coe_mul_T_zpow]; simpa using hδ), hsub, ih]
  suffices ∀ n : ℕ, ∀ γ : SL(2, ℤ), 0 < γ 1 0 → (γ 1 0).toNat = n → P γ from
    this (γ 1 0).toNat γ hc rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro γ hc hn
    by_cases h1 : γ 1 0 = 1
    · exact h_one γ h1
    set q : ℤ := γ 1 1 / γ 1 0
    set γ' : SL(2, ℤ) := γ * T ^ (-q)
    have hγ'_c : γ' 1 0 = γ 1 0 := by dsimp only [γ']; rw [coe_mul_T_zpow]; simp
    have hγ'_d : γ' 1 1 = γ 1 1 % γ 1 0 := by
      have hval : γ' 1 1 = γ 1 0 * (-q) + γ 1 1 := by dsimp only [γ']; rw [coe_mul_T_zpow]; simp
      rw [hval, Int.emod_def]
      ring
    have hd_nonneg : 0 ≤ γ' 1 1 := hγ'_d ▸ Int.emod_nonneg _ hc.ne'
    have hd_lt : γ' 1 1 < γ 1 0 := hγ'_d ▸ Int.emod_lt_of_pos _ hc
    have hd_ne : γ' 1 1 ≠ 0 := by
      intro h0
      have hdet := γ'.det_coe
      rw [det_fin_two, h0, mul_zero, zero_sub, hγ'_c] at hdet
      have hdvd : γ 1 0 ∣ 1 := ⟨-γ' 0 1, by linarith⟩
      have := Int.le_of_dvd one_pos hdvd
      omega
    have hd_pos : 0 < γ' 1 1 := lt_of_le_of_ne hd_nonneg hd_ne.symm
    have hS_c : (γ' * S) 1 0 = γ' 1 1 := by rw [coe_mul_S]; simp
    have hPS : P (γ' * S) := ih (γ' 1 1).toNat (by omega) (γ' * S) (by omega) (by rw [hS_c])
    have hγ_eq : γ = γ' * T ^ q := by simp [γ', mul_assoc]
    rw [hγ_eq, h_Tzpow γ' (by omega) q]
    exact h_S γ' (by omega) hd_pos hPS

end Matrix.SpecialLinearGroup
