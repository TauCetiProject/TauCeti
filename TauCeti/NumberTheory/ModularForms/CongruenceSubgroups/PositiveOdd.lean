/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Modular.Reduction
public import TauCeti.NumberTheory.Modular.ConjugateTranslation
public import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.Basic

/-!
# Positive odd matrix entries in congruence subgroups

Theta transformation formulas obtained from quadratic Gauss sums initially apply to a matrix
`[a,b;c,d]` with `c > 0` and `a` positive and odd. These restrictions can be arranged using
translations, with two different ways of arranging the sign of `c`.

In `Γ₀(N)` one may negate the matrix, then left multiply by `T^j`, leaving its bottom row fixed
up to the common sign. In `Γ(N)` negation is generally unavailable: invert the matrix when
`c < 0`, then left multiply by `T^(jN)`. The translations remain in `Γ(N)`. In both cases `j`
can be nonnegative. The determinant equation ensures that an even translation step already has
odd initial entry `a`.

The zero lower-left entry is handled by the existing signed-translation decomposition
`TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero`. For `Γ(N)`, the exponent is a
multiple of `N`, and the negative sign can occur only when `N ∣ 2`.

## References

* B. Schoeneberg, *Elliptic Modular Functions*, Chapter IX.
* W. Ebeling, *Lattices and Codes*, third edition, Chapter 3.
-/

public section

open Matrix Matrix.SpecialLinearGroup ModularGroup
open scoped MatrixGroups

namespace CongruenceSubgroup

/-- A matrix in `Γ₀(N)` with nonzero lower-left entry can be made to have positive lower-left
and positive odd upper-left entries by negation and a nonnegative translation. -/
theorem exists_pos_odd_of_mem_Gamma0 {N : ℕ} {A : SL(2, ℤ)} (hA : A ∈ Gamma0 N)
    (hc : A 1 0 ≠ 0) :
    ∃ B ∈ Gamma0 N, 0 < B 1 0 ∧ 0 < B 0 0 ∧ Odd (B 0 0) ∧
      ∃ j : ℕ, B = T ^ (j : ℤ) * A ∨ B = T ^ (j : ℤ) * (-A) := by
  have hpos (C : SL(2, ℤ)) (hC : C ∈ Gamma0 N) (hcC : 0 < C 1 0) :
      ∃ B ∈ Gamma0 N, 0 < B 1 0 ∧ 0 < B 0 0 ∧ Odd (B 0 0) ∧
        ∃ j : ℕ, B = T ^ (j : ℤ) * C := by
    obtain ⟨j, hj, hjo⟩ := C.exists_pos_odd_T_zpow_mul (m := 1) (one_dvd _) hcC
    simp only [Nat.cast_one, mul_one] at hj hjo
    have hrow := congrFun (T_pow_mul_apply_one (j : ℤ) C) 0
    refine ⟨T ^ (j : ℤ) * C, ?_, ?_, hj, hjo, j, rfl⟩
    · simpa only [Gamma0_mem, hrow] using hC
    · rwa [hrow]
  rcases hc.lt_or_gt with hc | hc
  · have hneg : -A ∈ Gamma0 N := by simpa [Gamma0_mem] using hA
    obtain ⟨B, hB, hBc, hBa, hBo, j, hj⟩ := hpos (-A) hneg (by simpa using neg_pos.mpr hc)
    exact ⟨B, hB, hBc, hBa, hBo, j, Or.inr hj⟩
  · obtain ⟨B, hB, hBc, hBa, hBo, j, hj⟩ := hpos A hA hc
    exact ⟨B, hB, hBc, hBa, hBo, j, Or.inl hj⟩

/-- A matrix in `Γ(N)` with nonzero lower-left entry can be made to have positive
lower-left and positive odd upper-left entries using inversion and a nonnegative translation
by a multiple of `N`. Both operations stay inside `Γ(N)`. -/
theorem exists_pos_odd_of_mem_Gamma {N : ℕ} {A : SL(2, ℤ)}
    (hA : A ∈ Gamma N) (hc : A 1 0 ≠ 0) :
    ∃ B ∈ Gamma N, 0 < B 1 0 ∧ 0 < B 0 0 ∧ Odd (B 0 0) ∧
      ∃ j : ℕ, B = T ^ ((j : ℤ) * N) * A ∨ B = T ^ ((j : ℤ) * N) * A⁻¹ := by
  have hpos (C : SL(2, ℤ)) (hC : C ∈ Gamma N) (hcC : 0 < C 1 0) :
      ∃ B ∈ Gamma N, 0 < B 1 0 ∧ 0 < B 0 0 ∧ Odd (B 0 0) ∧
        ∃ j : ℕ, B = T ^ ((j : ℤ) * N) * C := by
    have hdvd : (N : ℤ) ∣ C 1 0 :=
      mem_Gamma0_iff_dvd.mp (Gamma_le_Gamma0 N hC)
    obtain ⟨j, hj, hjo⟩ := C.exists_pos_odd_T_zpow_mul hdvd hcC
    refine ⟨T ^ ((j : ℤ) * N) * C, ?_, ?_, hj, hjo, j, rfl⟩
    · exact (Gamma N).mul_mem
        (by simpa using ModularGroup_T_pow_mem_Gamma (N : ℤ) _ (dvd_mul_left _ _)) hC
    · simpa only [T_pow_mul_apply_one] using hcC
  rcases hc.lt_or_gt with hc | hc
  · obtain ⟨B, hB, hBc, hBa, hBo, j, hj⟩ := hpos A⁻¹ ((Gamma N).inv_mem hA)
      (by simpa [SL2_inv_expl] using neg_pos.mpr hc)
    exact ⟨B, hB, hBc, hBa, hBo, j, Or.inr hj⟩
  · obtain ⟨B, hB, hBc, hBa, hBo, j, hj⟩ := hpos A hA hc
    exact ⟨B, hB, hBc, hBa, hBo, j, Or.inl hj⟩

/-- A matrix in `Γ(N)` fixing infinity is a signed translation by a multiple of `N`.
The negative sign is possible only at levels dividing `2`. -/
theorem dvd_and_eq_T_zpow_or_eq_neg_T_zpow_of_mem_Gamma_of_c_eq_zero {N : ℕ} {A : SL(2, ℤ)}
    (hA : A ∈ Gamma N) (hc : A 1 0 = 0) :
    (N : ℤ) ∣ A 0 1 ∧
      (A = T ^ A 0 1 ∨ N ∣ 2 ∧ A = -T ^ (-A 0 1)) := by
  refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma_mem.mp hA).2.1, ?_⟩
  rcases TauCeti.ModularGroup.eq_T_zpow_or_eq_neg_T_zpow_of_c_eq_zero hc with h | h
  · exact Or.inl h
  · refine Or.inr ⟨?_, h⟩
    apply neg_one_mem_Gamma1_iff.mp
    have hmem := (Gamma1 N).mul_mem (Gamma_le_Gamma1 N hA)
      (T_zpow_mem_Gamma1 N (A 0 1))
    nth_rw 1 [h] at hmem
    simpa only [neg_mul, ← zpow_add, neg_add_cancel, zpow_zero] using hmem

end CongruenceSubgroup
