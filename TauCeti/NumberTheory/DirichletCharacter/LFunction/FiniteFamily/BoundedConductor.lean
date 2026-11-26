/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.LFunction.FiniteFamily.Basic
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel

/-!
# Uniform lower bounds for regularized L-functions of bounded conductor

A bound on the conductor gives a finite family of primitive L-functions. The change-of-level
formula transfers their common positive lower bound near `1` to the regularized L-functions
at all ambient levels with a bounded number of prime divisors.
-/

public section

open Finset Filter DirichletCharacter
open scoped Topology

namespace TauCeti.DirichletCharacter

/-- Regularized L-functions are uniformly bounded away from zero near `1` when both the
conductor and the number of distinct prime divisors of the level are bounded. -/
theorem exists_pos_eventually_le_norm_regularizedLFunction_of_conductor_le (B k : ℕ) :
    ∃ c > (0 : ℝ), ∀ᶠ s : ℂ in 𝓝 1, ∀ (N : ℕ) [NeZero N], N.primeFactors.card ≤ k →
      ∀ χ : DirichletCharacter ℂ N, χ.conductor ≤ B → c ≤ ‖χ.regularizedLFunction s‖ := by
  let K := (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ k
  have hK : 0 < K := by
    apply pow_pos
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  obtain ⟨c, hc, hnear⟩ := exists_pos_eventually_le_norm_regularizedLFunction_of_level_le B
  have hre : ∀ᶠ s : ℂ in 𝓝 1, (1 / 2 : ℝ) < s.re :=
    Complex.continuous_re.continuousAt.tendsto.eventually_const_lt (by norm_num)
  refine ⟨c * K, mul_pos hc hK, ?_⟩
  filter_upwards [hnear, hre] with s hs hsre N inst hN χ hχ
  obtain rfl | h := eq_or_ne χ 1
  · have hB : 1 ≤ B := by simpa only [conductor_one] using hχ
    have h₁ := hs 1 hB 1
    have h₂ : K ≤ ‖∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))‖ := by
      simpa [K, MulChar.one_apply (isUnit_of_subsingleton _)] using
        one_sub_rpow_pow_le_norm_prod_one_sub_mul_prime_cpow (N := N) (1 : DirichletCharacter ℂ 1)
          hN (by norm_num : (0 : ℝ) ≤ 1 / 2) hsre.le
    rw [regularizedLFunction_one_apply, entireLFunction_one,
      LFunctionTrivChar₁_eq_mul_prod_one_sub_prime_cpow, mul_div_right_comm, norm_mul,
      ← entireLFunction_one, ← regularizedLFunction_one_apply]
    exact mul_le_mul h₁ h₂ hK.le (norm_nonneg _)
  · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hprim : χ.primitiveCharacter ≠ 1 := mt (χ.primitiveCharacter_eq_one_iff).mp h
    have h₁ := hs χ.conductor hχ χ.primitiveCharacter
    rw [χ.primitiveCharacter.regularizedLFunction_of_ne_one hprim] at h₁
    have h₂ := one_sub_rpow_pow_le_norm_prod_one_sub_mul_prime_cpow χ.primitiveCharacter hN
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hsre.le
    rw [χ.regularizedLFunction_of_ne_one h, ← χ.changeLevel_primitiveCharacter,
      LFunction_changeLevel _ _ (.inl hprim), norm_mul]
    exact mul_le_mul h₁ h₂ hK.le (norm_nonneg _)

end TauCeti.DirichletCharacter
