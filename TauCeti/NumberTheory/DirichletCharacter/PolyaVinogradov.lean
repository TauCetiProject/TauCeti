/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.DirichletCharacter.Bounds

import TauCeti.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.NumberTheory.ArithmeticFunction.Zeta
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.FourierInterval
import TauCeti.NumberTheory.DirichletCharacter.PartialSum

/-!
# The Pólya–Vinogradov inequality

Primitive nonprincipal complex Dirichlet characters have interval sums bounded uniformly in the
length of the interval. The same estimate holds on progressions with invertible step.

We use the Gauss-sum bound `DirichletCharacter.norm_sum_range_add_le_sum_norm_stdAddChar`
and the harmonic-sum estimate `ZMod.sum_norm_sum_range_stdAddChar_mul_add_le`. This is the
classical Fourier proof; see Montgomery and Vaughan, *Multiplicative Number Theory I: Classical
Theory*, Chapter 9, Theorem 9.18.

Imprimitive characters are handled by sieving the partial sums to the integers prime to a fixed
`m`, at the cost of a factor `2 ^ ω m`
(`DirichletCharacter.norm_sum_Icc_filter_coprime_le_two_pow_mul`). A character induced from a
primitive nonprincipal character `χ` modulo `N` to the level `M` agrees with `χ` on the `n` prime
to `M / N` and vanishes elsewhere, so its partial sums are at most
`2 ^ ω (M / N) * √N * (1 + log N)` (`DirichletCharacter.norm_sum_Icc_changeLevel_le`).
Every character is induced from its primitive character, and `2 ^ ω m ≤ 2 * √m`, so the partial
sums of an arbitrary nonprincipal complex Dirichlet character modulo `N` are at most
`2 * √N * (1 + log N)` (`DirichletCharacter.norm_sum_Icc_le_of_ne_one`).
-/

public section

open Finset ZMod
open scoped Real

namespace DirichletCharacter

open scoped ArithmeticFunction.omega

variable {N : ℕ} [NeZero N]

/-- **Pólya–Vinogradov inequality** for intervals of arbitrary length and starting residue.
The character may be any primitive nonprincipal complex Dirichlet character. -/
theorem norm_sum_range_add_le (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hχ₀ : χ ≠ 1) (a : ZMod N) (H : ℕ) :
    ‖∑ j ∈ range H, χ (a + (j : ZMod N))‖ ≤ Real.sqrt N * (1 + Real.log N) := by
  calc
    _ ≤ (Real.sqrt N / N) * ∑ k ∈ univ.erase (0 : ZMod N),
        ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ :=
      by simpa only [Real.sqrt_div_self] using
        χ.norm_sum_range_add_le_sum_norm_stdAddChar hχ hχ₀ a H
    _ ≤ (Real.sqrt N / N) * (N * (1 + Real.log N)) := by
      exact mul_le_mul_of_nonneg_left
        (ZMod.sum_norm_sum_range_stdAddChar_mul_add_le a H) (by positivity)
    _ = _ := by field_simp [NeZero.ne (N : ℝ)]

/-- **Pólya–Vinogradov inequality** for progressions with unit step modulo the conductor. -/
theorem norm_sum_range_add_mul_le (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hχ₀ : χ ≠ 1) (a : ZMod N) (d : (ZMod N)ˣ) (H : ℕ) :
    ‖∑ j ∈ range H, χ (a + (j : ZMod N) * (d : ZMod N))‖ ≤
      Real.sqrt N * (1 + Real.log N) := by
  have he (j : ℕ) : a + (j : ZMod N) * (d : ZMod N) =
      (d : ZMod N) * ((↑d⁻¹ : ZMod N) * a + j) := by
    rw [mul_add, d.mul_inv_cancel_left]
    ring
  simp_rw [he, map_mul, ← mul_sum, norm_mul, χ.unit_norm_eq_one d, one_mul]
  exact χ.norm_sum_range_add_le hχ hχ₀ _ H

/-- **Pólya–Vinogradov inequality** on an integer interval, including negative endpoints. -/
theorem norm_sum_Ico_le (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hχ₀ : χ ≠ 1) (a b : ℤ) :
    ‖∑ j ∈ Ico a b, χ (j : ZMod N)‖ ≤ Real.sqrt N * (1 + Real.log N) := by
  rw [Int.Ico_eq_finset_map, sum_map]
  simpa only [Function.Embedding.trans_apply, Nat.castEmbedding_apply,
    addLeftEmbedding_apply, Int.cast_add, Int.cast_natCast] using
    χ.norm_sum_range_add_le hχ hχ₀ (a : ZMod N) (b - a).toNat

/-- The **Pólya–Vinogradov inequality** for the partial sums `∑ n ∈ Icc 1 K, χ n` of a primitive
nonprincipal complex Dirichlet character. -/
theorem norm_sum_Icc_le (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1)
    (K : ℕ) : ‖∑ n ∈ Icc 1 K, χ n‖ ≤ Real.sqrt N * (1 + Real.log N) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  simpa using χ.norm_sum_range_add_le hχ hχ₀ 1 K

/-- **Pólya–Vinogradov inequality** on the integers prime to `m`: for a primitive nonprincipal
complex Dirichlet character modulo `N`, every partial sum over the `n ≤ K` prime to `m` has norm
at most `2 ^ ω m * √N * (1 + log N)`. -/
theorem norm_sum_Icc_filter_coprime_le (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hχ₀ : χ ≠ 1) (m K : ℕ) :
    ‖∑ n ∈ Icc 1 K with n.Coprime m, χ n‖ ≤
      2 ^ ω m * (Real.sqrt N * (1 + Real.log N)) :=
  χ.norm_sum_Icc_filter_coprime_le_two_pow_mul (χ.norm_sum_Icc_le hχ hχ₀) m K

/-- **Pólya–Vinogradov inequality for imprimitive characters.** If `χ` is a primitive
nonprincipal complex Dirichlet character modulo `N` and `N ∣ M`, then every partial sum of the
character induced from `χ` at level `M` has norm at most `2 ^ ω (M / N) * √N * (1 + log N)`. -/
theorem norm_sum_Icc_changeLevel_le (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hχ₀ : χ ≠ 1) {M : ℕ} (h : N ∣ M) (K : ℕ) :
    ‖∑ n ∈ Icc 1 K, changeLevel h χ n‖ ≤
      2 ^ ω (M / N) * (Real.sqrt N * (1 + Real.log N)) := by
  -- At `n` prime to `M / N` but not to `M`, `n` is not prime to `N`, so `χ n = 0` already.
  have hval (n : ℕ) : changeLevel h χ n = if n.Coprime (M / N) then χ n else 0 := by
    rw [changeLevel_natCast]
    split_ifs with hnM hn hn
    · rfl
    · exact absurd (hnM.coprime_dvd_right (Nat.div_dvd_of_dvd h)) hn
    · refine (χ.map_nonunit fun hu ↦ hnM ?_).symm
      rw [← Nat.mul_div_cancel' h]
      exact Nat.Coprime.mul_right ((ZMod.isUnit_iff_coprime n N).mp hu) hn
    · rfl
  simp_rw [hval, ← sum_filter]
  exact χ.norm_sum_Icc_filter_coprime_le hχ hχ₀ (M / N) K

/-- **Pólya–Vinogradov inequality** for an arbitrary nonprincipal complex Dirichlet character
`χ` modulo `N`: every partial sum `∑ n ∈ Icc 1 K, χ n` has norm at most `2 * √N * (1 + log N)`.

The character is induced from its primitive character of conductor `c ∣ N`, so the partial sums
are at most `2 ^ ω (N / c) * √c * (1 + log c)`, and `2 ^ ω (N / c) ≤ 2 * √(N / c)`. -/
theorem norm_sum_Icc_le_of_ne_one (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (K : ℕ) :
    ‖∑ n ∈ Icc 1 K, χ n‖ ≤ 2 * Real.sqrt N * (1 + Real.log N) := by
  have hc : χ.conductor ≠ 0 := χ.conductor_ne_zero
  have : NeZero χ.conductor := ⟨hc⟩
  have hdvd := χ.conductor_dvd_level
  have hle : χ.conductor ≤ N := Nat.le_of_dvd (NeZero.pos N) hdvd
  have h := χ.primitiveCharacter.norm_sum_Icc_changeLevel_le χ.primitiveCharacter_isPrimitive
    (mt χ.primitiveCharacter_eq_one_iff.mp hχ) hdvd K
  rw [χ.changeLevel_primitiveCharacter] at h
  refine h.trans ?_
  have hω : (2 : ℝ) ^ ω (N / χ.conductor) ≤ 2 * Real.sqrt (N / χ.conductor : ℕ) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left Real.nat_sqrt_le_real_sqrt zero_le_two)
    exact_mod_cast ArithmeticFunction.two_pow_cardDistinctFactors_le_two_mul_sqrt
      (Nat.div_ne_zero_iff_of_dvd hdvd |>.mpr ⟨NeZero.ne N, hc⟩)
  have hsqrt : Real.sqrt (N / χ.conductor : ℕ) * Real.sqrt χ.conductor = Real.sqrt N := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _), ← Nat.cast_mul, Nat.div_mul_cancel hdvd]
  have hlog : Real.log χ.conductor ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hc) (by exact_mod_cast hle)
  calc (2 : ℝ) ^ ω (N / χ.conductor) * (Real.sqrt χ.conductor * (1 + Real.log χ.conductor))
      ≤ 2 * Real.sqrt (N / χ.conductor : ℕ) * (Real.sqrt χ.conductor * (1 + Real.log N)) := by
        gcongr
    _ = 2 * Real.sqrt N * (1 + Real.log N) := by rw [← hsqrt]; ring

end DirichletCharacter
