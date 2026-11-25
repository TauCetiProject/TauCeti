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

import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.NumberTheory.DirichletCharacter.Basic
import TauCeti.NumberTheory.DirichletCharacter.PartialSum

/-!
# The Pólya–Vinogradov inequality

Primitive nonprincipal complex Dirichlet characters have interval sums bounded uniformly in the
length of the interval. The same estimate holds on progressions with invertible step.

We use discrete Fourier inversion and the primitive-character Gauss-sum formula from Mathlib,
then bound the resulting geometric sums by the chord inequality and a harmonic sum. This is the
classical Fourier proof; see Montgomery and Vaughan, *Multiplicative Number Theory I: Classical
Theory*, Chapter 9, Theorem 9.18.

Imprimitive characters are handled by sieving the partial sums to the integers prime to a fixed
`m`, at the cost of a factor `2 ^ ω m`
(`DirichletCharacter.norm_sum_Icc_filter_coprime_le_two_pow_mul`). A character induced from a
primitive nonprincipal character `χ` modulo `N` to the level `M` agrees with `χ` on the `n` prime
to `M / N` and vanishes elsewhere, so its partial sums are at most
`2 ^ ω (M / N) * √N * (1 + log N)` (`DirichletCharacter.norm_sum_Icc_changeLevel_le`).
-/

public section

open Finset ZMod
open scoped Real

namespace DirichletCharacter

open scoped ArithmeticFunction.omega

variable {N : ℕ} [NeZero N]

private lemma norm_interval_sum_le_fourier (χ : DirichletCharacter ℂ N)
    (hχ : χ.IsPrimitive) (hχ₀ : χ ≠ 1) (a : ZMod N) (H : ℕ) :
    ‖∑ j ∈ range H, χ (a + (j : ZMod N))‖ ≤
      (Real.sqrt N / N) * ∑ k ∈ univ.erase (0 : ZMod N),
        ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ := by
  have hz : 𝓕 (χ : ZMod N → ℂ) 0 = 0 := by
    rw [dft_apply_zero]
    exact MulChar.sum_eq_zero_of_ne_one hχ₀
  have hi (x : ZMod N) : χ x = (N : ℂ)⁻¹ *
      ∑ k ∈ univ.erase (0 : ZMod N), stdAddChar (k * x) * 𝓕 χ k := by
    have h := congr_fun ((dft (N := N) (E := ℂ)).symm_apply_apply χ) x
    rw [invDFT_apply] at h
    rw [← h, smul_eq_mul, ← sum_erase_add _ _ (mem_univ (0 : ZMod N))]
    simp only [hz, mul_zero, add_zero, smul_eq_mul]
  have heq : ∑ j ∈ range H, χ (a + (j : ZMod N)) = (N : ℂ)⁻¹ *
      ∑ k ∈ univ.erase (0 : ZMod N),
        (∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))) * 𝓕 χ k := by
    simp_rw [hi, ← mul_sum]
    rw [sum_comm]
    simp_rw [sum_mul]
  rw [heq, norm_mul, norm_inv, Complex.norm_natCast]
  calc (N : ℝ)⁻¹ * ‖∑ k ∈ univ.erase (0 : ZMod N),
        (∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))) * 𝓕 χ k‖
      ≤ (N : ℝ)⁻¹ * ∑ k ∈ univ.erase (0 : ZMod N),
          ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ * Real.sqrt N := by
        gcongr
        refine (norm_sum_le _ _).trans (sum_le_sum fun k _ ↦ ?_)
        rw [norm_mul, hχ.fourierTransform_eq_inv_mul_gaussSum, norm_mul,
          χ.norm_gaussSum_stdAddChar hχ]
        exact mul_le_mul_of_nonneg_left
          (mul_le_of_le_one_left (Real.sqrt_nonneg _) (χ⁻¹.norm_le_one (-k)))
          (norm_nonneg _)
    _ = _ := by rw [← sum_mul]; ring

/-- **Pólya–Vinogradov inequality** for intervals of arbitrary length and starting residue.
The character may be any primitive nonprincipal complex Dirichlet character. -/
theorem norm_sum_range_add_le (χ : DirichletCharacter ℂ N) (hχ : χ.IsPrimitive)
    (hχ₀ : χ ≠ 1) (a : ZMod N) (H : ℕ) :
    ‖∑ j ∈ range H, χ (a + (j : ZMod N))‖ ≤ Real.sqrt N * (1 + Real.log N) := by
  calc
    _ ≤ (Real.sqrt N / N) * ∑ k ∈ univ.erase (0 : ZMod N),
        ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ :=
      norm_interval_sum_le_fourier χ hχ hχ₀ a H
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

end DirichletCharacter
