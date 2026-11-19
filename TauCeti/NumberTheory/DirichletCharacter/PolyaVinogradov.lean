/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.NumberTheory.DirichletCharacter.Bounds

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.SpecialFunctions.Complex.CircleAddChar
import TauCeti.Data.ZMod.FinEquiv

/-!
# The Pólya–Vinogradov inequality

Primitive nonprincipal complex Dirichlet characters have interval sums bounded uniformly in the
length of the interval. The same estimate holds on progressions with invertible step.

We use discrete Fourier inversion and the primitive-character Gauss-sum formula from Mathlib,
then bound the resulting geometric sums by the chord inequality and a harmonic sum. This is the
classical Fourier proof; see Montgomery and Vaughan, *Multiplicative Number Theory I: Classical
Theory*, Chapter 9, Theorem 9.18.
-/

public section

open Finset ZMod
open scoped Real

namespace DirichletCharacter

variable {N : ℕ} [NeZero N]

private lemma two_div_norm_stdAddChar_sub_one_le (k : ZMod N) (hk : k ≠ 0) :
    2 / ‖ZMod.stdAddChar k - 1‖ ≤
      (N : ℝ) / 2 * ((k.val : ℝ)⁻¹ + ((-k).val : ℝ)⁻¹) := by
  have : NeZero k := ⟨hk⟩
  have hkpos : (0 : ℝ) < k.val := Nat.cast_pos.mpr (ZMod.val_pos.mpr hk)
  have hnegpos : (0 : ℝ) < (-k).val := Nat.cast_pos.mpr (ZMod.val_pos.mpr (neg_ne_zero.mpr hk))
  have hm : (0 : ℝ) < min (k.val : ℝ) ((-k).val : ℝ) := lt_min hkpos hnegpos
  have hc := ZMod.le_norm_stdAddChar_sub_one k
  rw [ZMod.valMinAbs_natAbs_eq_min, ← ZMod.val_neg_of_ne_zero k, Nat.cast_min] at hc
  calc
    2 / ‖ZMod.stdAddChar k - 1‖ ≤
        2 / (4 * min (k.val : ℝ) ((-k).val : ℝ) / N) :=
      div_le_div_of_nonneg_left (by norm_num)
        (div_pos (mul_pos (by norm_num) hm) (Nat.cast_pos.mpr (NeZero.pos N))) hc
    _ = (N : ℝ) / 2 * (min (k.val : ℝ) ((-k).val : ℝ))⁻¹ := by
      field_simp
      ring
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      rcases le_total (k.val : ℝ) ((-k).val : ℝ) with h | h
      · rw [min_eq_left h]
        exact le_add_of_nonneg_right (by positivity)
      · rw [min_eq_right h]
        exact le_add_of_nonneg_left (by positivity)

private lemma norm_phase_sum_le (a k : ZMod N) (H : ℕ)
    (hk : k ≠ 0) :
    ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ ≤
      2 / ‖stdAddChar k - 1‖ := by
  have hz : stdAddChar k ≠ 1 := by
    intro h
    apply hk
    apply injective_stdAddChar
    simpa only [AddChar.map_zero_eq_one] using h
  have heq : ∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N))) =
      stdAddChar (k * a) * ∑ j ∈ range H, (stdAddChar k) ^ j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    simp only [mul_add, AddChar.map_add_eq_mul]
    congr 1
    simpa only [nsmul_eq_mul, mul_comm] using
      (stdAddChar (N := N)).map_nsmul_eq_pow j k
  rw [heq, norm_mul, ZMod.stdAddChar_apply, Circle.norm_coe, one_mul, geom_sum_eq hz, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc ‖stdAddChar k ^ H - 1‖ ≤ ‖stdAddChar k ^ H‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by
      simp only [norm_pow, ZMod.stdAddChar_apply, Circle.norm_coe, one_pow, norm_one]
      norm_num

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

private lemma sum_inv_val_le :
    ∑ k ∈ univ.erase (0 : ZMod N), (k.val : ℝ)⁻¹ ≤ 1 + Real.log N := by
  have hall : ∑ k : ZMod N, (k.val : ℝ)⁻¹ = ∑ j ∈ range N, (j : ℝ)⁻¹ := by
    rw [← Fin.sum_univ_eq_sum_range]
    symm
    simpa only [RingEquiv.toEquiv_eq_coe, RingEquiv.coe_toEquiv,
      ZMod.finEquiv_apply, ZMod.val_natCast_of_lt, Fin.is_lt] using
      (ZMod.finEquiv N).toEquiv.sum_comp (fun k ↦ (k.val : ℝ)⁻¹)
  have hh : ∑ j ∈ range N, (j : ℝ)⁻¹ ≤ (harmonic N : ℝ) := by
    rw [sum_range_eq_add_Ico _ (NeZero.pos N), harmonic_eq_sum_Icc]
    simp only [Nat.cast_zero, _root_.inv_zero, zero_add, Rat.cast_sum, Rat.cast_inv,
      Rat.cast_natCast]
    exact sum_le_sum_of_subset_of_nonneg Ico_subset_Icc_self fun j _ _ ↦ by positivity
  have he : ∑ k ∈ univ.erase (0 : ZMod N), (k.val : ℝ)⁻¹ =
      ∑ k : ZMod N, (k.val : ℝ)⁻¹ := by
    rw [← sum_erase_add _ _ (mem_univ (0 : ZMod N))]
    simp
  rw [he, hall]
  exact hh.trans (harmonic_le_one_add_log N)

private lemma sum_norm_phase_le (a : ZMod N) (H : ℕ) :
    ∑ k ∈ univ.erase (0 : ZMod N),
        ‖∑ j ∈ range H, stdAddChar (k * (a + (j : ZMod N)))‖ ≤
      N * (1 + Real.log N) := by
  have hneg : ∑ k ∈ univ.erase (0 : ZMod N), ((-k).val : ℝ)⁻¹ =
      ∑ k ∈ univ.erase (0 : ZMod N), (k.val : ℝ)⁻¹ := by
    apply sum_equiv (Equiv.neg (ZMod N))
    · intro k
      simp only [mem_erase, mem_univ, and_true, Equiv.neg_apply, neg_ne_zero]
    · intro k _
      rfl
  calc
    _ ≤ ∑ k ∈ univ.erase (0 : ZMod N),
        (N : ℝ) / 2 * ((k.val : ℝ)⁻¹ + ((-k).val : ℝ)⁻¹) := by
      apply sum_le_sum
      intro k hk
      exact (norm_phase_sum_le a k H (mem_erase.mp hk).1).trans
        (two_div_norm_stdAddChar_sub_one_le k (mem_erase.mp hk).1)
    _ = (N : ℝ) * ∑ k ∈ univ.erase (0 : ZMod N), (k.val : ℝ)⁻¹ := by
      rw [← mul_sum, sum_add_distrib, hneg]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left sum_inv_val_le (Nat.cast_nonneg N)

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
      exact mul_le_mul_of_nonneg_left (sum_norm_phase_le a H) (by positivity)
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

end DirichletCharacter
