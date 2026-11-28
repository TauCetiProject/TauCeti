/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Polynomial sequences in additive abelian groups

* `TauCeti.fwdDiff_sum_range_pow_nsmul`: forward finite-difference identity for a degree-`s`
  polynomial sequence.
* `TauCeti.sum_range_mul_add_pow_zsmul`: affine reparametrization `Q * n + R` of a polynomial
  sequence.
* `TauCeti.exists_sum_range_mul_add_pow_zsmul_eq_of_forall_zsmul_eq_zero`: passing to a step `q`
  annihilating the higher torsion coefficients, yielding an expansion of degree at most `j₀`.
-/

public section

open Finset

namespace TauCeti

variable {G : Type*} [AddCommGroup G]

/-- Per-term binomial difference `(n + h) ^ j • a - n ^ j • a` expanded in powers of `n`. -/
private theorem add_pow_nsmul_sub_nsmul (n h j : ℕ) (a : G) :
    (n + h) ^ j • a - n ^ j • a = ∑ r ∈ range j, n ^ r • ((h ^ (j - r) * j.choose r) • a) := by
  rw [add_pow, sum_range_succ]
  simp [add_nsmul, sum_smul, mul_assoc, mul_nsmul']

/-- Forward finite-difference identity for a degree-`s` polynomial sequence in an additive abelian
group. -/
theorem fwdDiff_sum_range_pow_nsmul (s h : ℕ) (α : ℕ → G) (n : ℕ) :
    fwdDiff h (fun m : ℕ ↦ ∑ j ∈ range (s + 1), m ^ j • α j) n =
      ∑ r ∈ range s, n ^ r • ∑ j ∈ Ico (r + 1) (s + 1), (h ^ (j - r) * j.choose r) • α j := by
  rw [fwdDiff, ← sum_sub_distrib]
  simp_rw [add_pow_nsmul_sub_nsmul, ← Nat.Ico_zero_eq_range]
  rw [(sum_Ico_Ico_comm' 0 (s + 1) fun r j ↦ n ^ r • ((h ^ (j - r) * j.choose r) • α j)).symm]
  simp_rw [Nat.Ico_zero_eq_range]; rw [sum_range_succ, Ico_self, sum_empty, add_zero]
  exact sum_congr rfl fun r _ ↦ smul_sum.symm

/-- Affine reparametrization of an integer-indexed polynomial in an additive abelian group. -/
theorem sum_range_mul_add_pow_zsmul (s : ℕ) (c : ℕ → G) (Q R n : ℤ) :
    ∑ j ∈ range (s + 1), (Q * n + R) ^ j • c j = ∑ t ∈ range (s + 1), n ^ t •
      ∑ j ∈ Ico t (s + 1), (Q ^ t * R ^ (j - t) * (j.choose t : ℤ)) • c j := by
  simp_rw [(fun j : ℕ ↦ by
    rw [add_pow, sum_smul]
    exact sum_congr rfl fun t _ ↦ by rw [mul_pow, ← mul_zsmul]; congr 1; ring :
    ∀ j : ℕ, (Q * n + R) ^ j • c j =
      ∑ t ∈ range (j + 1), n ^ t • ((Q ^ t * R ^ (j - t) * (j.choose t : ℤ)) • c j)),
    ← Nat.Ico_zero_eq_range]
  rw [(sum_Ico_Ico_comm 0 (s + 1) _).symm]; simp_rw [Nat.Ico_zero_eq_range]
  exact sum_congr rfl fun t _ ↦ smul_sum.symm

/-- Passing to a step `q : ℤ` annihilating all higher coefficients `c j` (`j₀ < j ≤ s`) gives
an expansion of the affine reparametrization `q * n + r` (`n : ℤ`) of degree at most `j₀`, with
coefficient `q ^ j₀ • c j₀` at index `j₀`. -/
theorem exists_sum_range_mul_add_pow_zsmul_eq_of_forall_zsmul_eq_zero {s j₀ : ℕ} (hj₀_ge : 1 ≤ j₀)
    (hj₀_le : j₀ ≤ s) (c : ℕ → G) {q : ℤ} (hqkill : ∀ j ∈ Ioc j₀ s, q • c j = 0) (r : ℤ) :
    ∃ γ : ℕ → G, γ j₀ = q ^ j₀ • c j₀ ∧ ∀ n : ℤ,
      ∑ j ∈ range (s + 1), (q * n + r) ^ j • c j = ∑ t ∈ range (j₀ + 1), n ^ t • γ t := by
  let γ : ℕ → G := fun t ↦ ∑ j ∈ Ico t (s + 1), (q ^ t * r ^ (j - t) * (j.choose t : ℤ)) • c j
  have hkill (t j : ℕ) (ht : 1 ≤ t) (hj : j ∈ Ioc j₀ s) :
      (q ^ t * r ^ (j - t) * (j.choose t : ℤ)) • c j = 0 := by
    obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le' ht
    rw [pow_succ, mul_right_comm (q ^ t) q, mul_right_comm _ q, mul_zsmul, hqkill j hj, smul_zero]
  refine ⟨γ, ?_, fun n ↦ ?_⟩
  · have hsplit : Ico j₀ (s + 1) = insert j₀ (Ioc j₀ s) := by
      ext j; simp only [mem_Ico, mem_insert, mem_Ioc]; omega
    simp only [γ, hsplit, sum_insert (by simp : j₀ ∉ Ioc j₀ s),
      sum_eq_zero fun j hj ↦ hkill j₀ j hj₀_ge hj, add_zero, Nat.sub_self, pow_zero, mul_one,
      Nat.choose_self, Nat.cast_one]
  · rw [sum_range_mul_add_pow_zsmul, ← sum_range_add_sum_Ico _ (by omega : j₀ + 1 ≤ s + 1),
      sum_eq_zero (s := Ico (j₀ + 1) (s + 1)) fun t ht ↦ ?_, add_zero]
    have ht_gt : j₀ < t := (mem_Ico.mp ht).1
    rw [sum_eq_zero fun j hj ↦ hkill t j (by omega)
      (mem_Ioc.mpr ⟨by have := (mem_Ico.mp hj).1; omega, Nat.lt_succ_iff.mp (mem_Ico.mp hj).2⟩),
      smul_zero]

end TauCeti
