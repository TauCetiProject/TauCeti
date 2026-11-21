/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Polynomial sequences in additive abelian groups

* `TauCeti.poly_sub_shift`: forward finite-difference identity for a degree-`s` polynomial.
* `TauCeti.poly_comp_affine_int`: affine reparametrization `Q * n + R` of a polynomial.
* `TauCeti.poly_comp_affine_kill_high`: passing to step `D` killing high-degree torsion terms.
-/

public section

open Finset

namespace TauCeti

variable {G : Type*} [AddCommGroup G]

/-- Finite-difference identity for a degree-`s` polynomial sequence in an additive abelian
group. -/
theorem poly_sub_shift (s h : ℕ) (α : ℕ → G) (n : ℕ) :
    (∑ j ∈ range (s + 1), (n + h) ^ j • α j) - ∑ j ∈ range (s + 1), n ^ j • α j =
      ∑ r ∈ range s, n ^ r •
        ∑ j ∈ Ico (r + 1) (s + 1), (h ^ (j - r) * j.choose r) • α j := by
  rw [← sum_sub_distrib]
  simp_rw [(fun j : ℕ ↦ by
    rw [add_pow, sum_range_succ, Nat.sub_self, pow_zero, mul_one, Nat.choose_self, Nat.cast_one,
      mul_one, add_nsmul, add_sub_cancel_right, sum_smul]
    exact sum_congr rfl fun r _ ↦ by rw [Nat.cast_id, mul_assoc, mul_nsmul'] :
    ∀ j : ℕ, (n + h) ^ j • α j - n ^ j • α j =
      ∑ r ∈ range j, n ^ r • ((h ^ (j - r) * j.choose r) • α j))]
  rw [sum_range_sum_range_lt (s + 1) (fun r j ↦ n ^ r • ((h ^ (j - r) * j.choose r) • α j)),
    sum_range_succ, Ico_self, sum_empty, add_zero]
  exact sum_congr rfl fun r _ ↦ smul_sum.symm

/-- Affine reparametrization of an integer-indexed polynomial in an additive abelian group. -/
theorem poly_comp_affine_int (s : ℕ) (c : ℕ → G) (Q R n : ℤ) :
    ∑ j ∈ range (s + 1), (Q * n + R) ^ j • c j =
      ∑ t ∈ range (s + 1), n ^ t •
        ∑ j ∈ Ico t (s + 1), (Q ^ t * R ^ (j - t) * (j.choose t : ℤ)) • c j := by
  simp_rw [(fun j : ℕ ↦ by
    rw [add_pow, sum_smul]
    exact sum_congr rfl fun t _ ↦ by rw [mul_pow, ← mul_zsmul]; congr 1; ring :
    ∀ j : ℕ, (Q * n + R) ^ j • c j =
      ∑ t ∈ range (j + 1), n ^ t • ((Q ^ t * R ^ (j - t) * (j.choose t : ℤ)) • c j))]
  rw [sum_range_sum_range_le (s + 1)]; exact sum_congr rfl fun t _ ↦ smul_sum.symm

/-- Passing to an arithmetic progression of step `D` annihilating all high-degree torsion
coefficients `c j` (`j₀ < j ≤ s`) collapses an affine reparametrization of a degree-`s` polynomial
to a degree-`j₀` polynomial with leading coefficient `(Q * D) ^ j₀ • c j₀`. -/
theorem poly_comp_affine_kill_high {s j₀ D : ℕ} (hj₀_ge : 1 ≤ j₀) (hj₀_le : j₀ ≤ s) (c : ℕ → G)
    (hDkill : ∀ j ∈ Ioc j₀ s, (D : ℤ) • c j = 0) (Q R : ℤ) (r : ℕ) :
    ∃ γ : ℕ → G, γ j₀ = (Q * (D : ℤ)) ^ j₀ • c j₀ ∧
      ∀ u : ℕ, ∑ j ∈ range (s + 1), (Q * ((D * u + r : ℕ) : ℤ) + R) ^ j • c j =
        ∑ t ∈ range (j₀ + 1), u ^ t • γ t := by
  let Q' : ℤ := Q * (D : ℤ); let R' : ℤ := Q * (r : ℤ) + R
  let γ : ℕ → G := fun t ↦ ∑ j ∈ Ico t (s + 1), (Q' ^ t * R' ^ (j - t) * (j.choose t : ℤ)) • c j
  have hkill (t j : ℕ) (ht : 1 ≤ t) (hj : j ∈ Ioc j₀ s) :
      (Q' ^ t * R' ^ (j - t) * (j.choose t : ℤ)) • c j = 0 := by
    rw [(by rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel ht] :
        Q' ^ t = (Q ^ t * (D : ℤ) ^ (t - 1)) * (D : ℤ)),
      mul_assoc, mul_assoc, mul_comm (D : ℤ), ← mul_assoc, mul_zsmul, hDkill j hj, smul_zero]
  refine ⟨γ, ?_, fun u ↦ ?_⟩
  · have hsplit : Ico j₀ (s + 1) = insert j₀ (Ioc j₀ s) := by
      ext j; simp only [mem_Ico, mem_insert, mem_Ioc]; omega
    simp only [γ, Q', hsplit, sum_insert (by simp : j₀ ∉ Ioc j₀ s),
      sum_eq_zero fun j hj ↦ hkill j₀ j hj₀_ge hj, add_zero, Nat.sub_self, pow_zero, mul_one,
      Nat.choose_self, Nat.cast_one]
  · rw [(by simp only [Q', R']; push_cast; ring :
        Q * ((D * u + r : ℕ) : ℤ) + R = Q' * (u : ℤ) + R'),
      poly_comp_affine_int, ← sum_range_add_sum_Ico _ (by omega : j₀ + 1 ≤ s + 1),
      sum_eq_zero (s := Ico (j₀ + 1) (s + 1)) fun t ht ↦ ?_, add_zero]
    · exact sum_congr rfl fun t _ ↦ by rw [← Int.natCast_pow, natCast_zsmul]
    · have ht_gt : j₀ < t := (mem_Ico.mp ht).1
      rw [sum_eq_zero fun j hj ↦ hkill t j (by omega)
        (mem_Ioc.mpr ⟨by have := (mem_Ico.mp hj).1; omega, Nat.lt_succ_iff.mp (mem_Ico.mp hj).2⟩),
        smul_zero]

end TauCeti
