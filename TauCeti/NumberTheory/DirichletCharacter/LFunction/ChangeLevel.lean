/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.PrimeFactors.Bounds

/-!
# Uniform bounds for deleted Euler factors

Raising the level of a Dirichlet character deletes finitely many Euler factors. On every
half-plane `Re(s) ≥ δ > 0`, the correction and its reciprocal are bounded by `C N ^ ε`,
for any `ε > 0`, uniformly over the characters, levels and points in that half-plane.
Thus passage between an imprimitive character and its primitive character costs an arbitrarily
small power of the ambient level. This applies in particular to products of primitive quadratic
characters at their common level, including primes dividing both conductors.

The factors are nonzero on `Re(s) > 0`, so this passage also preserves zeros there. At `s = 1`
the L-function comparison requires nonprincipal characters, as in the native continuation API.

The exact identity is Mathlib's `DirichletCharacter.LFunction_changeLevel`,
by David Loeffler and Michael Stoll.
For the elementary finite-product estimates see Davenport, *Multiplicative Number Theory*,
the treatment of imprimitive characters and Siegel's theorem.
-/

public section

open Finset Complex

namespace DirichletCharacter

private theorem norm_mul_prime_cpow_le {M p : ℕ} (χ : DirichletCharacter ℂ M)
    (hp : p.Prime) {δ : ℝ} (hδ : 0 < δ) {s : ℂ} (hs : δ ≤ s.re) :
    ‖χ p * (p : ℂ) ^ (-s)‖ ≤ (2 : ℝ) ^ (-δ) := by
  rw [norm_mul, norm_natCast_cpow_of_pos hp.pos, neg_re]
  calc
    ‖χ p‖ * (p : ℝ) ^ (-s.re) ≤ (p : ℝ) ^ (-s.re) :=
      mul_le_of_le_one_left (by positivity) (χ.norm_le_one p)
    _ ≤ (p : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (by linarith)
    _ ≤ (2 : ℝ) ^ (-δ) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hp.two_le) (by linarith)

/-- Deleted Euler factors have no zeros in the open right half-plane, for arbitrary complex
Dirichlet characters, including principal ones. -/
theorem prod_one_sub_mul_prime_cpow_ne_zero {M N : ℕ} (χ : DirichletCharacter ℂ M)
    {s : ℂ} (hs : 0 < s.re) :
    (∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))) ≠ 0 := by
  refine prod_ne_zero_iff.2 fun p hp ↦ ?_
  have h := (norm_mul_prime_cpow_le χ (Nat.prime_of_mem_primeFactors hp) hs le_rfl).trans_lt
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hs))
  exact sub_ne_zero.mpr fun he ↦ by rw [← he, norm_one] at h; exact (lt_self_iff_false 1).mp h

/-- On a fixed closed right half-plane, the deleted Euler product and its reciprocal cost at
most an arbitrarily small power of the ambient level. The same constant works for every
character and every level. -/
theorem exists_norm_prod_one_sub_mul_prime_cpow_le_rpow {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ A > 0, ∀ (M N : ℕ), N ≠ 0 → ∀ (χ : DirichletCharacter ℂ M) (s : ℂ), δ ≤ s.re →
      ‖∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s))‖ ≤ A * (N : ℝ) ^ ε ∧
      ‖(∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)))⁻¹‖ ≤ A * (N : ℝ) ^ ε := by
  let r : ℝ := 2 ^ (-δ)
  have hr0 : 0 ≤ r := by positivity
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  let K := max (1 + r) (1 - r)⁻¹
  have hK : 1 ≤ K := le_trans (by linarith) (le_max_left _ _)
  obtain ⟨A, hA, hbound⟩ := TauCeti.exists_pow_card_primeFactors_le_mul_rpow hK hε
  refine ⟨A, hA, fun M N hN χ s hs ↦ ?_⟩
  have hlocal (p : ℕ) (hp : p ∈ N.primeFactors) :
      ‖1 - χ p * (p : ℂ) ^ (-s)‖ ≤ K ∧ ‖(1 - χ p * (p : ℂ) ^ (-s))⁻¹‖ ≤ K := by
    have hz := norm_mul_prime_cpow_le χ (Nat.prime_of_mem_primeFactors hp) hδ hs
    have hlo : 1 - r ≤ ‖1 - χ p * (p : ℂ) ^ (-s)‖ := by
      have := norm_sub_norm_le (1 : ℂ) (χ p * (p : ℂ) ^ (-s))
      simp only [norm_one] at this
      linarith
    constructor
    · have hu := norm_sub_le (1 : ℂ) (χ p * (p : ℂ) ^ (-s))
      simp only [norm_one] at hu
      have hu' : ‖1 - χ p * (p : ℂ) ^ (-s)‖ ≤ 1 + r := by linarith
      exact hu'.trans (le_max_left _ _)
    · rw [norm_inv]
      exact (inv_anti₀ (by linarith) hlo).trans (le_max_right _ _)
  constructor
  · rw [norm_prod]
    exact (prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun p hp ↦ (hlocal p hp).1)).trans
      (by simpa using hbound N hN)
  · rw [← prod_inv_distrib, norm_prod]
    exact (prod_le_prod₀ (fun _ _ ↦ norm_nonneg _) (fun p hp ↦ (hlocal p hp).2)).trans
      (by simpa using hbound N hN)

/-- Raising the level preserves the zeros of the continued L-function in the open right
half-plane. At the possible pole `1`, require the original character to be nonprincipal. -/
@[simp] theorem LFunction_changeLevel_eq_zero_iff {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ} (hs : 0 < s.re)
    (h : χ ≠ 1 ∨ s ≠ 1) :
    (changeLevel hMN χ).LFunction s = 0 ↔ χ.LFunction s = 0 := by
  rw [LFunction_changeLevel hMN χ h, mul_eq_zero]
  simp [prod_one_sub_mul_prime_cpow_ne_zero (N := N) χ hs]

/-- Uniform comparison of the L-functions before and after a level change in either direction.
In particular it applies to the primitive character at its conductor and the original character
at its ambient level. -/
theorem exists_norm_LFunction_changeLevel_le_rpow {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ A > 0, ∀ (M N : ℕ) [NeZero M] [NeZero N] (χ : DirichletCharacter ℂ M)
      (hMN : M ∣ N) (s : ℂ), δ ≤ s.re → (χ ≠ 1 ∨ s ≠ 1) →
      ‖(changeLevel hMN χ).LFunction s‖ ≤ A * (N : ℝ) ^ ε * ‖χ.LFunction s‖ ∧
      ‖χ.LFunction s‖ ≤ A * (N : ℝ) ^ ε * ‖(changeLevel hMN χ).LFunction s‖ := by
  obtain ⟨A, hA, hb⟩ := exists_norm_prod_one_sub_mul_prime_cpow_le_rpow hδ hε
  refine ⟨A, hA, fun M N _ _ χ hMN s hs h ↦ ?_⟩
  obtain ⟨hup, hinv⟩ := hb M N (NeZero.ne N) χ s hs
  have he := LFunction_changeLevel hMN χ h
  have hne := prod_one_sub_mul_prime_cpow_ne_zero (N := N) χ (hδ.trans_le hs)
  constructor
  · rw [he, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hup (norm_nonneg _)
  · have hi : χ.LFunction s = (changeLevel hMN χ).LFunction s *
        (∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)))⁻¹ := by
      rw [he, mul_assoc, mul_inv_cancel₀ hne, mul_one]
    rw [hi, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hinv (norm_nonneg _)

end DirichletCharacter
