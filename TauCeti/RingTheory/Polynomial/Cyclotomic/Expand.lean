/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# Cyclotomic expansion and derivative size

When every prime divisor of a positive integer `m` divides `n`, the cyclotomic polynomial
`Φ_(n*m)` is `Φ_n(X^m)`. At a primitive root of order `n*m`, the norm of its derivative is
`m` times the norm of `Φ_n′` at the corresponding root of order `n`. Thus the logarithmic
error after removing the scale `m` is bounded using only the roots at level `n`.

The derivative estimate is the cyclotomic part of the different estimate
`New.Parameters.exists_abs_log_le_and_apply_deltaE_eq` in
`grh/src/New/Derivatives/Field/ChosenPlaces.lean` of <https://github.com/lsernau/grh-lean> (`72fead1`).
-/

public section

namespace TauCeti

open Polynomial

/-- Expanding `Φ_n` by a nonzero factor supported on the primes of `n` gives `Φ_(n*m)`.
This extends `cyclotomic_expand_eq_cyclotomic` from one prime to a product of primes. -/
theorem cyclotomic_expand_eq_cyclotomic_of_primeFactors_subset (R : Type*) [CommRing R]
    {n m : ℕ} (hm : m ≠ 0) (h : m.primeFactors ⊆ n.primeFactors) :
    expand R m (cyclotomic n R) = cyclotomic (n * m) R := by
  induction m using Nat.recOnMul generalizing n with
  | zero => exact (hm rfl).elim
  | one => simp
  | prime p hp =>
    exact cyclotomic_expand_eq_cyclotomic hp
      (Nat.dvd_of_mem_primeFactors (h hp.mem_primeFactors_self)) R
  | mul a b ha hb =>
    have ha₀ : a ≠ 0 := fun e ↦ hm (by simp [e])
    have hb₀ : b ≠ 0 := fun e ↦ hm (by simp [e])
    rw [Nat.primeFactors_mul ha₀ hb₀, Finset.union_subset_iff] at h
    have h' : a.primeFactors ⊆ (n * b).primeFactors := by
      intro p hp
      have hpn := h.1 hp
      have hn := (Nat.mem_primeFactors.mp hpn).2.2
      exact Nat.primeFactors_mono (dvd_mul_right n b) (mul_ne_zero hn hb₀) hpn
    rw [expand_mul, hb hb₀ h.2, ha ha₀ h', mul_right_comm, mul_assoc]

/-- On the unit circle the derivative of `Φ_(n*m)` has norm `m` times the norm of
`Φ_n′` at `z ^ m`, when `m` introduces no new prime divisors. -/
theorem norm_eval_derivative_cyclotomic_mul {n m : ℕ} {z : ℂ}
    (h : m.primeFactors ⊆ n.primeFactors) (hz : ‖z‖ = 1) :
    ‖(cyclotomic (n * m) ℂ).derivative.eval z‖ =
      (m : ℝ) * ‖(cyclotomic n ℂ).derivative.eval (z ^ m)‖ := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rw [← cyclotomic_expand_eq_cyclotomic_of_primeFactors_subset ℂ hm h, derivative_expand]
  simp [expand_eval, hz, mul_comm]

/-- At a primitive root of order `n*m`, the norm of the derivative is `m` times a positive
factor whose absolute logarithm is bounded by a sum over the primitive roots of order `n`. -/
theorem exists_pos_norm_eval_derivative_cyclotomic_mul {n m : ℕ} {z : ℂ}
    (h₀ : n * m ≠ 0) (h : m.primeFactors ⊆ n.primeFactors) (hz : IsPrimitiveRoot z (n * m)) :
    ∃ A : ℝ, 0 < A ∧ ‖(cyclotomic (n * m) ℂ).derivative.eval z‖ = (m : ℝ) * A ∧
      |Real.log A| ≤ ∑ w ∈ primitiveRoots n ℂ, |Real.log ‖(cyclotomic n ℂ).derivative.eval w‖| := by
  have hm : m ≠ 0 := right_ne_zero_of_mul h₀
  have hn : 0 < n := Nat.pos_of_ne_zero (left_ne_zero_of_mul h₀)
  have hw : IsPrimitiveRoot (z ^ m) n := by
    simpa [Nat.mul_div_cancel _ hm.bot_lt] using hz.pow_of_dvd hm (dvd_mul_left m n)
  have : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  have hne := (separable_cyclotomic n ℂ).eval₂_derivative_ne_zero (RingHom.id ℂ)
    (by simpa only [eval₂_id, IsRoot.def] using hw.isRoot_cyclotomic hn)
  refine ⟨‖(cyclotomic n ℂ).derivative.eval (z ^ m)‖, ?_,
    norm_eval_derivative_cyclotomic_mul h (hz.norm'_eq_one h₀), ?_⟩
  · exact norm_pos_iff.mpr (by simpa only [eval₂_id] using hne)
  · exact Finset.single_le_sum (f := fun w ↦ |Real.log ‖(cyclotomic n ℂ).derivative.eval w‖|)
      (fun _ _ ↦ abs_nonneg _) ((mem_primitiveRoots hn).mpr hw)

end TauCeti
