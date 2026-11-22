/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.PrimeFactors.Bounds

import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.Analysis.SpecialFunctions.Pow.EulerFactor
import TauCeti.NumberTheory.LSeries.CompletedRiemannZeta

/-!
# Uniform bounds for deleted Euler factors

Raising the level of a Dirichlet character deletes finitely many Euler factors. On every
half-plane `Re(s) ≥ δ > 0`, the correction and its reciprocal are bounded by `C N ^ ε`,
for any `ε > 0`, uniformly over the characters, levels and points in that half-plane.
Thus passage between an imprimitive character and its primitive character costs an arbitrarily
small power of the ambient level. This applies in particular to products of primitive quadratic
characters at their common level, including primes dividing both conductors.

The factors are nonzero on `Re(s) > 0`, so order preservation
(`meromorphicOrderAt_LFunction_changeLevel`) holds throughout the open right half-plane,
including `χ = 1` at `s = 1`. By contrast, the L-function evaluation and logarithmic-derivative
identities and the `log N` bound on `Re(s) ≥ 1` exclude `χ = 1` at the pole `s = 1`, as in the
native continuation API.

The exact identity is Mathlib's `DirichletCharacter.LFunction_changeLevel`,
by David Loeffler and Michael Stoll.
For the elementary finite-product estimates see Davenport, *Multiplicative Number Theory*,
the treatment of imprimitive characters and Siegel's theorem.
-/

public section

open Finset Complex Filter
open scoped Topology

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

private theorem analyticAt_prod_one_sub_mul_prime_cpow {M N : ℕ} (χ : DirichletCharacter ℂ M)
    (s : ℂ) :
    AnalyticAt ℂ (fun z : ℂ ↦ ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z))) s := by
  refine Differentiable.analyticAt (Differentiable.fun_finsetProd fun p hp ↦ ?_) s
  have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_primeFactors hp).ne'
  fun_prop (disch := exact Or.inl hp0)

/-- Raising the level preserves the meromorphic order of the continued L-function in the open right
half-plane. No nonprincipality hypothesis is needed, since `LFunction_changeLevel` holds on a
punctured neighborhood of `1`. -/
theorem meromorphicOrderAt_LFunction_changeLevel {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ} (hs : 0 < s.re) :
    meromorphicOrderAt (changeLevel hMN χ).LFunction s = meromorphicOrderAt χ.LFunction s := by
  let P : ℂ → ℂ := fun z ↦ ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-z))
  have hev : ∀ᶠ z in 𝓝[≠] s, z ≠ (1 : ℂ) := by
    rcases eq_or_ne s 1 with rfl | hs1
    · exact self_mem_nhdsWithin
    · exact nhdsWithin_le_nhds (eventually_ne_nhds hs1)
  have heq : (changeLevel hMN χ).LFunction =ᶠ[𝓝[≠] s] P * χ.LFunction :=
    hev.mono fun z hz1 ↦ by
      rw [Pi.mul_apply, mul_comm]
      exact LFunction_changeLevel hMN χ (.inr hz1)
  rw [meromorphicOrderAt_congr heq]
  exact meromorphicOrderAt_mul_of_ne_zero (analyticAt_prod_one_sub_mul_prime_cpow χ s)
    (prod_one_sub_mul_prime_cpow_ne_zero (N := N) χ hs)

/-- The continued L-function of any principal Dirichlet character has a simple pole at `1`. -/
@[simp]
theorem meromorphicOrderAt_LFunction_one_at_one (q : ℕ) [NeZero q] :
    meromorphicOrderAt (1 : DirichletCharacter ℂ q).LFunction 1 = (-1 : ℤ) := by
  rw [← changeLevel_one (q.one_dvd),
    meromorphicOrderAt_LFunction_changeLevel (1 : DirichletCharacter ℂ 1) q.one_dvd
      (by norm_num),
    LFunction_modOne_eq, TauCeti.meromorphicOrderAt_riemannZeta_one]

/-- Raising the level adds precisely the logarithmic derivatives of its finitely many deleted
Euler factors wherever the higher-level L-function is nonzero, excluding `χ = 1` at `s = 1`. -/
theorem logDeriv_LFunction_changeLevel_sub {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ}
    (hL : (changeLevel hMN χ).LFunction s ≠ 0) (h : χ ≠ 1 ∨ s ≠ 1) :
    logDeriv (changeLevel hMN χ).LFunction s - logDeriv χ.LFunction s =
      ∑ p ∈ N.primeFactors, logDeriv (fun z : ℂ ↦ 1 - χ p * (p : ℂ) ^ (-z)) s := by
  let f (p : ℕ) (z : ℂ) : ℂ := 1 - χ p * (p : ℂ) ^ (-z)
  let P (z : ℂ) : ℂ := ∏ p ∈ N.primeFactors, f p z
  have heq : (changeLevel hMN χ).LFunction =ᶠ[𝓝 s] P * χ.LFunction := by
    rcases h with hχ | hs1
    · exact Eventually.of_forall fun z ↦ by
        rw [Pi.mul_apply, mul_comm]
        exact LFunction_changeLevel hMN χ (.inl hχ)
    · filter_upwards [eventually_ne_nhds hs1] with z hz
      rw [Pi.mul_apply, mul_comm]
      exact LFunction_changeLevel hMN χ (.inr hz)
  have hPχ : P s * χ.LFunction s ≠ 0 := fun hz ↦ hL (heq.eq_of_nhds.trans hz)
  have hP0 : P s ≠ 0 := (mul_ne_zero_iff.mp hPχ).1
  have hL0 : χ.LFunction s ≠ 0 := (mul_ne_zero_iff.mp hPχ).2
  have hf0 : ∀ p ∈ N.primeFactors, f p s ≠ 0 := Finset.prod_ne_zero_iff.mp hP0
  have hdf : ∀ p ∈ N.primeFactors, DifferentiableAt ℂ (f p) s := fun p hp ↦ by
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_primeFactors hp).ne'
    dsimp only [f]
    fun_prop (disch := exact Or.inl hp0)
  rw [(logDeriv_congr_nhds heq).eq_of_nhds, logDeriv_mul s hP0 hL0
    (DifferentiableAt.fun_finsetProd hdf) (differentiableAt_LFunction χ s h.symm),
    logDeriv_fun_prod hf0 hdf, add_sub_cancel_right]

/-- Raising the level changes the logarithmic derivative of a continued Dirichlet L-function on
`1 ≤ Re s`, excluding the principal-character pole `χ = 1` at `s = 1`, by at most `log N`. -/
theorem norm_logDeriv_LFunction_changeLevel_sub_le {M N : ℕ} [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hMN : M ∣ N) {s : ℂ} (hs : 1 ≤ s.re)
    (h : χ ≠ 1 ∨ s ≠ 1) :
    ‖logDeriv (changeLevel hMN χ).LFunction s - logDeriv χ.LFunction s‖ ≤ Real.log N := by
  have hchange_ne : changeLevel hMN χ ≠ 1 ∨ s ≠ 1 :=
    h.imp_left (by simpa only [ne_eq, changeLevel_eq_one_iff] using id)
  have hL : (changeLevel hMN χ).LFunction s ≠ 0 :=
    LFunction_ne_zero_of_one_le_re (changeLevel hMN χ) hchange_ne hs
  rw [logDeriv_LFunction_changeLevel_sub χ hMN hL h]
  calc
    ‖∑ p ∈ N.primeFactors, logDeriv (fun z : ℂ ↦ 1 - χ p * (p : ℂ) ^ (-z)) s‖
        ≤ ∑ p ∈ N.primeFactors, ‖logDeriv (fun z : ℂ ↦ 1 - χ p * (p : ℂ) ^ (-z)) s‖ :=
          norm_sum_le _ _
    _ ≤ ∑ p ∈ N.primeFactors, Real.log p := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        exact Complex.norm_logDeriv_one_sub_mul_ofReal_cpow_neg_le hp2 (χ.norm_le_one p) hs
    _ ≤ Real.log N := Nat.sum_primeFactors_log_le N

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
