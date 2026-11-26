/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.MulChar.Duality
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.Quadratic.LocalFactor

/-!
# A uniform lower bound near one for quadratic Dirichlet L-functions

When the prime divisors of the level range over a fixed finite set, quadratic Dirichlet
characters have bounded conductor. Nonvanishing at `1` in the resulting finite family,
together with a lower bound for the deleted Euler factors, gives a common positive lower bound
on a neighbourhood of `1`. For principal characters the bound is for the L-function with its
pole removed and divided by `s`.

This is the finite-family input to the near-one logarithmic-derivative estimate in
lsernau/grh-lean (revision `72fead1`, `New.eventually_norm_logDeriv_entireL_le_near_one`).
Unlike descent to a fixed level in a modulus tower, the conductor and Euler-factor argument
also allows the prime support to vary within the given set.
-/

public section

open Finset Filter
open scoped Topology

namespace DirichletCharacter

/-- With prescribed prime support `S`, the conductor of a quadratic character is at most
`∏ p ∈ S.filter Nat.Prime, p ^ 3`. -/
private theorem conductor_le_prod_cube_of_sq_eq_one {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ^ 2 = 1) {S : Finset ℕ} (hS : N.primeFactors ⊆ S) :
    χ.conductor ≤ ∏ p ∈ S.filter Nat.Prime, p ^ 3 := by
  have hsub : χ.conductor.primeFactors ⊆ S.filter Nat.Prime := by
    intro p hp
    exact mem_filter.mpr ⟨hS (Nat.primeFactors_mono χ.conductor_dvd_level (NeZero.ne N) hp),
      Nat.prime_of_mem_primeFactors hp⟩
  refine (Nat.prod_primeFactors_pow_factorization χ.conductor_ne_zero).le.trans ?_
  refine (prod_le_prod fun p hp ↦ ?_).trans
    (prod_le_prod_of_subset_of_one_le hsub fun p hp _ ↦
      Nat.one_le_pow _ _ (mem_filter.mp hp).2.pos)
  have hp' := Nat.prime_of_mem_primeFactors hp
  apply Nat.pow_le_pow_right hp'.pos
  by_cases h : p = 2
  · subst p
    rcases χ.factorization_two_conductor_eq_zero_or_two_or_three_of_sq_eq_one hχ with h | h | h <;>
      omega
  · exact (χ.factorization_conductor_le_one_of_sq_eq_one hχ hp' h).trans (by decide)

open Classical in
/-- A common positive lower bound for pole-removed L-functions at all levels up to `B`,
in a neighbourhood of `1`. -/
private theorem exists_eventually_pos_le_norm_LFunction_of_le (B : ℕ) :
    ∃ c > (0 : ℝ), ∀ᶠ s : ℂ in 𝓝 1, ∀ (n : ℕ) [NeZero n], n ≤ B →
      ∀ χ : DirichletCharacter ℂ n,
        c ≤ ‖if χ = 1 then LFunctionTrivChar₁ n s else χ.LFunction s‖ := by
  let ι := ↥(Icc 1 B)
  have (n : ι) : NeZero n.val := ⟨(Nat.one_le_iff_ne_zero.mp (mem_Icc.mp n.property).1)⟩
  let F (n : ι) (χ : DirichletCharacter ℂ n.val) (s : ℂ) : ℂ :=
    if χ = 1 then LFunctionTrivChar₁ n.val s else χ.LFunction s
  have hc (n : ι) (χ : DirichletCharacter ℂ n.val) : Continuous (F n χ) := by
    by_cases h : χ = 1
    · simpa [F, h] using (differentiable_LFunctionTrivChar₁ n.val).continuous
    · simpa [F, h] using (differentiable_LFunction h).continuous
  have hn (n : ι) (χ : DirichletCharacter ℂ n.val) : F n χ 1 ≠ 0 := by
    by_cases h : χ = 1
    · simpa [F, h] using LFunctionTrivChar₁_apply_one_ne_zero n.val
    · simpa [F, h] using LFunction_apply_one_ne_zero h
  have hm (n : ι) (χ : DirichletCharacter ℂ n.val) :
      ∀ᶠ c : ℝ in 𝓝 (0 : ℝ), c < ‖F n χ 1‖ := eventually_lt_nhds (norm_pos_iff.mpr (hn n χ))
  obtain ⟨c, hc', hmin⟩ : ∃ c : ℝ, 0 < c ∧ ∀ n χ, c < ‖F n χ 1‖ := by
    have h : ∀ᶠ c : ℝ in 𝓝[Set.Ioi 0] 0, ∀ n χ, c < ‖F n χ 1‖ :=
      ((eventually_all.mpr fun n ↦ eventually_all.mpr (hm n))).filter_mono nhdsWithin_le_nhds
    exact (eventually_mem_nhdsWithin.and h).exists
  refine ⟨c, hc', ?_⟩
  have hnear : ∀ᶠ s : ℂ in 𝓝 1, ∀ n χ, c < ‖F n χ s‖ :=
    eventually_all.mpr fun n ↦ eventually_all.mpr fun χ ↦
      (hc n χ).continuousAt.norm.tendsto.eventually_const_lt (hmin n χ)
  filter_upwards [hnear] with s hs n inst hn' χ
  exact (hs ⟨n, mem_Icc.mpr ⟨NeZero.pos n, hn'⟩⟩ χ).le

open Classical in
/-- For a fixed finite set of primes `S`, the regular L-functions of all complex characters
whose square is principal and whose level is supported in `S` are uniformly bounded away from
zero on a common neighbourhood of `1`. In the principal case the regular function is the
pole-removed `LFunctionTrivChar₁` divided by `s`; otherwise it is the ordinary L-function. -/
theorem exists_pos_le_norm_regularLFunction_of_sq_eq_one (S : Finset ℕ) :
    ∃ c > (0 : ℝ), ∀ᶠ s : ℂ in 𝓝 1, ∀ (N : ℕ) [NeZero N], N.primeFactors ⊆ S →
      ∀ χ : DirichletCharacter ℂ N, χ ^ 2 = 1 →
        c ≤ ‖if χ = 1 then LFunctionTrivChar₁ N s / s else χ.LFunction s‖ := by
  let B := ∏ p ∈ S.filter Nat.Prime, p ^ 3
  let K := (1 - (2 : ℝ) ^ (-(1 / 2 : ℝ))) ^ S.card
  have hK : 0 < K := by
    apply pow_pos
    exact sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))
  obtain ⟨c, hc, hnear⟩ := exists_eventually_pos_le_norm_LFunction_of_le B
  have hB : 1 ≤ B := one_le_prod fun p hp ↦ Nat.one_le_pow _ _ (mem_filter.mp hp).2.pos
  have hre : ∀ᶠ s : ℂ in 𝓝 1, (1 / 2 : ℝ) < s.re :=
    Complex.continuous_re.continuousAt.tendsto.eventually_const_lt (by norm_num)
  have hnorm : ∀ᶠ s : ℂ in 𝓝 1, ‖s‖ < 2 :=
    continuous_norm.continuousAt.tendsto.eventually_lt_const (by norm_num)
  refine ⟨c * K / 2, by positivity, ?_⟩
  filter_upwards [hnear, hre, hnorm] with s hs hsre hsnorm N inst hS χ hχ
  by_cases h : χ = 1
  · rw [ite_eq_left h, norm_div, LFunctionTrivChar₁_eq_mul_eulerFactors, norm_mul]
    have hnormpos : 0 < ‖s‖ := norm_pos_iff.mpr (fun he ↦ by norm_num [he] at hsre)
    have h₁ : c ≤ ‖LFunctionTrivChar₁ 1 s‖ := by simpa using hs 1 hB 1
    have h₂ : K ≤ ‖∏ p ∈ N.primeFactors, (1 - (p : ℂ) ^ (-s))‖ := by
      simpa [K, MulChar.one_apply (isUnit_of_subsingleton _)] using
        one_sub_rpow_pow_le_norm_eulerFactors (N := N) (1 : DirichletCharacter ℂ 1)
          (card_le_card hS) (by norm_num : (0 : ℝ) ≤ 1 / 2) hsre.le
    gcongr
  · have : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hprim : χ.primitiveCharacter ≠ 1 := mt (χ.primitiveCharacter_eq_one_iff).mp h
    have h₁ := hs χ.conductor (χ.conductor_le_prod_cube_of_sq_eq_one hχ hS) χ.primitiveCharacter
    rw [ite_eq_right hprim] at h₁
    have h₂ := one_sub_rpow_pow_le_norm_eulerFactors χ.primitiveCharacter (card_le_card hS)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) hsre.le
    rw [ite_eq_right h, ← χ.changeLevel_primitiveCharacter, LFunction_changeLevel _ _ (.inl hprim),
      norm_mul]
    exact (div_le_self (by positivity) (by norm_num)).trans
      (mul_le_mul h₁ h₂ hK.le (norm_nonneg _))

end DirichletCharacter
