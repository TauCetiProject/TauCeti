/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
import TauCeti.Analysis.SpecialFunctions.Complex.LogBounds

/-!
# Level changes of ordered Dirichlet Euler products

Raising the level of a Dirichlet character from `M` to a multiple `N` deletes the Euler
factors at primes dividing `N`. For a finite set of primes we prove the exact correction,
and for ordered cutoffs we identify the correction once the cutoff is at least `N`.
Primes already dividing `M` contribute the factor `1` automatically.

The correction is nonzero at `s = 1`, so convergence transports in both directions.
This also works when an arbitrary finite set of primes has already been omitted. For
nontrivial characters, Mathlib's `DirichletCharacter.LFunction_changeLevel` identifies the
corrected boundary value with the native `LFunction` at the raised level. Thus proving the
ordered Euler-product endpoint at one level proves it at every multiple of that level.
No convergence hypothesis is established here, and no unconditional product is asserted.

The finite-factor calculation follows the local calculation in Mathlib's
`DirichletCharacter.LSeries_changeLevel`. Nonvanishing of each boundary factor uses
`Complex.one_sub_div_natCast_ne_zero` and the native character bound `norm_le_one`.
-/

public section

open Filter Finset
open scoped Topology

namespace DirichletCharacter

variable {M N : ℕ}

/-- Raising the level deletes precisely the factors at primes dividing the new level.
This identity holds for every finite set of primes, without a convergence assumption. -/
theorem prod_one_sub_div_inv_changeLevel (χ : DirichletCharacter ℂ M) (hMN : M ∣ N)
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ p ∈ S, (1 - changeLevel hMN χ p / (p : ℂ))⁻¹) =
      (∏ p ∈ S, (1 - χ p / (p : ℂ))⁻¹) *
        ∏ p ∈ S with p ∣ N, (1 - χ p / (p : ℂ)) := by
  rw [prod_filter, ← prod_mul_distrib]
  refine prod_congr rfl fun p hp ↦ ?_
  by_cases hpN : p ∣ N
  · have hnonunit : ¬IsUnit (p : ZMod N) := by
      rwa [ZMod.isUnit_prime_iff_not_dvd (hS p hp), not_not]
    rw [MulChar.map_nonunit _ hnonunit]
    simp only [zero_div, sub_zero, inv_one, hpN, ↓reduceIte]
    exact (inv_mul_cancel₀
      (Complex.one_sub_div_natCast_ne_zero (hS p hp).one_lt (χ.norm_le_one p))).symm
  · have hunit : IsUnit (p : ZMod N) :=
      (ZMod.isUnit_prime_iff_not_dvd (hS p hp)).mpr hpN
    have heq : changeLevel hMN χ p = χ p := by
      rw [← hunit.unit_spec, changeLevel_eq_cast_of_dvd, hunit.unit_spec,
        ZMod.cast_natCast hMN]
    simp [hpN, heq]

/-- Once the ordered cutoff is at least the new level, the correction is the fixed
product over its prime divisors, excluding any primes already omitted. -/
theorem prod_primesLE_filter_notMem_inv_changeLevel (χ : DirichletCharacter ℂ M)
    [NeZero N] (hMN : M ∣ N) (S : Finset ℕ) {B : ℕ} (hB : N ≤ B) :
    (∏ p ∈ Nat.primesLE B with p ∉ S, (1 - changeLevel hMN χ p / (p : ℂ))⁻¹) =
      (∏ p ∈ Nat.primesLE B with p ∉ S, (1 - χ p / (p : ℂ))⁻¹) *
        ∏ p ∈ N.primeFactors with p ∉ S, (1 - χ p / (p : ℂ)) := by
  rw [prod_one_sub_div_inv_changeLevel χ hMN _ (fun p hp ↦
    Nat.prime_of_mem_primesLE (mem_filter.mp hp).1)]
  have hsets : ((Nat.primesLE B).filter (· ∉ S)).filter (· ∣ N) =
      N.primeFactors.filter (· ∉ S) := by
    ext p
    simp only [mem_filter, Nat.mem_primesLE, Nat.mem_primeFactors_of_ne_zero (NeZero.ne N)]
    constructor
    · rintro ⟨⟨⟨_, hp⟩, hpS⟩, hpN⟩
      exact ⟨⟨hp, hpN⟩, hpS⟩
    · rintro ⟨⟨hp, hpN⟩, hpS⟩
      exact ⟨⟨⟨(Nat.le_of_dvd (NeZero.pos N) hpN).trans hB, hp⟩, hpS⟩, hpN⟩
  rw [hsets]

/-- Ordered Euler-product convergence transports in both directions under a level
change, with its explicit nonzero finite correction. The same finite set of primes may
be omitted on both sides. The limit `L` may be zero. -/
theorem tendsto_prod_primesLE_filter_notMem_inv_changeLevel_iff
    (χ : DirichletCharacter ℂ M) [NeZero N] (hMN : M ∣ N) (S : Finset ℕ) (L : ℂ) :
    Tendsto (fun B : ℕ ↦ ∏ p ∈ Nat.primesLE B with p ∉ S,
        (1 - changeLevel hMN χ p / (p : ℂ))⁻¹) atTop
      (𝓝 (L * ∏ p ∈ N.primeFactors with p ∉ S, (1 - χ p / (p : ℂ)))) ↔
    Tendsto (fun B : ℕ ↦ ∏ p ∈ Nat.primesLE B with p ∉ S,
        (1 - χ p / (p : ℂ))⁻¹) atTop (𝓝 L) := by
  have hne : (∏ p ∈ N.primeFactors with p ∉ S, (1 - χ p / (p : ℂ))) ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun p hp ↦ ?_
    exact Complex.one_sub_div_natCast_ne_zero
      (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).one_lt (χ.norm_le_one p)
  have heq : (fun B : ℕ ↦ ∏ p ∈ Nat.primesLE B with p ∉ S,
      (1 - changeLevel hMN χ p / (p : ℂ))⁻¹) =ᶠ[atTop]
      (fun B ↦ (∏ p ∈ Nat.primesLE B with p ∉ S, (1 - χ p / (p : ℂ))⁻¹) *
        ∏ p ∈ N.primeFactors with p ∉ S, (1 - χ p / (p : ℂ))) := by
    filter_upwards [eventually_ge_atTop N] with B hB
    exact prod_primesLE_filter_notMem_inv_changeLevel χ hMN S hB
  rw [tendsto_congr' heq]
  exact tendsto_mul_iff_of_ne_zero tendsto_const_nhds hne

/-- For a nontrivial character, the ordered Euler-product endpoint with its native
`LFunction` value holds at the raised level if and only if it holds at the original level.
This is a transport theorem, not an assertion of boundary convergence. -/
theorem tendsto_prod_primesLE_inv_changeLevel_iff [NeZero M] [NeZero N]
    (χ : DirichletCharacter ℂ M) (hχ : χ ≠ 1) (hMN : M ∣ N) :
    Tendsto (fun B : ℕ ↦ ∏ p ∈ Nat.primesLE B,
        (1 - changeLevel hMN χ p / (p : ℂ))⁻¹) atTop
      (𝓝 (LFunction (changeLevel hMN χ) 1)) ↔
    Tendsto (fun B : ℕ ↦ ∏ p ∈ Nat.primesLE B,
        (1 - χ p / (p : ℂ))⁻¹) atTop (𝓝 (LFunction χ 1)) := by
  rw [LFunction_changeLevel hMN χ (Or.inl hχ)]
  simpa only [notMem_empty, not_false_eq_true, filter_true, Complex.cpow_neg_one,
    div_eq_mul_inv] using
    tendsto_prod_primesLE_filter_notMem_inv_changeLevel_iff χ hMN ∅ (LFunction χ 1)

end DirichletCharacter
