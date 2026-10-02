/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Finite approximation in Dedekind domains

This file gives the finite approximation theorem in the form used to patch local data over a
Dedekind domain. Given residue classes modulo powers of the maximal ideals in finitely many
localizations, one global element realizes all of them.

The proof combines the Chinese remainder theorem
`Ideal.pi_quotient_surjective` with the canonical comparison
`IsLocalization.AtPrime.equivQuotMaximalIdealPow` between a prime-power quotient and the
corresponding quotient after localization.

## Main results

* `TauCeti.DedekindDomain.exists_eq_mod_localized_prime_pow`: simultaneous approximation of
  finitely many classes in localized prime-power quotients.
* `TauCeti.DedekindDomain.exists_sub_mem_span_singleton`: one element of `R` agrees with a
  prescribed element of every localization `R_v` modulo a fixed nonzero `d`. Only the finitely
  many `v` containing `d` impose a condition.

This is the finite approximation input for the local-to-global patching arguments in
Silverman, *The Arithmetic of Elliptic Curves*, Chapter VIII, Section 8.
-/

public section

namespace TauCeti.DedekindDomain

open Function
open IsDedekindDomain

variable {R ι : Type*} [CommRing R] [IsDedekindDomain R] [Finite ι]

/-- **Finite approximation at height-one primes.**

For pairwise distinct height-one primes `v i`, arbitrary residue classes modulo the indicated
powers of the maximal ideals of `R_{v i}` are simultaneously represented by a single element
of `R`.

Allowing exponent zero is harmless: the corresponding quotient is the zero ring, so that
component imposes no condition. -/
theorem exists_eq_mod_localized_prime_pow
    (v : ι → HeightOneSpectrum R) (hv : Function.Injective v) (n : ι → ℕ)
    (x : (i : ι) →
      Localization.AtPrime (v i).asIdeal ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime (v i).asIdeal) ^ n i) :
    ∃ a : R, ∀ i,
      Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime (v i).asIdeal) a) = x i := by
  let y : (i : ι) → R ⧸ (v i).asIdeal ^ n i := fun i ↦
    (IsLocalization.AtPrime.equivQuotMaximalIdealPow (v i).asIdeal
      (Localization.AtPrime (v i).asIdeal) (n i)).symm (x i)
  have hcoprime : Pairwise (IsCoprime on fun i ↦ (v i).asIdeal ^ n i) := by
    intro i j hij
    exact (v i).isCoprime_pow_of_ne (v j) (fun h ↦ hij (hv h)) (n i) (n j)
  obtain ⟨a, ha⟩ := Ideal.pi_quotient_surjective hcoprime y
  refine ⟨a, fun i ↦ ?_⟩
  rw [← IsLocalization.AtPrime.equivQuotMaximalIdealPow_apply_mk (v i).asIdeal
    (Localization.AtPrime (v i).asIdeal) (n i) a, ha i]
  exact Equiv.apply_symm_apply _ (x i)

/-- **Approximation modulo a nonzero element at every height-one prime.**

Given an element `x v` of every localization `R_v`, a single `a ∈ R` is congruent to each `x v`
modulo `d`. The family is indexed by all height-one primes; only the finitely many containing `d`
constrain `a`, since at every other prime `d` is a unit of `R_v`. -/
theorem exists_sub_mem_span_singleton {d : R} (hd : d ≠ 0)
    (x : (v : HeightOneSpectrum R) → Localization.AtPrime v.asIdeal) :
    ∃ a : R, ∀ v : HeightOneSpectrum R,
      algebraMap R (Localization.AtPrime v.asIdeal) a - x v ∈
        Ideal.span {algebraMap R (Localization.AtPrime v.asIdeal) d} := by
  let T := {v : HeightOneSpectrum R | v.asIdeal ∣ Ideal.span {d}}
  have : Finite T := (Ideal.finite_factors (by simpa using hd)).to_subtype
  -- At each prime, a power of the maximal ideal of the discrete valuation ring `R_v` lies in `(d)`.
  have hpow (v : HeightOneSpectrum R) : ∃ n : ℕ,
      IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ^ n ≤
        Ideal.span {algebraMap R (Localization.AtPrime v.asIdeal) d} := by
    have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot
      (Localization.AtPrime v.asIdeal)
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime v.asIdeal)
    have hd' : Ideal.span {algebraMap R (Localization.AtPrime v.asIdeal) d} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors _
        v.asIdeal.primeCompl_le_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hd)
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hd' hϖ
    exact ⟨n, by rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, hn]⟩
  choose n hn using hpow
  obtain ⟨a, ha⟩ := exists_eq_mod_localized_prime_pow (fun v : T ↦ v.1) Subtype.val_injective
    (fun v ↦ n v) (fun v ↦ Ideal.Quotient.mk _ (x v))
  refine ⟨a, fun v ↦ ?_⟩
  by_cases hv : v ∈ T
  · exact hn v (Ideal.Quotient.eq.1 (ha ⟨v, hv⟩))
  · -- Away from the primes containing `d`, `d` is a unit of `R_v` and there is nothing to prove.
    have hdv : d ∉ v.asIdeal := fun h ↦
      hv (Ideal.dvd_iff_le.2 (Ideal.span_singleton_le_iff_mem _ |>.2 h))
    rw [Ideal.span_singleton_eq_top.2
      ((IsLocalization.AtPrime.isUnit_to_map_iff _ v.asIdeal d).2 hdv)]
    exact Submodule.mem_top

end TauCeti.DedekindDomain

end
