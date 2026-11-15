/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Localization.AtPrime.Basic

import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Factorization
import TauCeti.RingTheory.Localization.ChineseRemainder

/-!
# Finite approximation in Dedekind domains

This file gives the finite approximation theorem in the form used to patch local data over a
Dedekind domain. Given an element of every localization at a height-one prime, one global element
agrees with all of them modulo a fixed nonzero ideal.

Only the finitely many primes containing the ideal impose a condition, and at each of them the
extended ideal contains a power of the maximal ideal of the discrete valuation ring `R_v`. The
statement therefore reduces to the Chinese remainder theorem for localizations at finitely many
maximal ideals, `TauCeti.Localization.AtPrime.exists_mk_algebraMap_eq_of_isMaximal`.

## Main results

* `TauCeti.DedekindDomain.exists_forall_sub_mem_map_localizationAtPrime`: one element of `R`
  agrees with a prescribed element of every localization `R_v` modulo a fixed nonzero ideal.
  Only the finitely many primes containing the ideal impose a condition.
* `TauCeti.DedekindDomain.exists_forall_sub_mem_span_singleton_localizationAtPrime`: the
  specialization to a nonzero principal modulus.

This is the finite approximation input for the local-to-global patching arguments in
Silverman, *The Arithmetic of Elliptic Curves*, Chapter VIII, Section 8.
-/

public section

namespace TauCeti.DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]

/-- **Approximation modulo a nonzero ideal at every height-one prime.**

Given an element `x v` of every localization `R_v`, a single `a ∈ R` is congruent to each `x v`
modulo the extension of `I` to `R_v`. The family is indexed by all height-one primes; only the
finitely many containing `I` constrain `a`, since at every other prime the extension is the
unit ideal. -/
theorem exists_forall_sub_mem_map_localizationAtPrime {I : Ideal R} (hI : I ≠ ⊥)
    (x : (v : HeightOneSpectrum R) → Localization.AtPrime v.asIdeal) :
    ∃ a : R, ∀ v : HeightOneSpectrum R,
      algebraMap R (Localization.AtPrime v.asIdeal) a - x v ∈
        I.map (algebraMap R (Localization.AtPrime v.asIdeal)) := by
  let T := {v : HeightOneSpectrum R | v.asIdeal ∣ I}
  have : Finite T := (Ideal.finite_factors hI).to_subtype
  -- At each prime, a power of the maximal ideal of the discrete valuation ring `R_v` lies in `I`.
  have hpow (v : HeightOneSpectrum R) : ∃ n : ℕ,
      IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ^ n ≤
        I.map (algebraMap R (Localization.AtPrime v.asIdeal)) := by
    have := IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R v.ne_bot
      (Localization.AtPrime v.asIdeal)
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime v.asIdeal)
    obtain ⟨n, hn⟩ :=
      IsDiscreteValuationRing.ideal_eq_span_pow_irreducible (Ideal.map_ne_bot_of_ne_bot hI) hϖ
    exact ⟨n, by rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, hn]⟩
  choose n hn using hpow
  obtain ⟨a, ha⟩ := Localization.AtPrime.exists_mk_algebraMap_eq_of_isMaximal
    (fun v : T ↦ v.1.asIdeal) (HeightOneSpectrum.asIdeal_injective.comp Subtype.val_injective)
    (fun v ↦ n v) (fun v ↦ Ideal.Quotient.mk _ (x v))
  refine ⟨a, fun v ↦ ?_⟩
  by_cases hv : v ∈ T
  · exact hn v (Ideal.Quotient.eq.1 (ha ⟨v, hv⟩))
  · -- Away from the primes containing `I`, its extension is the unit ideal.
    rw [IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime v.asIdeal)
      (fun h ↦ hv (Ideal.dvd_iff_le.2 h))]
    exact Submodule.mem_top

/-- **Approximation modulo a nonzero element at every height-one prime.**

Given an element `x v` of every localization `R_v`, a single `a ∈ R` is congruent to each `x v`
modulo `d`. Only the finitely many primes containing `d` constrain `a`. -/
theorem exists_forall_sub_mem_span_singleton_localizationAtPrime {d : R} (hd : d ≠ 0)
    (x : (v : HeightOneSpectrum R) → Localization.AtPrime v.asIdeal) :
    ∃ a : R, ∀ v : HeightOneSpectrum R,
      algebraMap R (Localization.AtPrime v.asIdeal) a - x v ∈
        Ideal.span {algebraMap R (Localization.AtPrime v.asIdeal) d} := by
  simpa only [Ideal.map_span, Set.image_singleton] using
    exists_forall_sub_mem_map_localizationAtPrime (I := Ideal.span {d}) (by simpa using hd) x

end TauCeti.DedekindDomain

end
