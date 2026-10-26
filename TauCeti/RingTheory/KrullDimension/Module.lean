/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
import Mathlib.RingTheory.KrullDimension.Field
import TauCeti.RingTheory.Ideal.AssociatedPrime.Basic
import TauCeti.RingTheory.KrullDimension.Quotient
import TauCeti.RingTheory.Localization.Annihilator

/-!
# Support dimension of a localized module

Let `M` be a finite module over a Noetherian ring `R` and `p` a prime containing the annihilator
of `M`. The support of the localization `M_p` over `R_p` is zero-dimensional exactly when `p` is a
minimal prime of the support of `M`. Primes of the support of `M_p` contract to primes of the
support of `M` below `p`, and a minimal prime strictly below `p` is associated to `M`, so it
survives in `M_p` as a non-maximal associated prime.

This is the dimension input to the characterization of Serre's condition `(S_1)` as the absence of
embedded primes.

## Main results

* `Module.exists_supportDim_eq_natCast`: a nonzero module over a ring of finite Krull dimension,
  such as a Noetherian local ring, has support of finite dimension.
* `Module.supportDim_localizedModule_nonpos_iff`: `M_p` has zero-dimensional support exactly when
  `p` is a minimal prime of the support of `M`.
-/

public section

open IsLocalRing

namespace Module

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]

/-- The support of a nonzero module over a ring of finite Krull dimension, such as a Noetherian
local ring, has finite dimension: it is neither `⊥` nor `⊤`. -/
theorem exists_supportDim_eq_natCast [FiniteRingKrullDim R] [Nontrivial M] :
    ∃ k : ℕ, supportDim R M = k := by
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.1 (supportDim_ne_bot_of_nontrivial R M)
  have hd_top : d ≠ ⊤ := by
    rintro rfl
    exact (hd ▸ (supportDim_le_ringKrullDim R M).trans_lt ringKrullDim_lt_top).ne rfl
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.1 hd_top
  exact ⟨k, hd.symm⟩

/-- Let `M` be a finite module over a Noetherian ring and `p` a prime containing the annihilator
of `M`. The support of `M_p` has dimension zero exactly when `p` is a minimal prime of the support
of `M`. -/
theorem supportDim_localizedModule_nonpos_iff [IsNoetherianRing R] [Module.Finite R M]
    {p : Ideal R} [p.IsPrime] (hp : annihilator R M ≤ p) :
    supportDim (Localization.AtPrime p) (LocalizedModule p.primeCompl M) ≤ 0 ↔
      p ∈ (annihilator R M).minimalPrimes := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- A minimal prime `q ⊊ p` of the support is associated to `M`, so `q R_p` is an associated
    -- prime of `M_p` strictly below the maximal ideal, and `1 ≤ dim (R_p ⧸ q R_p) ≤ dim Supp M_p`.
    obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le hp
    refine by_contra fun hpmin ↦ ?_
    have hqp : q < p := lt_of_le_of_ne hqp fun h ↦ hpmin (h ▸ hq)
    have := hq.isPrime
    have hdisj : Disjoint (p.primeCompl : Set R) q :=
      Set.disjoint_left.2 fun _ hx hxq ↦ hx (hqp.le hxq)
    set Q := q.map (algebraMap R (Localization.AtPrime p))
    have hQ : Q.under R = q := IsLocalization.under_map_of_isPrime_disjoint _ _ ‹_› hdisj
    have hQass : IsAssociatedPrime Q (LocalizedModule p.primeCompl M) :=
      associatedPrimes.mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule
        p.primeCompl (LocalizedModule.mkLinearMap p.primeCompl M) Q
        (by rw [← Ideal.under_def, hQ]
            exact associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R M hq)
    have := hQass.isPrime
    have hQlt : Q < maximalIdeal (Localization.AtPrime p) :=
      lt_of_le_of_ne (le_maximalIdeal this.ne_top) fun h ↦
        hqp.ne (hQ.symm.trans (Localization.AtPrime.eq_maximalIdeal_iff_under_eq.2 h))
    have hdim := (TauCeti.ringKrullDim_quotient_add_one_le_of_lt hQlt).trans
      hQass.ringKrullDim_quotient_le_supportDim
    rw [ringKrullDim_eq_zero_of_isField
      ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 inferInstance), zero_add] at hdim
    exact absurd (hdim.trans h) (by decide)
  · -- Every prime `Q` of the support of `M_p` contracts to a prime between the annihilator of `M`
    -- and `p`, hence to `p`, so `Q` is the maximal ideal and the support is a single point.
    refine Order.krullDim_nonpos_iff_forall_isMax.2 fun Q Q' _ ↦ ?_
    suffices key : ∀ Q ∈ support (Localization.AtPrime p) (LocalizedModule p.primeCompl M),
        Q.asIdeal = maximalIdeal (Localization.AtPrime p) by
      exact (Subtype.ext (PrimeSpectrum.ext ((key _ Q'.2).trans (key _ Q.2).symm))).le
    intro Q hQ
    have hQp : Q.asIdeal.under R ≤ p :=
      (Ideal.comap_mono (le_maximalIdeal Q.isPrime.ne_top)).trans_eq
        Localization.AtPrime.under_maximalIdeal
    -- The annihilator of `M` extends into the annihilator of `M_p`, hence into `Q`.
    have hann : annihilator R M ≤ Q.asIdeal.under R := Ideal.map_le_iff_le_comap.1 <|
      (IsLocalizedModule.map_annihilator_le p.primeCompl _
        (LocalizedModule.mkLinearMap p.primeCompl M)).trans (annihilator_le_of_mem_support hQ)
    exact Localization.AtPrime.eq_maximalIdeal_iff_under_eq.1
      (le_antisymm hQp (h.2 ⟨Ideal.IsPrime.under R Q.asIdeal, hann⟩ hQp))

end Module
