/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Basic
-- Proof-only: `Localization.subalgebra.ofField` builds the localizations the argument compares;
-- the statement names only `Subalgebra` and `IsIntegrallyClosed`.
import Mathlib.RingTheory.Localization.Integral
-- Proof-only, and load-bearing despite no textual use: supplies `IsIntegrallyClosed` on a
-- `ValuationSubring`, which the overring argument closes with.
import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.RingTheory.DedekindDomain.AdicValuation
-- Proof-only: `Valuation.eq_valuation_of_forall_mem_asIdeal_iff` identifies the valuations of the
-- primes of an overring that lie over a given prime.
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

/-!
# Overrings of a Dedekind domain in its fraction field

An *overring* of `A` here is a subalgebra of the fraction field `K` of `A`, that is, a ring between
`A` and `K`. Every such ring is integrally closed: its localizations at maximal ideals are
localizations of `A` too, and those are valuation rings of `K`, or `K` itself over the zero prime.

Nothing about integral closures of `A` in *larger* fields is needed for this, which is why it lives
apart from `RingTheory/IntegralClosure/`.

The extension to an overring `B` of a height one prime `𝔭` of `A` is read off the valuation of
`𝔭`. If some element of `B` has a pole at `𝔭`, the extension is the unit ideal: that pole puts an
element of `A` outside `𝔭` into `𝔭B`. If instead the valuation of `𝔭` is the valuation of a height
one prime `𝔓` of `B`, then `𝔓` is the only prime of `B` containing `𝔭B`, and `𝔭B = 𝔓`, with no
ramification, the two rings having the same fraction field.

## Main results

* `Subalgebra.isIntegrallyClosed_overring`: every subalgebra of the fraction field of a Dedekind
  domain is integrally closed.
* `IsDedekindDomain.HeightOneSpectrum.map_asIdeal_eq_top_of_one_lt_valuation`: a prime extends to
  the unit ideal of an overring containing an element with a pole at it.
* `IsDedekindDomain.HeightOneSpectrum.map_asIdeal_eq_asIdeal_of_valuation_eq`: a prime extends to
  the prime of an overring carrying the same valuation.

## Provenance

Adapted from D. K. Angdinata's `NormalizationFinite.lean`, Apache-2.0, supplied by the author on
2026-09-07, declaration `Subalgebra.isIntegrallyClosed_overring`.
-/

public section

namespace Subalgebra

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

variable {A K : Type*} [CommRing A] [IsDedekindDomain A] [Field K]
  [Algebra A K] [IsFractionRing A K]

/-- Every overring of a Dedekind domain in its fraction field is integrally closed. -/
theorem isIntegrallyClosed_overring (C : Subalgebra A K) : IsIntegrallyClosed C := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro q _ hq
  let p : Ideal A := q.comap (algebraMap A C)
  have p_prime : p.IsPrime := hq.isPrime.comap (algebraMap A C)
  let S : Subalgebra C K := Localization.subalgebra.ofField K q.primeCompl
    q.primeCompl_le_nonZeroDivisors
  let T : Subalgebra A K := Localization.subalgebra.ofField K p.primeCompl
    p.primeCompl_le_nonZeroDivisors
  have hTS : T.toSubring ≤ S.toSubring := by
    rintro x ⟨a, s, hs, rfl⟩
    refine ⟨algebraMap A C a, algebraMap A C s, ?_, ?_⟩
    · simpa [p] using hs
    -- both images in `K` agree because the routes `A → K` and `A → C → K` coincide by the
    -- scalar tower, so this is a rewrite rather than a reliance on how the coercion unfolds.
    · rw [IsScalarTower.algebraMap_apply A C K, IsScalarTower.algebraMap_apply A C K]
  -- `S` is a valuation subring: above a nonzero prime it contains the valuation subring at that
  -- prime, and above `⊥` it is all of `K`. Either way `IsIntegrallyClosed` transfers to the
  -- localization along `IsLocalization.algEquiv`.
  have key : ∀ V : ValuationSubring K, V.toSubring = S.toSubring → IsIntegrallyClosed S := by
    intro V hV
    have : IsIntegrallyClosed V := inferInstance
    exact this.of_equiv (RingEquiv.subringCongr hV)
  by_cases hp : p = ⊥
  · have hall : ∀ x : K, x ∈ S := fun x ↦ hTS <| by
      obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective A x
      exact ⟨a, b, by simpa [p, hp, Ideal.primeCompl_bot] using nonZeroDivisors.ne_zero hb,
        by simpa [div_eq_mul_inv] using hab.symm⟩
    exact (key ⊤ (by ext x; simpa using hall x)).of_equiv
      (IsLocalization.algEquiv q.primeCompl S (Localization.AtPrime q)).toRingEquiv
  · exact (key (ValuationSubring.ofLE (valuationSubringAtPrime K ⟨p, p_prime, hp⟩)
      S.toSubring hTS) rfl).of_equiv
      (IsLocalization.algEquiv q.primeCompl S (Localization.AtPrime q)).toRingEquiv

end Subalgebra

namespace IsDedekindDomain.HeightOneSpectrum

variable {A K B : Type*} [CommRing A] [IsDedekindDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [CommRing B] [Algebra A B] [Algebra B K] [IsScalarTower A B K]

/-- **A prime extends to the unit ideal of an overring containing an element with a pole at it.**
If `b ∈ B` has `v 𝔭 b > 1`, then `b⁻¹ = n / d` with `n ∈ 𝔭` and `d ∉ 𝔭`, so `d = b n` lies in
`𝔭B`; as `d` is invertible modulo the maximal ideal `𝔭`, so does `1`. -/
theorem map_asIdeal_eq_top_of_one_lt_valuation [FaithfulSMul B K] (v : HeightOneSpectrum A)
    {b : B} (hb : 1 < v.valuation K (algebraMap B K b)) :
    v.asIdeal.map (algebraMap A B) = ⊤ := by
  have hb0 : algebraMap B K b ≠ 0 := by
    rintro h
    rw [h, map_zero] at hb
    exact not_lt_of_ge zero_le hb
  obtain ⟨n, d, hnd⟩ := v.exists_primeCompl_mul_eq_of_integer (algebraMap B K b)⁻¹ <| by
    rw [map_inv₀]
    exact (inv_lt_one_of_one_lt₀ hb).le
  have hn : n ∈ v.asIdeal := by
    have hlt : v.valuation K (algebraMap A K n) < 1 := by
      rw [← hnd, map_mul, v.valuation_eq_one_iff_notMem.mpr d.2, mul_one, map_inv₀]
      exact inv_lt_one_of_one_lt₀ hb
    exact (v.valuation_lt_one_iff_mem (K := K) n).mp hlt
  have hd : algebraMap A B d = b * algebraMap A B n := by
    apply FaithfulSMul.algebraMap_injective B K
    rw [map_mul, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, ← hnd,
      ← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
  obtain ⟨y, i, hi, hyi⟩ := v.isMaximal.exists_inv d.2
  rw [Ideal.eq_top_iff_one, ← map_one (algebraMap A B), ← hyi, map_add, map_mul, hd]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _
    (Ideal.mem_map_of_mem _ hn))) (Ideal.mem_map_of_mem _ hi)

/-- **A prime extends to the prime of an overring carrying the same valuation**, unramified: if
the valuation of the height one prime `𝔓` of the Dedekind overring `B` is that of `𝔭`, then
`𝔭B = 𝔓`.

Every maximal ideal of `B` containing `𝔭B` has a valuation bounded by `1` on `A` and centred at
`𝔭`, hence equal to the valuation of `𝔭`, so it is `𝔓`. Thus `𝔭B` is a power of `𝔓`, and the
exponent is `1` because a uniformizer of `𝔭` stays a uniformizer of `𝔓`. -/
theorem map_asIdeal_eq_asIdeal_of_valuation_eq [IsDedekindDomain B] [IsFractionRing B K]
    (v : HeightOneSpectrum A) (𝔓 : HeightOneSpectrum B) (h : 𝔓.valuation K = v.valuation K) :
    v.asIdeal.map (algebraMap A B) = 𝔓.asIdeal := by
  set I := v.asIdeal.map (algebraMap A B)
  have hval (a : A) : 𝔓.valuation K (algebraMap B K (algebraMap A B a)) =
      v.valuation K (algebraMap A K a) := by
    rw [← IsScalarTower.algebraMap_apply, h]
  have hinj : Function.Injective (algebraMap A B) := fun a a' haa' ↦
    IsFractionRing.injective A K <| by
      rw [IsScalarTower.algebraMap_apply A B K, IsScalarTower.algebraMap_apply A B K, haa']
  have hle : I ≤ 𝔓.asIdeal := Ideal.map_le_iff_le_comap.mpr fun a ha ↦ by
    rw [Ideal.mem_comap, ← 𝔓.valuation_lt_one_iff_mem (K := K), hval]
    exact (v.valuation_lt_one_iff_mem (K := K) a).mpr ha
  have hI0 : I ≠ ⊥ := (Ideal.map_eq_bot_iff_of_injective hinj).not.mpr v.ne_bot
  -- `𝔓` is the only maximal ideal of `B` containing `I`
  have huniq (M : Ideal B) (hM : M.IsMaximal) (hIM : I ≤ M) : M = 𝔓.asIdeal := by
    let Q : HeightOneSpectrum B :=
      ⟨M, hM.isPrime, fun hM0 ↦ hI0 (le_bot_iff.mp (hM0 ▸ hIM))⟩
    have hQ : v.valuation K = Q.valuation K := by
      refine Valuation.eq_valuation_of_forall_mem_asIdeal_iff (Q.valuation_surjective K)
        (fun a ↦ ?_) (fun a ↦ ?_)
      · rw [IsScalarTower.algebraMap_apply A B K]
        exact Q.valuation_le_one _
      · rw [IsScalarTower.algebraMap_apply A B K, Q.valuation_lt_one_iff_mem]
        refine ⟨fun ha ↦ hIM (Ideal.mem_map_of_mem _ ha), fun ha ↦ ?_⟩
        have hvle : v.asIdeal ≤ M.comap (algebraMap A B) := fun a' ha' ↦
          hIM (Ideal.mem_map_of_mem _ ha')
        exact v.isMaximal.eq_of_le (Ideal.IsPrime.comap _).ne_top hvle ▸ ha
    exact congrArg HeightOneSpectrum.asIdeal (valuation_injective (K := K) (hQ.symm.trans h.symm))
  -- so the part of `I` prime to `𝔓` is trivial, and `I` is a power of `𝔓`
  obtain ⟨Q, hPQ, hIQ⟩ := Ideal.eq_prime_pow_mul_coprime hI0 𝔓.asIdeal
  have hQtop : Q = ⊤ := by
    by_contra hQ
    obtain ⟨M, hM, hQM⟩ := Ideal.exists_le_maximal Q hQ
    rw [huniq M hM (hIQ ▸ Ideal.mul_le_right.trans hQM)] at hQM
    exact 𝔓.isMaximal.ne_top (top_le_iff.mp (hPQ ▸ sup_le le_rfl hQM))
  rw [hQtop, Ideal.mul_top] at hIQ
  -- and the exponent is `1`, by the valuation of a uniformizer of `𝔭`
  set c := Multiset.count 𝔓.asIdeal (UniqueFactorizationMonoid.normalizedFactors I)
  obtain ⟨t, ht⟩ := v.intValuation_exists_uniformizer
  have htI : algebraMap A B t ∈ 𝔓.asIdeal ^ c := hIQ ▸ Ideal.mem_map_of_mem _
    ((v.intValuation_lt_one_iff_mem t).mp (by rw [ht]; decide))
  have htP : 𝔓.intValuation (algebraMap A B t) = WithZero.exp (-1 : ℤ) := by
    rw [← valuation_of_algebraMap (K := K), hval, valuation_of_algebraMap, ht]
  have hc : c = 1 := by
    rcases Nat.lt_trichotomy c 1 with hc | hc | hc
    · rw [Nat.lt_one_iff.mp hc, pow_zero, Ideal.one_eq_top] at hIQ
      exact absurd (top_le_iff.mp (hIQ ▸ hle)) 𝔓.isMaximal.ne_top
    · exact hc
    · have := (𝔓.intValuation_le_pow_iff_mem _ c).mpr htI
      rw [htP, WithZero.exp_le_exp] at this
      omega
  rw [hIQ, hc, pow_one]

end IsDedekindDomain.HeightOneSpectrum
