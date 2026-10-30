/-
Copyright (c) 2026 Taylor Dupuy, Thomas Tucker, Zhuoran Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Taylor Dupuy, Thomas Tucker, Zhuoran Wang
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import TauCeti.RingTheory.Ideal.Quotient.Colon

/-!
# Integrally closed local domains of dimension one

A Noetherian integrally closed local domain of Krull dimension one is a discrete valuation ring
(Stacks, Lemma 10.119.7 (00PD)). Mathlib proves the equivalence of the conditions in
`tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`, one of which asks for integral closedness
together with "every nonzero prime is the maximal ideal"; this file supplies that condition from
the dimension.

Conversely, a Noetherian domain is integrally closed as soon as its localizations at the
associated primes of principal ideals are discrete valuation rings: a fraction `a / b` that lies
in all of them lies in `R`, because an associated prime of `R ⧸ (b)` containing `((b) : a)` would
otherwise exist. This is the common last step of the proofs that regular domains and domains
satisfying Serre's conditions `(R₁)` and `(S₂)` are integrally closed.

## Main results

* `IsDiscreteValuationRing.of_krullDimLE_one`: a Noetherian integrally closed local domain of
  Krull dimension at most one that is not a field is a discrete valuation ring.
* `IsDiscreteValuationRing.of_ringKrullDim_eq_one`: the dimension-one specialization.
* `TauCeti.isIntegrallyClosed_of_forall_isAssociatedPrime_isDiscreteValuationRing`: conversely, a
  Noetherian domain whose localizations at the associated primes of principal ideals are discrete
  valuation rings is integrally closed (H. Matsumura, *Commutative Ring Theory*, Theorem 11.5).

## References

* [Stacks Project, Lemma 10.119.7](https://stacks.math.columbia.edu/tag/00PD).
* Ported from T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0): the ring-level step of
  `Pcf.isDiscreteValuationRing_localizationAtPrime_of_heightOne` in
  `lean/Pcf/Bounding/Divisors.lean`, stated there for the localization of a Noetherian
  integrally closed domain at a prime of height one.
* `isIntegrallyClosed_of_forall_isAssociatedPrime_isDiscreteValuationRing` is the final step of
  `Pcf.Stacks.isIntegrallyClosed_of_isRegularRing` in the same repository at commit
  `a39c3781b9850b9f3d5cbc9920322a3b8e365ef2`, `lean/Pcf/Stacks/Common/RegularNormal.lean`.
* H. Matsumura, *Commutative Ring Theory*, Theorem 11.5.
-/

public section

open IsLocalRing

namespace IsDiscreteValuationRing

/-- A Noetherian integrally closed local domain of Krull dimension at most one that is not a
field is a discrete valuation ring. -/
theorem of_krullDimLE_one {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] [Ring.KrullDimLE 1 R]
    (hnot : ¬ IsField R) : _root_.IsDiscreteValuationRing R := by
  have hmax : maximalIdeal R ≠ ⊥ := fun hbot ↦ hnot (isField_iff_maximalIdeal_eq.mpr hbot)
  have hnormal : IsIntegrallyClosed R ∧
      ∀ P : Ideal R, P ≠ ⊥ → P.IsPrime → P = maximalIdeal R :=
    ⟨inferInstance, fun P hP _ ↦ eq_maximalIdeal (Ideal.isMaximal_of_isPrime_of_ne_bot P hP)⟩
  have : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 1).mp hnormal
  exact { not_a_field' := hmax }

/-- A Noetherian integrally closed local domain of Krull dimension one is a discrete valuation
ring. Stacks, Lemma 10.119.7 (00PD). -/
@[stacks 00PD]
theorem of_ringKrullDim_eq_one {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R] [IsIntegrallyClosed R] (h : ringKrullDim R = 1) :
    _root_.IsDiscreteValuationRing R := by
  have : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr h.le
  apply of_krullDimLE_one
  intro hfield
  rw [ringKrullDim_eq_zero_of_isField hfield] at h
  exact zero_ne_one h

end IsDiscreteValuationRing

namespace TauCeti

open _root_.Ideal

open scoped nonZeroDivisors

/-- **A Krull-type criterion for integral closedness.** A Noetherian domain `R` is integrally
closed if, for every nonzerodivisor `b`, the localization of `R` at every associated prime of
`R ⧸ (b)` is a discrete valuation ring. H. Matsumura, *Commutative Ring Theory*, Theorem 11.5,
the "if" direction. -/
theorem isIntegrallyClosed_of_forall_isAssociatedPrime_isDiscreteValuationRing {R : Type*}
    [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h : ∀ b ∈ R⁰, ∀ (P : Ideal R) [P.IsPrime], IsAssociatedPrime P (R ⧸ span {b}) →
      _root_.IsDiscreteValuationRing (Localization.AtPrime P)) :
    IsIntegrallyClosed R := by
  classical
  let K := FractionRing R
  -- localize at the primes where `R_p` is integrally closed, so that the side condition of
  -- `IsIntegrallyClosed.of_localization` is exactly the defining condition of this set
  apply IsIntegrallyClosed.of_localization
    {p : PrimeSpectrum R | IsIntegrallyClosed (Localization.AtPrime p.asIdeal)}
    fun _ hp ↦ by simpa using hp
  rw [eq_bot_iff]
  intro z hz
  simp only [Algebra.mem_iInf, Set.mem_ofPred_eq] at hz
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) (K := K) z
  have hbK : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  by_cases hab : a ∈ span {b}
  · obtain ⟨r, hr⟩ := mem_span_singleton'.mp hab
    exact Algebra.mem_bot.mpr ⟨r, by rw [← hr, map_mul, mul_div_cancel_right₀ _ hbK]⟩
  exfalso
  -- an associated prime `P = ((b) : c)` of `R ⧸ (b)` containing `((b) : a)`
  obtain ⟨P, hPass, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R
    (Ideal.Quotient.mk (span {b}) a) (by rwa [Ne, Ideal.Quotient.eq_zero_iff_mem])
  have := hPass.isPrime
  have hcolon : ∀ r, r * a ∈ span {b} → r ∈ P := fun r hr ↦
    hle (Ideal.Quotient.mem_colon_singleton_mk.mpr hr)
  have : _root_.IsDiscreteValuationRing (Localization.AtPrime P) := h b hb P hPass
  -- `a / b = r / s` with `s ∉ P` gives `s a ∈ (b)`, so `s ∈ P`
  have hzP := hz ⟨P, inferInstance⟩ inferInstance
  rw [← Localization.subalgebra.ofField_eq K P.primeCompl P.primeCompl_le_nonZeroDivisors] at hzP
  obtain ⟨r, s, hs, hrs⟩ := hzP
  have hsK : algebraMap R K s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (P.primeCompl_le_nonZeroDivisors hs)
  rw [← div_eq_mul_inv, div_eq_div_iff hbK hsK, ← map_mul, ← map_mul] at hrs
  exact hs (hcolon s (mem_span_singleton'.mpr ⟨r, by
    rw [mul_comm s, IsFractionRing.injective R K hrs]⟩))

end TauCeti
