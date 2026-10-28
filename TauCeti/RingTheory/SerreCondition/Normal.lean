/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.SerreCondition
import TauCeti.RingTheory.CohenMacaulay.Normal
import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
import TauCeti.RingTheory.IntegralClosure.AssociatedPrime
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Serre's criterion for normality

A Noetherian domain is integrally closed if and only if it satisfies Serre's conditions `(R₁)`
and `(S₂)` (Stacks, Lemma 10.157.4 (031S), for a domain). Here `(R₁)` asks that the localizations
at primes of height at most one be regular, and `(S₂)` that the localization `R_p` at every prime
have depth at least `min (2, dim R_p)`.

The condition `(S₂)` controls the associated primes of quotients by nonzerodivisors: for a finite
module `M` satisfying `(S₂)` and an `M`-regular element `a`, every associated prime `p` of
`M ⧸ a M` has `dim Supp M_p ≤ 1`, since dividing by `a` lowers the depth of `M_p` by one and
`p` is associated exactly when `(M ⧸ a M)_p` has depth zero. For `M = R`, every associated prime
of `R ⧸ (b)` has height one. Under `(R₁)` the localization at such a prime is a regular local ring
of dimension one, that is a discrete valuation ring, and
`TauCeti.IsIntegrallyClosed.of_localization_isAssociatedPrime` shows that `R` is integrally
closed.

Conversely, the localizations of an integrally closed Noetherian domain are integrally closed:
in dimension one they are discrete valuation rings, giving `(R₁)`, and in dimension at least two
they have depth at least two (`IsLocalRing.two_le_depth_of_isIntegrallyClosed`), giving `(S₂)`.

## Main results

* `Module.SatisfiesSerreS.supportDim_le_one_of_mem_associatedPrimes_quotSMulTop`: if `M`
  satisfies `(S₂)` and `a` is `M`-regular, every associated prime `p` of `M ⧸ a M` has
  `dim Supp M_p ≤ 1`.
* `Module.SatisfiesSerreS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton`: if `R`
  satisfies `(S₂)` and `b` is a nonzerodivisor, every associated prime of `R ⧸ (b)` has height
  one.
* `IsIntegrallyClosed.satisfiesSerreR_one` and `IsIntegrallyClosed.satisfiesSerreS_two`: an
  integrally closed Noetherian domain satisfies `(R₁)` and `(S₂)`.
* `TauCeti.isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two`: Serre's criterion
  for a Noetherian domain.

## References

* [Stacks Project, Lemma 10.157.4](https://stacks.math.columbia.edu/tag/031S).
* H. Matsumura, *Commutative Ring Theory*, Theorems 11.5 and 23.8.
-/

public section

universe u v

open IsLocalRing Module

open scoped nonZeroDivisors

namespace Module.SatisfiesSerreS

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- Let `M` be a finite module satisfying `(S₂)` over a Noetherian ring and `a` an `M`-regular
element. Every associated prime `p` of `M ⧸ a M` has `dim Supp M_p ≤ 1`. -/
theorem supportDim_le_one_of_mem_associatedPrimes_quotSMulTop {M : Type v} [AddCommGroup M]
    [Module R M] [Module.Finite R M] (h : SatisfiesSerreS 2 R M) {a : R}
    (reg : IsSMulRegular M a) (p : Ideal R) [p.IsPrime]
    (hp : p ∈ associatedPrimes R (QuotSMulTop a M)) :
    supportDim (Localization.AtPrime p) (LocalizedModule p.primeCompl M) ≤ 1 := by
  have ha : a ∈ p := hp.annihilator_le <| by
    rw [Submodule.annihilator_top]
    exact QuotSMulTop.mem_annihilator M a
  -- `(M ⧸ a M)_p` has depth zero, so `M_p` has depth one.
  have hdepth := TauCeti.depth_localizedModule_quotSMulTop_add_one reg p ha
  rw [TauCeti.depth_localizedModule_eq_zero_iff.2 hp, zero_add] at hdepth
  have h2 := satisfiesSerreS_iff.1 h p
  rw [← hdepth, min_le_iff] at h2
  exact h2.resolve_left (by decide)

/-- If a Noetherian ring `R` satisfies `(S₂)` and `b` is a nonzerodivisor, every associated prime
of `R ⧸ (b)` has height one. -/
theorem height_eq_one_of_isAssociatedPrime_quotient_span_singleton
    (h : SatisfiesSerreS 2 R R) {b : R} (hb : b ∈ R⁰) {P : Ideal R}
    (hP : IsAssociatedPrime P (R ⧸ Ideal.span {b})) : P.height = 1 := by
  have := hP.isPrime
  have e : QuotSMulTop b R ≃ₗ[R] R ⧸ Ideal.span {b} :=
    (Ideal.quotientEquivAlgOfEq R (by simp [← Submodule.ideal_span_singleton_smul])).toLinearEquiv
  have hP' : P ∈ associatedPrimes R (QuotSMulTop b R) := by
    rw [LinearEquiv.AssociatedPrimes.eq e]
    exact hP
  have hbP : b ∈ P := hP.annihilator_le <| by
    rw [Submodule.annihilator_top, Ideal.annihilator_quotient]
    exact Ideal.mem_span_singleton_self b
  have hdim := h.supportDim_le_one_of_mem_associatedPrimes_quotSMulTop
    (isRegular_iff_mem_nonZeroDivisors.2 hb).left P hP'
  rw [supportDim_self_eq_ringKrullDim, IsLocalization.AtPrime.ringKrullDim_eq_height P] at hdim
  exact le_antisymm (by exact_mod_cast hdim)
    ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors hb).trans
      (Ideal.height_mono ((Ideal.span_singleton_le_iff_mem _).2 hbP)))

end Module.SatisfiesSerreS

section Domain

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

/-- An integrally closed Noetherian domain satisfies `(R₁)`: its localizations at primes of height
at most one are fields or discrete valuation rings. -/
theorem IsIntegrallyClosed.satisfiesSerreR_one : Ring.SatisfiesSerreR 1 R := by
  refine Ring.satisfiesSerreR_iff.2 fun p _ hp ↦ ?_
  rcases hp.lt_or_eq with hp | hp
  · exact Ring.satisfiesSerreR_iff.1 IsReduced.satisfiesSerreR_zero p (by simpa using hp)
  · have : IsIntegrallyClosed (Localization.AtPrime p) :=
      isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
    have : IsDiscreteValuationRing (Localization.AtPrime p) :=
      IsDiscreteValuationRing.of_ringKrullDim_eq_one <| by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height p, hp, Nat.cast_one, WithBot.coe_one]
    infer_instance

/-- An integrally closed Noetherian domain satisfies `(S₂)`: its localizations at primes of
dimension at least two have depth at least two, and those of dimension at most one are
Cohen–Macaulay. -/
theorem IsIntegrallyClosed.satisfiesSerreS_two : SatisfiesSerreS 2 R R := by
  refine satisfiesSerreS_iff.2 fun p _ ↦ ?_
  have : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors
  by_cases hdim : 2 ≤ ringKrullDim (Localization.AtPrime p)
  · -- `LocalizedModule p.primeCompl R` is reducibly `Localization.AtPrime p`.
    have h2 : (2 : ℕ∞) ≤
        depth (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl R)) :=
      two_le_depth_of_isIntegrallyClosed hdim
    exact (min_le_left _ _).trans (WithBot.coe_le_coe.2 h2)
  · have : Ring.KrullDimLE 1 (Localization.AtPrime p) :=
      Ring.krullDimLE_iff.2 (Order.le_of_lt_succ (not_le.1 hdim))
    exact (min_le_right _ _).trans <| (isCohenMacaulay_iff_supportDim_le_depth).1
      isCohenMacaulay_self_of_isDomain_of_krullDimLE_one

end Domain

namespace TauCeti

variable {R : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]

/-- A Noetherian domain satisfying `(R₁)` and `(S₂)` is integrally closed: the localization at an
associated prime of `R ⧸ (b)`, for `b ≠ 0`, has dimension one by `(S₂)` and is regular by `(R₁)`,
hence is a discrete valuation ring. -/
theorem isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two
    (hR : Ring.SatisfiesSerreR 1 R) (hS : SatisfiesSerreS 2 R R) : IsIntegrallyClosed R :=
  IsIntegrallyClosed.of_localization_isAssociatedPrime fun _ hb P _ hP ↦
    have hP1 := hS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton hb hP
    have := Ring.satisfiesSerreR_iff.1 hR P hP1.le
    have : IsDiscreteValuationRing (Localization.AtPrime P) :=
      IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.2 <| by
        rw [IsLocalization.AtPrime.ringKrullDim_eq_height P, hP1, WithBot.coe_one]
    inferInstance

/-- **Serre's criterion for normality.** A Noetherian domain is integrally closed if and only if
it satisfies `(R₁)` and `(S₂)`. Stacks, Lemma 10.157.4 (031S), for a domain. -/
@[stacks 031S "for a domain"]
theorem isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two :
    IsIntegrallyClosed R ↔ Ring.SatisfiesSerreR 1 R ∧ SatisfiesSerreS 2 R R :=
  ⟨fun _ ↦ ⟨IsIntegrallyClosed.satisfiesSerreR_one, IsIntegrallyClosed.satisfiesSerreS_two⟩,
    fun h ↦ isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two h.1 h.2⟩

end TauCeti

/-- A polynomial ring over a field is a unique factorization domain, hence integrally closed, so
it satisfies `(S₂)`. -/
example {k : Type u} [Field k] (n : ℕ) :
    SatisfiesSerreS 2 (MvPolynomial (Fin n) k) (MvPolynomial (Fin n) k) :=
  IsIntegrallyClosed.satisfiesSerreS_two
