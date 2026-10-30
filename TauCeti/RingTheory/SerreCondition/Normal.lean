/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.CohenMacaulay.Normal
public import TauCeti.RingTheory.DiscreteValuationRing.IntegrallyClosed
public import TauCeti.RingTheory.SerreCondition.Basic
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.Regular.RegularSequence

/-!
# Serre's criterion for normality

A Noetherian ring `R` is *normal* when every localization `R_p` at a prime is an integrally closed
domain (Stacks, Definition 10.37.11 (00GV)). Serre's criterion says that this happens exactly when
`R` satisfies `(R₁)` and `(S₂)` (Stacks, Lemma 10.157.4 (031S)). This file proves that a normal
Noetherian ring satisfies `(R₁)` and `(S₂)`, and proves the converse for Noetherian domains, so
that a Noetherian domain is integrally closed if and only if it satisfies `(R₁)` and `(S₂)`.

The `(R₁)` half holds because an integrally closed Noetherian local domain of dimension at most
one is a field or a discrete valuation ring. The `(S₂)` half is the local depth bound
`IsLocalRing.two_le_depth_of_isIntegrallyClosed` in dimension at least two, together with the
Cohen–Macaulay property of Noetherian local domains of dimension at most one.

For the converse, let `b` be a nonzerodivisor and `P` an associated prime of `R ⧸ (b)`. Then
`R_P ⧸ (b)` has depth zero, so `R_P` has depth one, and `(S₂)` bounds the height of `P` by one;
so `P` has height one
(`Module.SatisfiesSerreS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton`).
By `(R₁)` the localization `R_P` is then a discrete valuation ring, and a Noetherian domain with
this property is integrally closed
(`TauCeti.isIntegrallyClosed_of_forall_isAssociatedPrime_isDiscreteValuationRing`).

## Main results

* `TauCeti.satisfiesSerreR_one_of_forall_isIntegrallyClosed`: a normal Noetherian ring satisfies
  `(R₁)`.
* `TauCeti.satisfiesSerreS_two_of_forall_isIntegrallyClosed`: a normal Noetherian ring satisfies
  `(S₂)`.
* `Module.SatisfiesSerreS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton`: in a
  Noetherian ring satisfying `(S₂)`, the associated primes of `R ⧸ (b)` for a nonzerodivisor `b`
  have height one.
* `TauCeti.isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two`: a Noetherian domain
  satisfying `(R₁)` and `(S₂)` is integrally closed.
* `TauCeti.isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two`: Serre's
  criterion for Noetherian domains.

## References

* [Stacks Project, Lemma 10.157.4](https://stacks.math.columbia.edu/tag/031S).
* H. Matsumura, *Commutative Ring Theory*, Theorems 11.5 and 23.8.
-/

public section

universe u

open IsLocalRing Ideal

open scoped nonZeroDivisors

namespace TauCeti

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- A normal Noetherian ring, one whose localizations at primes are integrally closed domains,
satisfies Serre's condition `(R₁)`: its localizations at primes of height at most one are regular.
Stacks, Lemma 10.157.4 (031S), the `(R₁)` half of "normal implies `(R₁)` and `(S₂)`". -/
@[stacks 031S "normal implies `(R₁)`"]
theorem satisfiesSerreR_one_of_forall_isIntegrallyClosed
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    Ring.SatisfiesSerreR 1 R := by
  refine Ring.satisfiesSerreR_iff.2 fun p _ hp ↦ ?_
  obtain ⟨_, _⟩ := h p
  have : Ring.KrullDimLE 1 (Localization.AtPrime p) := Ring.krullDimLE_iff.2 <| by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p]
    exact_mod_cast hp
  -- `R_p` is a field or a discrete valuation ring, hence a principal ideal ring.
  by_cases hfield : IsField (Localization.AtPrime p)
  · have := hfield.isPrincipalIdealRing
    infer_instance
  · have := IsDiscreteValuationRing.of_krullDimLE_one hfield
    infer_instance

/-- A normal Noetherian ring, one whose localizations at primes are integrally closed domains,
satisfies Serre's condition `(S₂)` as a module over itself. Stacks, Lemma 10.157.4 (031S), the
`(S₂)` half of "normal implies `(R₁)` and `(S₂)`". -/
@[stacks 031S "normal implies `(S₂)`"]
theorem satisfiesSerreS_two_of_forall_isIntegrallyClosed
    (h : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) :
    Module.SatisfiesSerreS 2 R R := by
  refine (Module.satisfiesSerreS_self_iff 2 R).2 fun p _ ↦ ?_
  obtain ⟨_, _⟩ := h p
  by_cases hdim : 2 ≤ ringKrullDim (Localization.AtPrime p)
  · refine (min_le_left _ _).trans ?_
    rw [← WithBot.coe_natCast, WithBot.coe_le_coe]
    exact_mod_cast IsLocalRing.two_le_depth_of_isIntegrallyClosed hdim
  -- In dimension at most two, `R_p` is Cohen–Macaulay: its depth is its dimension.
  have : Ring.KrullDimLE 2 (Localization.AtPrime p) :=
    Ring.krullDimLE_iff.2 (not_le.1 hdim).le
  refine (min_le_right _ _).trans_eq ?_
  rw [← Module.supportDim_self_eq_ringKrullDim]
  exact (Module.isCohenMacaulay_self_of_isIntegrallyClosed_of_krullDimLE_two
    (R := Localization.AtPrime p)).depth_eq.symm

end TauCeti

namespace Module.SatisfiesSerreS

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/-- In a Noetherian ring satisfying Serre's condition `(S₂)`, every associated prime of `R ⧸ (b)`,
for a nonzerodivisor `b`, has height one. H. Matsumura, *Commutative Ring Theory*,
Theorem 23.8. -/
theorem height_eq_one_of_isAssociatedPrime_quotient_span_singleton (hS : SatisfiesSerreS 2 R R)
    {b : R} (hb : b ∈ R⁰) {P : Ideal R} (hP : IsAssociatedPrime P (R ⧸ span {b})) :
    P.height = 1 := by
  have := hP.isPrime
  have hbP : b ∈ P := hP.annihilator_le <| by
    rw [Submodule.annihilator_top, annihilator_quotient]
    exact mem_span_singleton_self b
  -- `height P ≥ 1`, since `P` contains the nonzerodivisor `b`
  have hP1 : 1 ≤ P.height := (one_le_height_span_singleton_of_mem_nonZeroDivisors hb).trans
    (height_mono ((span_singleton_le_iff_mem _).mpr hbP))
  -- `R_P ⧸ (b)` has depth zero, so `R_P` has depth one
  have hAss : P ∈ associatedPrimes R (QuotSMulTop b R) := by
    rw [LinearEquiv.AssociatedPrimes.eq (Submodule.quotEquivOfEq _ _ (by
      rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, mul_top]))]
    exact hP
  have hdepth := TauCeti.depth_localizedModule_quotSMulTop_add_one
    (isLeftRegular_iff.1 (isRegular_iff_mem_nonZeroDivisors.2 hb).left) hbP
  rw [TauCeti.depth_localizedModule_eq_zero_iff.2 hAss, zero_add] at hdepth
  -- `(S₂)` at `P` then bounds `dim R_P = height P` by one
  let e : LocalizedModule P.primeCompl R ≃ₗ[Localization.AtPrime P] Localization.AtPrime P :=
    (IsLocalizedModule.iso P.primeCompl
      (Algebra.linearMap R (Localization.AtPrime P))).extendScalarsOfIsLocalization
      P.primeCompl (Localization.AtPrime P)
  have h2 := satisfiesSerreS_iff.1 hS P
  rw [← hdepth, supportDim_eq_of_equiv e, supportDim_self_eq_ringKrullDim,
    IsLocalization.AtPrime.ringKrullDim_eq_height P] at h2
  have hle : P.height ≤ 1 := by
    rcases min_le_iff.1 h2 with h2 | h2
    · exact absurd h2 (by decide)
    · exact_mod_cast h2
  exact le_antisymm hle hP1

end Module.SatisfiesSerreS

namespace TauCeti

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsDomain R]

/-- A Noetherian domain satisfying Serre's conditions `(R₁)` and `(S₂)` is integrally closed.
Stacks, Lemma 10.157.4 (031S), the converse direction, for a domain. -/
@[stacks 031S "`(R₁)` and `(S₂)` imply normal, for a domain"]
theorem isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two
    (hR : Ring.SatisfiesSerreR 1 R) (hS : Module.SatisfiesSerreS 2 R R) : IsIntegrallyClosed R :=
  -- at an associated prime `P` of `R ⧸ (b)`, `R_P` is regular local of dimension one
  isIntegrallyClosed_of_forall_isAssociatedPrime_isDiscreteValuationRing fun _ hb P _ hP ↦ by
    have hP1 := hS.height_eq_one_of_isAssociatedPrime_quotient_span_singleton hb hP
    have := Ring.satisfiesSerreR_iff.1 hR P hP1.le
    refine IsRegularLocalRing.isDiscreteValuationRing_iff_ringKrullDim_eq_one.2 ?_
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height P, hP1, WithBot.coe_one]

/-- **Serre's criterion for normality, for domains.** A Noetherian domain is integrally closed if
and only if it satisfies Serre's conditions `(R₁)` and `(S₂)`. Stacks, Lemma 10.157.4 (031S). -/
@[stacks 031S "for a domain"]
theorem isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two :
    IsIntegrallyClosed R ↔ Ring.SatisfiesSerreR 1 R ∧ Module.SatisfiesSerreS 2 R R := by
  refine ⟨fun _ ↦ ?_, fun h ↦ isIntegrallyClosed_of_satisfiesSerreR_one_of_satisfiesSerreS_two
    h.1 h.2⟩
  -- the localizations of an integrally closed domain are integrally closed domains
  have h (p : Ideal R) [p.IsPrime] :
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p) :=
    ⟨inferInstance,
      isIntegrallyClosed_of_isLocalization _ p.primeCompl p.primeCompl_le_nonZeroDivisors⟩
  exact ⟨satisfiesSerreR_one_of_forall_isIntegrallyClosed h,
    satisfiesSerreS_two_of_forall_isIntegrallyClosed h⟩

end TauCeti

/-- A Dedekind domain is integrally closed, so it satisfies `(S₂)`. -/
example {R : Type u} [CommRing R] [IsDedekindDomain R] : Module.SatisfiesSerreS 2 R R :=
  (TauCeti.isIntegrallyClosed_iff_satisfiesSerreR_one_and_satisfiesSerreS_two.1 inferInstance).2
