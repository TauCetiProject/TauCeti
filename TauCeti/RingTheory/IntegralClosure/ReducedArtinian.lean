/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import TauCeti.RingTheory.Localization.Integral

/-!
# Integral closures in reduced Artinian rings

Let `R → E` be a ring homomorphism with `E` reduced and Artinian, for instance a finite product of
fields, and suppose `R` is integrally closed in `E`. Then `R` is normal in the sense of Stacks,
Definition 10.37.11 (00GV): every localization of `R` at a prime is an integrally closed domain.
Indeed, for a prime `Q` of `R` the localization `E_Q` of `E` at the image of `R ∖ Q` is again
reduced and Artinian, and it is local: two distinct primes of `E` are separated by an idempotent,
which is integral over `R`, hence comes from `R`, and so cannot lie over primes contained in
`Q`. Thus `E_Q` is a field, and `R_Q`, which is integrally closed in `E_Q`, is an integrally closed
domain.

This applies to the integral closure of any ring in a finite étale algebra over a field, a finite
product of fields. It is the normality of the finite algebra attached to a finite étale cover of
the punctured spectrum of a normal local domain, whose generic fibre is a finite étale algebra
over the fraction field.

## Main results

* `IsIntegrallyClosedIn.isDomain_localization_atPrime` and
  `IsIntegrallyClosedIn.isIntegrallyClosed_localization_atPrime`: a ring integrally closed in a
  reduced Artinian ring is normal.

## References

* [Stacks Project, Definition 10.37.11](https://stacks.math.columbia.edu/tag/00GV).
* [Stacks Project, Lemma 58.20.3](https://stacks.math.columbia.edu/tag/0BM9), whose proof uses the
  integral closure in the generic fibre of a finite étale cover of a punctured spectrum.
* The normality argument generalizes the étale case in T. Dupuy, T. Tucker and Z. Wang,
  [pcfawd-formalization](https://github.com/tdupu/pcfawd-formalization) at commit
  `9a20b3f351446d64e6015d704198bc71c7002008` (Apache-2.0),
  `lean/Pcf/Stacks/Common/EtaleNormal.lean`, where `E` is the generic fibre of an étale algebra
  over an integrally closed domain (`eq_of_comap_le_of_etale` and
  `isField_localization_tensor_fractionRing_of_etale`), as ported to
  `TauCeti.RingTheory.Etale.Normal`.
-/

public section

namespace IsIntegrallyClosedIn

variable {R : Type*} (E : Type*) [CommRing R] [CommRing E] [Algebra R E]
  [IsIntegrallyClosedIn R E]

/-- If `R` is integrally closed in an Artinian ring `E`, two primes of `E` whose contractions
lie in a common prime `Q` of `R` coincide: an idempotent separating them would come from `R`. -/
private theorem eq_of_under_le [IsArtinianRing E] (Q : Ideal R) [Q.IsPrime] (P₁ P₂ : Ideal E)
    [P₁.IsPrime] [P₂.IsPrime] (h₁ : P₁.under R ≤ Q) (h₂ : P₂.under R ≤ Q) : P₁ = P₂ := by
  by_contra hne
  obtain ⟨e, he₂, hidem, hall⟩ := IsArtinianRing.exists_notMem_forall_mem_of_ne P₂
  have he₁ : e ∈ P₁ := hall P₁ inferInstance hne
  have : Nontrivial R := nontrivial_of_ne 0 1 fun h ↦
    ‹Q.IsPrime›.ne_top ((Ideal.eq_top_iff_one Q).mpr (h ▸ Q.zero_mem))
  have hint : IsIntegral R e := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, ?_, ?_⟩
    · exact Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; decide)
    · simp [pow_two, hidem.eq]
  obtain ⟨s, rfl⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp hint
  -- Both `s` and `1 - s` lie in `Q`, since `s (1 - s) = 0` and `s ∉ P₂`.
  have hzero : algebraMap R E s * algebraMap R E (1 - s) = 0 := by
    rw [map_sub, map_one, mul_sub, mul_one, hidem.eq, sub_self]
  have hcompl : algebraMap R E (1 - s) ∈ P₂ :=
    (‹P₂.IsPrime›.mem_or_mem (hzero ▸ P₂.zero_mem)).resolve_left he₂
  exact ‹Q.IsPrime›.ne_top ((Ideal.eq_top_iff_one Q).mpr (by
    simpa using Q.add_mem (h₁ he₁) (h₂ hcompl)))

/-- If `R` is integrally closed in a reduced Artinian ring `E` and `Q` is a prime of `R`, a
nonzero localization of `E` at the image of `R ∖ Q` is a field. -/
private theorem isField_localization [IsArtinianRing E] [IsReduced E] (Q : Ideal R) [Q.IsPrime]
    (Lq : Type*) [CommRing Lq] [Algebra E Lq]
    [IsLocalization (Algebra.algebraMapSubmonoid E Q.primeCompl) Lq] [Nontrivial Lq] :
    IsField Lq := by
  let M := Algebra.algebraMapSubmonoid E Q.primeCompl
  have : IsArtinianRing Lq := IsArtinianRing.localization_artinian M Lq
  -- `isReduced_localizationPreserves` requires `Lq` in the universe of `E`, so transport
  -- Mathlib's instance for `Localization` along the canonical isomorphism instead.
  have : IsReduced Lq := by
    let e := IsLocalization.algEquiv M Lq (Localization M)
    exact isReduced_of_injective e.toRingHom e.injective
  -- Every maximal ideal of `Lq` contracts to a prime of `E` lying over a prime contained in `Q`.
  have hunder : ∀ m : Ideal Lq, m.IsMaximal → (m.under E).under R ≤ Q := by
    intro m hm s hs
    by_contra hsQ
    have hunit : IsUnit (algebraMap E Lq (algebraMap R E s)) :=
      IsLocalization.map_units Lq (⟨algebraMap R E s,
        Algebra.mem_algebraMapSubmonoid_of_mem (⟨s, hsQ⟩ : Q.primeCompl)⟩ : M)
    exact hm.ne_top (Ideal.eq_top_of_isUnit_mem _ hs hunit)
  have : IsLocalRing Lq := by
    obtain ⟨m, hm⟩ := Ideal.exists_maximal Lq
    refine IsLocalRing.of_unique_max_ideal ⟨m, hm, fun m' hm' ↦ ?_⟩
    have := hm.isPrime
    have := hm'.isPrime
    have heq : m'.under E = m.under E :=
      eq_of_under_le E Q _ _ (hunder m' hm') (hunder m hm)
    rw [← IsLocalization.map_under M Lq m', heq, IsLocalization.map_under M Lq m]
  exact IsArtinianRing.isField_of_isReduced_of_isLocalRing Lq

/-- If `R` is integrally closed in a reduced Artinian ring `E`, every localization of `R` at a
prime is an integrally closed domain, as a conjunction. -/
private theorem isDomain_and_isIntegrallyClosed_localization_atPrime [IsArtinianRing E]
    [IsReduced E] (Q : Ideal R) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) ∧ IsIntegrallyClosed (Localization.AtPrime Q) := by
  let M := Algebra.algebraMapSubmonoid E Q.primeCompl
  have hclq : IsIntegrallyClosedIn (Localization.AtPrime Q) (Localization M) :=
    TauCeti.IsLocalization.isIntegrallyClosedIn (R := R) (S := E) Q.primeCompl
  have hinj := (isIntegrallyClosedIn_iff.mp hclq).1
  have : Nontrivial (Localization M) := hinj.nontrivial
  let : Field (Localization M) := (isField_localization E Q _).toField
  have : FaithfulSMul (Localization.AtPrime Q) (Localization M) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  exact ⟨hinj.isDomain _, IsIntegrallyClosed.of_isIntegrallyClosedIn _ (Localization M)⟩

/-- **A ring integrally closed in a reduced Artinian ring has domains as local rings.** If `R` is
integrally closed in a reduced Artinian ring `E`, for instance a finite product of fields, then
every localization of `R` at a prime is a domain. -/
theorem isDomain_localization_atPrime [IsArtinianRing E] [IsReduced E] (Q : Ideal R) [Q.IsPrime] :
    IsDomain (Localization.AtPrime Q) :=
  (isDomain_and_isIntegrallyClosed_localization_atPrime E Q).1

/-- **A ring integrally closed in a reduced Artinian ring is normal.** If `R` is integrally closed
in a reduced Artinian ring `E`, for instance a finite product of fields, then every localization
of `R` at a prime is integrally closed. -/
theorem isIntegrallyClosed_localization_atPrime [IsArtinianRing E] [IsReduced E] (Q : Ideal R)
    [Q.IsPrime] : IsIntegrallyClosed (Localization.AtPrime Q) :=
  (isDomain_and_isIntegrallyClosed_localization_atPrime E Q).2

end IsIntegrallyClosedIn
