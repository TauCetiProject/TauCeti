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
import Mathlib.RingTheory.DedekindDomain.AdicValuation

/-!
# Overrings of a Dedekind domain in its fraction field

An *overring* of `A` here is a subalgebra of the fraction field `K` of `A`, that is, a ring between
`A` and `K`. Every such ring is integrally closed: its localizations at maximal ideals are
localizations of `A` too, and those are valuation rings of `K`, or `K` itself over the zero prime.

Nothing about integral closures of `A` in *larger* fields is needed for this, which is why it lives
apart from `RingTheory/IntegralClosure/`.

## Main results

* `Subalgebra.isIntegrallyClosed_overring`: every subalgebra of the fraction field of a Dedekind
  domain is integrally closed.

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
