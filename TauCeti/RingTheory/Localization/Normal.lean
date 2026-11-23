/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Normal rings under isomorphisms and localization

A ring `R` is *normal* when its localization at every prime is an integrally closed domain
(Stacks, Definition 10.37.11 (00GV)); this is the condition
`∀ p [p.IsPrime], IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)`,
which `TauCeti.AlgebraicGeometry.isNormalScheme_Spec_iff_forall_localization` identifies with the
normality of `Spec R`. This file shows that normality is preserved by localization and by ring
isomorphisms. No Noetherian hypothesis is made.

## Main results

* `IsLocalization.forall_isDomain_and_isIntegrallyClosed`: a localization of a normal ring is
  normal (Stacks, Lemma 10.37.13 (030B)).
* `RingEquiv.forall_isDomain_and_isIntegrallyClosed`: normality is invariant under ring
  isomorphisms.

## References

* [Stacks Project, Definition 10.37.11](https://stacks.math.columbia.edu/tag/00GV) and
  [Lemma 10.37.13](https://stacks.math.columbia.edu/tag/030B).
-/

public section

/-- **A localization of a normal ring is normal.** If every localization of `R` at a prime is an
integrally closed domain, then so is every localization at a prime of a localization `S` of `R`:
it is a localization of `R` at a prime. Stacks, Lemma 10.37.13 (030B). -/
@[stacks 030B]
theorem IsLocalization.forall_isDomain_and_isIntegrallyClosed {R : Type*} [CommRing R]
    (M : Submonoid R)
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
    (Localization.AtPrime q) q
  let e : Localization.AtPrime (q.under R) ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv (q.under R).primeCompl _ (Localization.AtPrime q)).toRingEquiv
  obtain ⟨_, _⟩ := hR (q.under R)
  exact ⟨e.symm.toMulEquiv.isDomain _, IsIntegrallyClosed.of_equiv e⟩

/-- **Normality is invariant under ring isomorphisms.** If every localization of `R` at a prime is
an integrally closed domain and `R ≃+* S`, then so is every localization of `S` at a prime: along
`e`, the ring `S` is a localization of `R` at the trivial submonoid. -/
theorem RingEquiv.forall_isDomain_and_isIntegrallyClosed {R S : Type*} [CommRing R]
    [CommRing S] (e : R ≃+* S)
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (q : Ideal S) [q.IsPrime] :
    IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
  let := e.toRingHom.toAlgebra
  have : IsLocalization (⊥ : Submonoid R) R := IsLocalization.self bot_le
  have : IsLocalization (⊥ : Submonoid R) S :=
    IsLocalization.isLocalization_of_algEquiv ⊥ (AlgEquiv.ofRingEquiv (f := e) fun _ ↦ rfl)
  exact IsLocalization.forall_isDomain_and_isIntegrallyClosed ⊥ S hR q
