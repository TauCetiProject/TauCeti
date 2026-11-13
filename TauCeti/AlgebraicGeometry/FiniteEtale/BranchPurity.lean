/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.FiniteEtale.FiniteNormal
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.Localization.LocalizationLocalization
import TauCeti.RingTheory.Unramified.Localization
import TauCeti.RingTheory.Unramified.Normal

/-!
# Purity of the branch locus from purity of local rings

Let `A` be a Noetherian integrally closed domain which is not a field, and `B` a finite
torsion-free `A`-algebra whose localizations at maximal ideals are normal domains. Suppose that
purity holds (`TauCeti.IsLocalRing.PurityHolds`) for the local ring `A_𝔭` at every prime `𝔭` of
height at least two: every finite étale cover of the punctured spectrum of `A_𝔭` extends across
the closed point. Then `B` is étale over `A` as soon as it is unramified over `A` at every prime of
height one. This is the finite algebraic form of purity of the branch locus (Stacks, Lemma
58.21.4 (0BMB)), deduced from purity of the local rings of the base; for a regular base, the
latter is purity for regular local rings (Stacks, Lemma 58.21.3 (0BMA)).

The proof is the induction on the dimension in Stacks' proof of 0BMB, run over the primes `𝔭`
of `A` ordered by height. If `𝔭` has height at most one, unramifiedness at the primes of `B`
over `𝔭` is the hypothesis, extended to height zero by going up and going down
(`Algebra.IsUnramifiedAt.of_forall_height_eq_one`). If `𝔭` has height at least two, localize
at `𝔭`: the algebra `B_𝔭` is finite, torsion free and normal over the normal local domain `A_𝔭`.
Its primes not over the closed point lie over primes of `A` strictly contained in `𝔭`, where
`B` is unramified by induction, hence étale since heights agree by going down
(`Algebra.IsEtaleAt.of_isUnramifiedAt_of_height_le`). Purity for `A_𝔭`, in its algebraic form
`TauCeti.Algebra.etale_of_finiteNormal_of_purityHolds`, makes `B_𝔭` étale over `A_𝔭`, so `B` is
unramified at the primes over `𝔭` (`Algebra.isUnramifiedAt_localization_iff`). Finally, a
prime of `B` unramified over `A` is étale over `A`, again because heights agree.

The hypothesis that `A` is not a field cannot be dropped: a purely inseparable field extension
has no prime of height one and is not étale.

## Main results

* `TauCeti.Algebra.etale_of_isUnramifiedAt_height_eq_one_of_purityHolds`: if purity holds for
  the local rings of `A` at primes of height at least two, then a finite torsion-free algebra
  with normal localizations, unramified at every prime of height one, is étale.

## References

* [The Stacks Project, Lemma 58.21.4](https://stacks.math.columbia.edu/tag/0BMB), purity of the
  branch locus, whose proof is this induction on the dimension.
* [The Stacks Project, Lemma 58.21.3](https://stacks.math.columbia.edu/tag/0BMA), purity for
  regular local rings, whose part (2) needs `B` torsion free over `A`.
-/

public section

open IsLocalRing

universe u

namespace TauCeti.Algebra

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsDomain A]
  [IsIntegrallyClosed A] [IsNoetherianRing A] [Module.Finite A B] [Module.IsTorsionFree A B]

/-- The inductive step: let `𝔭` be a prime of `A` of height at least two for which purity holds
for `A_𝔭`. If `B` is unramified over `A` at every prime lying over a prime strictly contained in
`𝔭`, then `B` is unramified over `A` at every prime lying over `𝔭`. -/
private theorem isUnramifiedAt_of_purityHolds_localization (𝔭 : Ideal A) [𝔭.IsPrime]
    (hpurity : IsLocalRing.PurityHolds (Localization.AtPrime 𝔭)) (h𝔭 : 2 ≤ 𝔭.height)
    (hnormal : ∀ (q : Ideal B) [q.IsPrime],
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q))
    (hlt : ∀ (q : Ideal B) [q.IsPrime], q.under A < 𝔭 → Algebra.IsUnramifiedAt A q)
    (q : Ideal B) [q.IsPrime] (hq : q.under A = 𝔭) : Algebra.IsUnramifiedAt A q := by
  let A𝔭 := Localization.AtPrime 𝔭
  let B𝔭 := Localization (Algebra.algebraMapSubmonoid B 𝔭.primeCompl)
  have : IsIntegrallyClosed A𝔭 :=
    isIntegrallyClosed_of_isLocalization _ _ 𝔭.primeCompl_le_nonZeroDivisors
  have : Module.IsTorsionFree A𝔭 B𝔭 :=
    IsLocalizedModule.isTorsionFree (IsScalarTower.toAlgHom A B B𝔭).toLinearMap 𝔭.primeCompl
  -- `B𝔭` is étale over `A𝔭` at every prime not over the closed point.
  have hetale (q' : Ideal B𝔭) [q'.IsPrime] (hq' : q'.under A𝔭 ≠ maximalIdeal A𝔭) :
      Algebra.IsEtaleAt A𝔭 q' := by
    let P := q'.under A𝔭
    have hP : P.under A < 𝔭 := by
      refine lt_of_le_of_ne ?_ fun h ↦
        hq' (Localization.AtPrime.eq_maximalIdeal_iff_under_eq.mp h)
      exact (Ideal.comap_mono (le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance))).trans_eq
        Localization.AtPrime.under_maximalIdeal
    have : Algebra.IsUnramifiedAt A (q'.under B) :=
      hlt _ (by rwa [Ideal.under_under, ← Ideal.under_under (B := A𝔭)])
    have : Algebra.IsUnramifiedAt A𝔭 q' :=
      (Algebra.isUnramifiedAt_localization_iff 𝔭.primeCompl q').mpr this
    have : IsIntegrallyClosed (Localization.AtPrime P) :=
      isIntegrallyClosed_of_isLocalization _ _ P.primeCompl_le_nonZeroDivisors
    have : q'.LiesOver P := ⟨rfl⟩
    exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_height_le P q'
      (q'.height_eq_height_under_of_isIntegral_of_hasGoingDown (R := A𝔭)).ge
  -- The localizations of `B𝔭` at its primes are those of `B`, hence normal domains.
  have hnormal' (𝔮 : Ideal B𝔭) [𝔮.IsMaximal] :
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮) := by
    let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization
      (Algebra.algebraMapSubmonoid B 𝔭.primeCompl) 𝔮
    obtain ⟨_, _⟩ := hnormal (𝔮.under B)
    exact ⟨e.symm.toMulEquiv.isDomain _, .of_equiv e.toRingEquiv⟩
  have hdim : 2 ≤ ringKrullDim A𝔭 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔭 A𝔭]
    exact WithBot.coe_le_coe.mpr h𝔭
  have := etale_of_finiteNormal_of_purityHolds hpurity hdim hnormal' hetale
  -- `q` survives in `B𝔭`, where `B𝔭` is unramified over `A𝔭`.
  have hd : Disjoint (Algebra.algebraMapSubmonoid B 𝔭.primeCompl : Set B) q :=
    ((Ideal.disjoint_map_primeCompl_iff_comap_le (f := algebraMap A B)).mpr hq.le).symm
  obtain ⟨q', _, rfl⟩ : ∃ q' : Ideal B𝔭, ∃ _ : q'.IsPrime, q'.under B = q :=
    ⟨_, IsLocalization.isPrime_of_isPrime_disjoint _ _ q ‹_› hd,
      IsLocalization.under_map_of_isPrime_disjoint _ _ ‹_› hd⟩
  have : Algebra.IsUnramifiedAt A𝔭 q' :=
    Algebra.FormallyUnramified.comp A𝔭 B𝔭 (Localization.AtPrime q')
  exact (Algebra.isUnramifiedAt_localization_iff 𝔭.primeCompl q').mp this

/-- **Purity of the branch locus from purity of local rings.** Let `A` be a Noetherian integrally
closed domain which is not a field, such that purity holds for the local ring `A_𝔭` at every
prime `𝔭` of height at least two. Let `B` be a finite torsion-free `A`-algebra whose
localizations at maximal ideals are normal domains. If `B` is unramified over `A` at every prime
of height one, then `B` is étale over `A`. -/
@[stacks 0BMB "finite algebras, from purity for the local rings of the base"]
theorem etale_of_isUnramifiedAt_height_eq_one_of_purityHolds (hA : ¬IsField A)
    (hpurity : ∀ (𝔭 : Ideal A) [𝔭.IsPrime], 2 ≤ 𝔭.height →
      IsLocalRing.PurityHolds (Localization.AtPrime 𝔭))
    (hnormal : ∀ (𝔮 : Ideal B) [𝔮.IsMaximal],
      IsDomain (Localization.AtPrime 𝔮) ∧ IsIntegrallyClosed (Localization.AtPrime 𝔮))
    (hunram : ∀ (q : Ideal B) [q.IsPrime], q.height = 1 → Algebra.IsUnramifiedAt A q) :
    Algebra.Etale A B := by
  -- The localizations of `B` at all primes are normal domains.
  have hnormal' (q : Ideal B) [q.IsPrime] :
      IsDomain (Localization.AtPrime q) ∧ IsIntegrallyClosed (Localization.AtPrime q) := by
    obtain ⟨𝔮, _, hq𝔮⟩ := q.exists_le_maximal Ideal.IsPrime.ne_top'
    obtain ⟨_, _⟩ := hnormal 𝔮
    obtain ⟨P, _, -, ⟨e⟩⟩ := IsLocalization.exists_ringEquiv_localization_atPrime
      𝔮.primeCompl (Localization.AtPrime 𝔮) q
      (Set.disjoint_left.mpr fun _ hx hxq ↦ hx (hq𝔮 hxq))
    have := IsLocalization.isDomain_localization P.primeCompl_le_nonZeroDivisors
    have := isIntegrallyClosed_of_isLocalization (Localization.AtPrime P) P.primeCompl
      P.primeCompl_le_nonZeroDivisors
    exact ⟨e.toMulEquiv.isDomain _, .of_equiv e.symm⟩
  -- `B` is unramified at every prime, by induction on the height of the prime below.
  have hall (n : ℕ∞) : ∀ (q : Ideal B) [q.IsPrime], (q.under A).height = n →
      Algebra.IsUnramifiedAt A q := by
    induction n using WellFoundedLT.induction with | _ n ih => ?_
    intro q _ hn
    have hq := q.height_eq_height_under_of_isIntegral_of_hasGoingDown (R := A)
    rcases le_or_gt (q.under A).height 1 with h1 | h2
    · exact Algebra.IsUnramifiedAt.of_forall_height_eq_one hA hunram q (hq ▸ h1)
    have h2 : 2 ≤ (q.under A).height := Order.add_one_le_of_lt h2
    refine isUnramifiedAt_of_purityHolds_localization _ (hpurity _ h2) h2 hnormal'
      (fun q' _ hlt ↦ ih _ ?_ q' rfl) q rfl
    rw [← hn]
    exact Ideal.height_strict_mono_of_isPrime hlt
  -- Heights agree by going down, so `B` is étale at every prime.
  have : Algebra.FinitePresentation A B :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  refine (Algebra.etaleLocus_eq_univ_iff_etale).mp (Set.eq_univ_of_forall fun q ↦ ?_)
  have := hall _ q.asIdeal rfl
  have : IsIntegrallyClosed (Localization.AtPrime (q.asIdeal.under A)) :=
    isIntegrallyClosed_of_isLocalization _ _ (q.asIdeal.under A).primeCompl_le_nonZeroDivisors
  exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_height_le (q.asIdeal.under A) q.asIdeal
    (q.asIdeal.height_eq_height_under_of_isIntegral_of_hasGoingDown (R := A)).ge

end TauCeti.Algebra
