/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Unramified.LocalStructure
import TauCeti.RingTheory.Etale.Normal
import TauCeti.RingTheory.Ideal.Height
import TauCeti.RingTheory.IntegralClosure.GoingDown
import TauCeti.RingTheory.KrullDimension.Basic
import TauCeti.RingTheory.KrullDimension.Integral
import TauCeti.RingTheory.QuasiFinite.Height

/-!
# Unramified algebras over a normal base

Let `R` be a Noetherian ring, `S` a finite type `R`-algebra and `q` a prime of `S` over `p`, at
which `S` is unramified over `R`. If `R_p` is a normal domain and `q` has height at least that of
`p`, then `S` is étale over `R` at `q`. Compare SGA 1, Exposé I, Théorème 9.5 (ii), on unramified
morphisms to a normal scheme; here the hypothesis is a comparison of dimensions. It shows that
the unramified points of a dominant morphism of integral schemes, locally of finite type over a
locally Noetherian normal scheme, are étale, without purity of the branch locus. Since
unramifiedness at `q` already forces `ht q ≤ ht p` (`Ideal.height_le_height_of_quasiFiniteAt`),
the height condition says that the two heights agree.

Over a Noetherian integrally closed domain `R` which is not a field, an integral torsion-free
algebra of essentially finite type that is unramified at its primes of height one is also
unramified at its primes of height zero. Height-zero primes are the generic points of `Spec S`;
each is a generization of a height-one prime, so the hypothesis of purity of the branch locus
(Stacks, Lemma 58.21.4 (0BMB)), which only constrains codimension-one points, extends to them.

## Proof

By the local structure of unramified algebras
(`Algebra.IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn`), there are `f ∉ q` and a standard
étale `R`-algebra `A` with a surjection `A → S_f`. Let `Q` be the prime of `A` under `q`. The
induced map `A_Q → S_q` is surjective. As `A` is étale over `R` and `R_p` is a normal domain,
`A_Q` is a (normal) domain (Stacks, Lemma 10.163.9 (033C)), and `ht Q ≤ ht p ≤ ht q` because `A`
is quasi-finite over `R`. A surjection from a domain of finite dimension onto a ring of at least
the same dimension is injective (`RingHom.injective_of_surjective_of_ringKrullDim_le`), so
`S_q ≅ A_Q` is formally étale over `R`.

## Main results

* `Algebra.IsEtaleAt.of_isUnramifiedAt_of_height_le`: an algebra of finite type over a Noetherian
  ring, unramified at `q` over `p` with `R_p` a normal domain and `ht p ≤ ht q`, is étale at `q`.
* `Algebra.IsUnramifiedAt.of_forall_height_eq_one`: over a Noetherian integrally closed domain
  which is not a field, an integral torsion-free algebra unramified at every prime of height one
  is unramified at every prime of height at most one.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé I, Théorème 9.5.
* [Stacks Project, Lemma 10.163.9](https://stacks.math.columbia.edu/tag/033C), normality of
  étale algebras over a normal ring.
* [Stacks Project, Lemma 58.21.4](https://stacks.math.columbia.edu/tag/0BMB), purity of the branch
  locus, whose unramifiedness hypothesis is at the points of codimension one.
-/

public section

open IsLocalRing

namespace Algebra

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Unramified algebras over a normal base of the same dimension are étale** (compare SGA 1,
Exposé I, Théorème 9.5 (ii)). Let `S` be a finite type algebra over a Noetherian ring `R`,
unramified at a prime `q` over `p`. If `R_p` is a normal domain and `ht p ≤ ht q`, then `S` is
étale over `R` at `q`. -/
theorem IsEtaleAt.of_isUnramifiedAt_of_height_le [IsNoetherianRing R] [FiniteType R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] [q.LiesOver p] [IsUnramifiedAt R q]
    [IsDomain (Localization.AtPrime p)] [IsIntegrallyClosed (Localization.AtPrime p)]
    (h : p.height ≤ q.height) : IsEtaleAt R q := by
  obtain ⟨f, hfq, P, φ, hφ⟩ := IsUnramifiedAt.exists_hasStandardEtaleSurjectionOn (R := R) q
  let T := Localization.AtPrime q
  -- The composite `ψ : P.Ring → S_f → S_q`, which hits every element of `S`.
  have hf (y : Submonoid.powers f) : IsUnit (IsScalarTower.toAlgHom R S T y) := by
    obtain ⟨_, n, rfl⟩ := y
    exact IsLocalization.map_units T (⟨f ^ n, q.primeCompl.pow_mem hfq n⟩ : q.primeCompl)
  let ψ : P.Ring →ₐ[R] T := (IsLocalization.liftAlgHom hf).comp φ
  have hψ (s : S) : ∃ a, ψ a = algebraMap S T s := by
    obtain ⟨a, ha⟩ := hφ (algebraMap S _ s)
    exact ⟨a, by simp [ψ, ha, IsLocalization.lift_eq]⟩
  -- The prime `Q` of `P.Ring` under the maximal ideal of `S_q` lies over `p`.
  let Q := (maximalIdeal T).comap ψ
  have : (maximalIdeal T).LiesOver p := .trans _ q p
  have : Q.LiesOver p := inferInstance
  obtain rfl := Q.over_def p
  let D := Localization.AtPrime Q
  have hunit (y : Q.primeCompl) : IsUnit (ψ y) :=
    notMem_maximalIdeal.mp (Ideal.mem_comap.not.mp (Ideal.mem_primeCompl_iff.mp y.2))
  let θ : D →ₐ[R] T := IsLocalization.liftAlgHom hunit
  have hsurj : Function.Surjective θ := by
    intro z
    obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨a, ha⟩ := hψ s
    obtain ⟨b, hb⟩ := hψ t
    have hbQ : b ∈ Q.primeCompl := by
      rw [Ideal.mem_primeCompl_iff, Ideal.mem_comap, hb]
      exact notMem_maximalIdeal.mpr (IsLocalization.map_units T t)
    refine ⟨IsLocalization.mk' D a ⟨b, hbQ⟩, ?_⟩
    simp only [θ, IsLocalization.coe_liftAlgHom]
    rw [IsLocalization.lift_mk'_spec]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, ha, hb]
    exact (IsLocalization.mk'_spec' T s t).symm
  -- `A_Q` is a Noetherian local domain of dimension at most that of `S_q`, so `θ` is injective.
  have := TauCeti.Algebra.Etale.isDomain_localization_atPrime_of_localization_under R Q
  have := FiniteType.isNoetherianRing R P.Ring
  have hD : ringKrullDim D ≤ ringKrullDim T := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q D,
      IsLocalization.AtPrime.ringKrullDim_eq_height q T]
    exact_mod_cast (Ideal.height_le_height_of_quasiFiniteAt (Q.under R) Q).trans h
  have hinj : Function.Injective θ :=
    θ.toRingHom.injective_of_surjective_of_ringKrullDim_le hsurj hD
  exact FormallyEtale.of_equiv (AlgEquiv.ofBijective θ ⟨hinj, hsurj⟩)

/-- Let `S` be an integral, torsion-free algebra of essentially finite type over a Noetherian
integrally closed domain `R` which is not a field. If `S` is unramified over `R` at every prime of
height one, then it is unramified over `R` at every prime of height at most one. -/
theorem IsUnramifiedAt.of_forall_height_eq_one [IsDomain R] [IsIntegrallyClosed R]
    [IsNoetherianRing R] [Algebra.IsIntegral R S] [Module.IsTorsionFree R S] [EssFiniteType R S]
    (hR : ¬IsField R) (h : ∀ (Q : Ideal S) [Q.IsPrime], Q.height = 1 → IsUnramifiedAt R Q)
    (q : Ideal S) [q.IsPrime] (hq : q.height ≤ 1) : IsUnramifiedAt R q := by
  rcases hq.lt_or_eq with hq | hq
  swap
  · exact h q hq
  -- `q` has height zero, so by going down it lies over the zero ideal of `R`.
  have hq0 : q.under R = ⊥ := by
    rw [← Ideal.height_eq_zero_iff_eq_bot, ← q.height_eq_height_under_of_isIntegral_of_hasGoingDown]
    exact Order.lt_one_iff.mp hq
  obtain ⟨p, _, hp1⟩ := Ideal.exists_isPrime_height_eq_one_of_not_isField hR
  -- By going up, `q` lies below a prime `Q` over `p`, which has height one by going down. The
  -- unramified locus is open, hence stable under generization, so it contains `q`.
  obtain ⟨Q, hqQ, hQ, hQp⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime p q (hq0 ▸ bot_le)
  have hQ1 : Q.height = 1 := by
    rw [Q.height_eq_height_under_of_isIntegral_of_hasGoingDown (R := R), hQp, hp1]
  exact (isOpen_unramifiedLocus (R := R) (A := S)).stableUnderGeneralization
    ((PrimeSpectrum.le_iff_specializes ⟨q, ‹_›⟩ ⟨Q, hQ⟩).mp hqQ) (h Q hQ1)

end Algebra
