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
import TauCeti.RingTheory.KrullDimension.Basic
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

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé I, Théorème 9.5.
* [Stacks Project, Lemma 10.163.9](https://stacks.math.columbia.edu/tag/033C), normality of
  étale algebras over a normal ring.
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

end Algebra
