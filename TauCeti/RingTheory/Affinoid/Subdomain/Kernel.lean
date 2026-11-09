/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Affinoid.Subdomain.Basic

import TauCeti.RingTheory.Affinoid.FiniteQuotient
import TauCeti.RingTheory.Ideal.KrullIntersection

/-!
# The kernel of restriction to an affinoid subdomain

Let `φ : A → B` represent a set `U` of classical points of an affinoid algebra `A` as an affinoid
subdomain. An element of `A` restricts to zero on the subdomain exactly when it lies in every power
of the maximal ideal of every point of `U`:

`ker φ = ⋂_{x ∈ U} ⋂_n 𝔪ₓⁿ`.

One inclusion holds because `φ` induces isomorphisms `A ⧸ 𝔪ₓⁿ ≃ B ⧸ 𝔪ₓⁿ B` for `x ∈ U`. For the
other, every maximal ideal of `B` is an extension `𝔪ₓ B` with `x ∈ U`, and the powers of all
maximal ideals of the noetherian ring `B` have zero intersection.

If `A` is a domain, Krull's intersection theorem gives `⋂_n 𝔪ₓⁿ = 0` for a single point `x`, so
restriction to a nonempty affinoid subdomain is injective. Without the domain hypothesis this
fails: in `K × K` the subdomain consisting of one of the two points is represented by a projection
`K × K → K`, which is not injective.

## Main results

* `TauCeti.IsAffinoidSubdomainMap.ker_eq_iInf_pow`: `ker φ = ⋂_{x ∈ U} ⋂_n 𝔪ₓⁿ`.
* `TauCeti.IsAffinoidSubdomainMap.injective`: for an affinoid domain `A` and nonempty `U`, the
  representing map `φ` is injective.

## References

* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §7.2.2.
-/

public section

namespace TauCeti.IsAffinoidSubdomainMap

universe u

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : Type u} [CommRing A] [Algebra K A] [CommRing B] [Algebra K B]
  {φ : A →ₐ[K] B} {U : Set (MaximalSpectrum A)}

/-- **The kernel of restriction to an affinoid subdomain.** If `φ : A → B` represents `U`, then an
element of `A` maps to zero in `B` exactly when it lies in every power of the maximal ideal of every
point of `U`. -/
theorem ker_eq_iInf_pow (h : IsAffinoidSubdomainMap φ U) (hA : IsAffinoidAlgebra K A) :
    RingHom.ker φ = ⨅ x ∈ U, ⨅ n : ℕ, x.asIdeal ^ n := by
  ext a
  simp only [RingHom.mem_ker, Ideal.mem_iInf]
  refine ⟨fun ha x hx n ↦ ?_, fun ha ↦ ?_⟩
  · -- `A ⧸ 𝔪ₓⁿ ≃ B ⧸ 𝔪ₓⁿ B` sends the class of `a` to the class of `φ a = 0`.
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    apply (h.quotientPowAlgEquiv hA hx n).injective
    rw [quotientPowAlgEquiv_mk, ha, map_zero, map_zero]
  · -- Every maximal ideal of `B` is `𝔪ₓ B` for some `x ∈ U`, so `φ a` lies in every power of
    -- every maximal ideal of the noetherian ring `B`.
    have := h.isAffinoidAlgebra.isNoetherianRing
    rw [← Ideal.mem_bot, ← Ideal.iInf_isMaximal_pow_eq_bot]
    simp only [Ideal.mem_iInf]
    intro m hm n _
    obtain ⟨y, rfl⟩ : ∃ y : MaximalSpectrum B, y.asIdeal = m := ⟨⟨m, hm⟩, rfl⟩
    rw [← h.map_maximalSpectrumComap_asIdeal hA y, ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ (ha _ (h.range_maximalSpectrumComap_subset ⟨y, rfl⟩) n)

/-- **Restriction to an affinoid subdomain of an affinoid domain is injective.** If `A` is a domain
and `φ : A → B` represents a nonempty set `U` of classical points, then `φ` is injective. -/
theorem injective [IsDomain A] (h : IsAffinoidSubdomainMap φ U) (hA : IsAffinoidAlgebra K A)
    (hU : U.Nonempty) : Function.Injective φ := by
  obtain ⟨x, hx⟩ := hU
  have := hA.isNoetherianRing
  rw [injective_iff_map_eq_zero]
  intro a ha
  -- By Krull's intersection theorem, the powers of the single maximal ideal `𝔪ₓ` meet in zero.
  rw [← Ideal.mem_bot, ← x.asIdeal.iInf_pow_eq_bot_of_isDomain x.isMaximal.ne_top, Ideal.mem_iInf]
  have ha' : a ∈ ⨅ x ∈ U, ⨅ n : ℕ, x.asIdeal ^ n := h.ker_eq_iInf_pow hA ▸ RingHom.mem_ker.mpr ha
  simp only [Ideal.mem_iInf] at ha'
  exact ha' x hx

end TauCeti.IsAffinoidSubdomainMap
