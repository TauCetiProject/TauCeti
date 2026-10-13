/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic

/-!
# Discrete valuation rings of an algebraic extension of a local field

Let `K` be a nonarchimedean local field and `M` an algebraic extension of `K`. A discrete
valuation
ring `S` with fraction field `M` which lies over `𝒪[K]` through a local homomorphism defines a
valuation on `M` whose restriction to `K` has valuation ring `𝒪[K]`
(`TauCeti.isEquiv_comap_valuation_maximalIdeal_of_isLocalHom`). Since the valuation of `K`
extends uniquely to `M` (`TauCeti.algebraicExtensionValuation_isEquiv`), the valuation of `S` is the
extended valuation, and in particular `S` lies inside `𝒪[M]`.

This is what lets a statement phrased with an abstract discrete valuation ring dominating `𝒪[K]`,
such as potential good reduction, be read over the ring of integers of an algebraic extension.

## Main results

* `TauCeti.isEquiv_valuation_maximalIdeal_of_isLocalHom`: the valuation of `S` is equivalent to
  the valuation of `M`.
* `TauCeti.valuation_algebraMap_le_one_of_isLocalHom`: the elements of `S` have valuation at most
  `1` in `M`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 (Theorem 4.8).
-/

public section

open ValuativeRel IsDedekindDomain

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] {M : Type*} [Field M] [Algebra K M] [Algebra.IsAlgebraic K M]
  {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra S M]
  [IsFractionRing S M] [Algebra 𝒪[K] S] [IsLocalHom (algebraMap 𝒪[K] S)]

/-- **A discrete valuation ring dominating `𝒪[K]` defines the extended valuation.** Let `S` be a
discrete valuation ring with fraction field an algebraic extension `M` of `K`, lying over
`𝒪[K]`
through a local homomorphism. Its valuation is equivalent to the valuation of any valuative
relation on `M` extending that of `K`. -/
theorem isEquiv_valuation_maximalIdeal_of_isLocalHom [ValuativeRel M] [ValuativeExtension K M]
    (h : (algebraMap S M).comp (algebraMap 𝒪[K] S) = (algebraMap K M).comp (algebraMap 𝒪[K] K)) :
    ((IsDiscreteValuationRing.maximalIdeal S).valuation M).IsEquiv (valuation M) :=
  algebraicExtensionValuation_isEquiv (isEquiv_comap_valuation_maximalIdeal_of_isLocalHom h)
    (ValuativeRel.isEquiv ((valuation M).comap (algebraMap K M)) (valuation K))

/-- **A discrete valuation ring dominating `𝒪[K]` lies in `𝒪[M]`.** Every element of a discrete
valuation ring `S` with fraction field `M`, lying over `𝒪[K]` through a local homomorphism, has
valuation at most `1` for any valuative relation on `M` extending that of `K`. -/
theorem valuation_algebraMap_le_one_of_isLocalHom [ValuativeRel M] [ValuativeExtension K M]
    (h : (algebraMap S M).comp (algebraMap 𝒪[K] S) = (algebraMap K M).comp (algebraMap 𝒪[K] K))
    (s : S) : valuation M (algebraMap S M s) ≤ 1 :=
  (isEquiv_valuation_maximalIdeal_of_isLocalHom h).le_one_iff_le_one.1
    (HeightOneSpectrum.valuation_le_one _ s)

end TauCeti
