/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic

/-!
# Discrete valuation rings of a finite extension of a local field

Let `K` be a nonarchimedean local field and `M` a finite extension of `K`. A discrete valuation
ring `S` with fraction field `M` which lies over `𝒪[K]` through a local homomorphism defines a
valuation on `M` whose restriction to `K` has valuation ring `𝒪[K]`. Since the valuation of `K`
extends uniquely to `M` (`TauCeti.finiteExtensionValuation_isEquiv`), the valuation of `S` is the
extended valuation, and in particular `S` lies inside `𝒪[M]`.

This is what lets a statement phrased with an abstract discrete valuation ring dominating `𝒪[K]`,
such as potential good reduction, be read over the ring of integers of a finite extension.

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
  [IsNonarchimedeanLocalField K] {M : Type*} [Field M] [Algebra K M] [Module.Finite K M]
  {S : Type*} [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [Algebra S M]
  [IsFractionRing S M] [Algebra 𝒪[K] S] [IsLocalHom (algebraMap 𝒪[K] S)]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [Module.Finite K M] in
/-- The valuation of a discrete valuation ring `S` with fraction field `M`, dominating `𝒪[K]`,
restricts to the valuation class of `K`: an element of `K` is integral at `S` exactly when it lies
in `𝒪[K]`. -/
theorem isEquiv_comap_valuation_maximalIdeal_of_isLocalHom
    (h : (algebraMap S M).comp (algebraMap 𝒪[K] S) = (algebraMap K M).comp (algebraMap 𝒪[K] K)) :
    (((IsDiscreteValuationRing.maximalIdeal S).valuation M).comap (algebraMap K M)).IsEquiv
      (valuation K) := by
  set w := (IsDiscreteValuationRing.maximalIdeal S).valuation M
  -- An element `r` of `𝒪[K]` has the `S`-valuation of its image in `S`.
  have hw (r : 𝒪[K]) : w (algebraMap K M r) = w (algebraMap S M (algebraMap 𝒪[K] S r)) := by
    rw [← RingHom.comp_apply, h, RingHom.comp_apply]
    rfl
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · -- If `x ∉ 𝒪[K]`, then `x⁻¹` lies in the maximal ideal of `𝒪[K]`, hence of `S`.
    by_contra hx'
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp at hx'
    have hinv : valuation K x⁻¹ < 1 := by
      rw [map_inv₀]
      exact inv_lt_one_of_one_lt₀ (not_le.1 hx')
    set r : 𝒪[K] := ⟨x⁻¹, hinv.le⟩
    have hr : ¬IsUnit r := (Valuation.Integer.not_isUnit_iff_valuation_lt_one).2 hinv
    have hrS : ¬IsUnit (algebraMap 𝒪[K] S r) := fun hu ↦ hr (isUnit_of_map_unit _ _ hu)
    have hlt : w (algebraMap K M x⁻¹) < 1 := by
      rw [show x⁻¹ = (r : K) from rfl, hw,
        HeightOneSpectrum.valuation_lt_one_iff_mem]
      exact (IsLocalRing.mem_maximalIdeal _).2 hrS
    rw [map_inv₀, map_inv₀] at hlt
    have hpos : 0 < w (algebraMap K M x) := by
      rw [zero_lt_iff, Valuation.ne_zero_iff, map_ne_zero_iff _ (algebraMap K M).injective]
      exact hx0
    rw [Valuation.comap_apply] at hx
    exact ((one_le_inv₀ hpos).2 hx).not_gt hlt
  · rw [Valuation.comap_apply, show x = ((⟨x, hx⟩ : 𝒪[K]) : K) from rfl, hw]
    exact HeightOneSpectrum.valuation_le_one _ _

/-- **A discrete valuation ring dominating `𝒪[K]` defines the extended valuation.** Let `S` be a
discrete valuation ring with fraction field a finite extension `M` of `K`, lying over `𝒪[K]`
through a local homomorphism. Its valuation is equivalent to the valuation of any valuative
relation on `M` extending that of `K`. -/
theorem isEquiv_valuation_maximalIdeal_of_isLocalHom [ValuativeRel M] [ValuativeExtension K M]
    (h : (algebraMap S M).comp (algebraMap 𝒪[K] S) = (algebraMap K M).comp (algebraMap 𝒪[K] K)) :
    ((IsDiscreteValuationRing.maximalIdeal S).valuation M).IsEquiv (valuation M) :=
  finiteExtensionValuation_isEquiv (isEquiv_comap_valuation_maximalIdeal_of_isLocalHom h)
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
