/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
public import TauCeti.RingTheory.Valuation.ValuationRing

/-!
# The valuation of a discrete valuation ring on its own elements

Let `R` be a discrete valuation ring with fraction field `K`, and let `v` be the valuation on `K`
attached to the maximal ideal of `R` (`IsDiscreteValuationRing.maximalIdeal`). Mathlib's
`IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem` reads `v r < 1`, for `r : R`, as
membership in the ideal underlying that height-one prime. This file restates it with the local
ring's maximal ideal, and with divisibility by a uniformiser. On `R` itself, the `𝔪`-adic
valuation `intValuation` compares elements by divisibility and vanishes only at `0`.

It also compares the valuation of a discrete valuation ring `S` with that of a valued field `K`
whose valuation ring maps to `S` through a local homomorphism: the valuation of `S`, restricted
along `K → Frac(S)`, is equivalent to the valuation of `K`.

## Main results

* `TauCeti.IsDiscreteValuationRing.valuation_algebraMap_lt_one_iff_mem`: `v r < 1` exactly when
  `r` lies in the maximal ideal.
* `TauCeti.IsDiscreteValuationRing.intValuation_le_intValuation_iff_dvd`: on `R`, the `𝔪`-adic
  valuation satisfies `v x ≤ v y` exactly when `y ∣ x`.
* `IsDedekindDomain.HeightOneSpectrum.supp_intValuation`: the adic valuation of a height-one
  prime of a Dedekind domain has zero support.
* `Irreducible.valuation_algebraMap_lt_one_iff_dvd` and
  `Irreducible.valuation_algebraMap_eq_one_iff_not_dvd`: for a uniformiser `ϖ`, `v r < 1` exactly
  when `ϖ ∣ r`, and `v r = 1` exactly when `ϖ ∤ r`.
* `TauCeti.isEquiv_comap_valuation_maximalIdeal_of_isLocalHom`: a discrete valuation ring
  dominating the valuation ring of `K` restricts to the valuation class of `K`.
-/

public section

open IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

namespace TauCeti.IsDiscreteValuationRing

/-- An element of a discrete valuation ring has valuation less than one in the fraction field
exactly when it lies in the maximal ideal. -/
theorem valuation_algebraMap_lt_one_iff_mem (r : R) :
    valuation K (_root_.IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K r) < 1 ↔
      r ∈ IsLocalRing.maximalIdeal R :=
  -- `(maximalIdeal R).asIdeal` is by definition `IsLocalRing.maximalIdeal R`
  valuation_lt_one_iff_mem _ r

/-- **The `𝔪`-adic valuation of a discrete valuation ring compares elements by divisibility**:
`v x ≤ v y` exactly when `y ∣ x`. -/
@[simp]
theorem intValuation_le_intValuation_iff_dvd (x y : R) :
    (_root_.IsDiscreteValuationRing.maximalIdeal R).intValuation x ≤
      (_root_.IsDiscreteValuationRing.maximalIdeal R).intValuation y ↔ y ∣ x := by
  refine Valuation.le_iff_dvd _ (intValuation_le_one _) (fun a ha ↦ ?_) (fun a ha ↦ ?_)
  · exact (intValuation_lt_one_iff_mem _ a).mpr ((IsLocalRing.mem_maximalIdeal a).mpr ha)
  · by_contra h
    exact intValuation_ne_zero _ a h ha

end TauCeti.IsDiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum

/-- The adic valuation of a height-one prime of a Dedekind domain vanishes only at `0`. -/
@[simp]
theorem supp_intValuation {A : Type*} [CommRing A] [IsDedekindDomain A]
    (v : HeightOneSpectrum A) : v.intValuation.supp = ⊥ := by
  ext x
  rw [Valuation.mem_supp_iff, Ideal.mem_bot]
  exact ⟨fun h ↦ by_contra fun hx ↦ v.intValuation_ne_zero x hx h, fun h ↦ h ▸ map_zero _⟩

end IsDedekindDomain.HeightOneSpectrum

namespace Irreducible

variable {K} {ϖ : R}

/-- An element of a discrete valuation ring has valuation less than one in the fraction field
exactly when the uniformiser divides it. -/
theorem valuation_algebraMap_lt_one_iff_dvd (hϖ : Irreducible ϖ) (r : R) :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K r) < 1 ↔ ϖ ∣ r := by
  rw [TauCeti.IsDiscreteValuationRing.valuation_algebraMap_lt_one_iff_mem, hϖ.maximalIdeal_eq,
    Ideal.mem_span_singleton]

/-- An element of a discrete valuation ring has valuation one in the fraction field exactly when
the uniformiser does not divide it. -/
theorem valuation_algebraMap_eq_one_iff_not_dvd (hϖ : Irreducible ϖ) (r : R) :
    valuation K (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R K r) = 1 ↔ ¬ ϖ ∣ r := by
  rw [← hϖ.valuation_algebraMap_lt_one_iff_dvd (K := K),
    (valuation_le_one (K := K) _ r).lt_iff_ne, not_not]

end Irreducible

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] {M : Type*} [Field M] [Algebra K M]
  {S : Type*} [CommRing S] [IsDomain S] [_root_.IsDiscreteValuationRing S] [Algebra S M]
  [IsFractionRing S M] [Algebra (ValuativeRel.valuation K).integer S]
  [IsLocalHom (algebraMap (ValuativeRel.valuation K).integer S)]

/-- The valuation of a discrete valuation ring `S` with fraction field `M`, dominating the
valuation ring of `K`, restricts to the valuation class of `K`: an element of `K` is integral at
`S` exactly when it lies in the valuation ring of `K`. -/
theorem isEquiv_comap_valuation_maximalIdeal_of_isLocalHom
    (h : (algebraMap S M).comp (algebraMap (ValuativeRel.valuation K).integer S) =
      (algebraMap K M).comp (algebraMap (ValuativeRel.valuation K).integer K)) :
    ((valuation M (_root_.IsDiscreteValuationRing.maximalIdeal S)).comap
      (algebraMap K M)).IsEquiv (ValuativeRel.valuation K) := by
  set w := valuation M (_root_.IsDiscreteValuationRing.maximalIdeal S)
  -- An element `y` of the valuation ring of `K` has the `S`-valuation of its image in `S`.
  have hw {y : K} (hy : y ∈ (ValuativeRel.valuation K).integer) :
      w (algebraMap K M y) =
        w (algebraMap S M (algebraMap (ValuativeRel.valuation K).integer S ⟨y, hy⟩)) := by
    rw [← RingHom.comp_apply, h, RingHom.comp_apply, Algebra.algebraMap_ofSubsemiring_apply]
  refine Valuation.isEquiv_iff_val_le_one.2 fun {x} ↦ ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · -- The valuation ring of `K` is integrally closed against `S`, which dominates it.
    obtain ⟨⟨y, hy⟩, rfl⟩ := ValuationRing.isInteger_of_isInteger_algebraMap
      (IsFractionRing.injective S M) h (IsDiscreteValuationRing.exists_lift_of_le_one hx)
    exact hy
  · rw [Valuation.comap_apply, hw hx]
    exact valuation_le_one _ _

end TauCeti
