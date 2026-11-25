/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Points of the valuation spectrum with prescribed support and centre

A point `v` of `Spv R` that is bounded by `1` on all of `R` has two prime ideals attached to it:
its support `{r : v(r) = 0}` and its centre `{r : v(r) < 1}`, and the support lies inside the
centre. This file shows that every such pair arises: for prime ideals `𝔮 ⊆ 𝔭` of a commutative
ring `R` there is a point of `Spv R`, bounded by `1` on `R`, with support `𝔮` and centre `𝔭`
(`TauCeti.ValuationSpectrum.exists_supp_eq_and_valuation_lt_one_iff_mem`).

The point is the classical one. The localisation of the domain `R ⧸ 𝔮` at the image of `𝔭` is a
local subring of the fraction field of `R ⧸ 𝔮`, and a valuation subring dominating it
(`LocalSubring.exists_le_valuationSubring`) has a valuation which, pulled back to `R`, is bounded
by `1`, vanishes exactly on `𝔮` and is below `1` exactly on `𝔭`.

This is the algebraic input to the surjectivity of the specialization map of a Tate Huber pair,
`Spa(A, A⁺) → Spec(A⁺ ⧸ A°°)`: there `𝔭` is the prime of `A⁺` to be hit and `𝔮` a prime below
it that avoids a pseudouniformiser.

## Main results

* `TauCeti.ValuationSpectrum.exists_supp_eq_and_valuation_lt_one_iff_mem`: for primes `𝔮 ⊆ 𝔭` of
  `R`, some point of `Spv R` bounded by `1` on `R` has support `𝔮` and centre `𝔭`.

## References

* [The Stacks Project](https://stacks.math.columbia.edu/tag/00IA), Tag 00IA: every local subring
  of a field is dominated by a valuation subring.
-/

public section

namespace TauCeti.ValuationSpectrum

variable {R : Type*} [CommRing R]

/-- **Every pair of primes `𝔮 ⊆ 𝔭` is the support and centre of a valuation.** For prime ideals
`𝔮 ⊆ 𝔭` of `R`, some point `v` of `Spv R` is bounded by `1` on `R`, has support `𝔮`, and takes
values strictly below `1` exactly on `𝔭`. -/
theorem exists_supp_eq_and_valuation_lt_one_iff_mem {𝔮 𝔭 : Ideal R} [𝔮.IsPrime] [𝔭.IsPrime]
    (h : 𝔮 ≤ 𝔭) :
    ∃ v : Spv R, v.supp = 𝔮 ∧ (∀ r, v.valuation r ≤ 1) ∧ ∀ r, v.valuation r < 1 ↔ r ∈ 𝔭 := by
  classical
  -- `g : R → K = Frac(R ⧸ 𝔮)` has kernel `𝔮`; its corestriction to its range is onto
  let K := FractionRing (R ⧸ 𝔮)
  let g : R →+* K := (algebraMap (R ⧸ 𝔮) K).comp (Ideal.Quotient.mk 𝔮)
  have hkerg : RingHom.ker g = 𝔮 := by
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (R ⧸ 𝔮) K), Ideal.mk_ker]
  have hker : RingHom.ker g.rangeRestrict = 𝔮 := by rw [RingHom.ker_rangeRestrict, hkerg]
  have hgr : Function.Surjective g.rangeRestrict := g.rangeRestrict_surjective
  -- the image `P` of `𝔭` in the range of `g` is prime, and pulls back to `𝔭`
  let P : Ideal g.range := 𝔭.map g.rangeRestrict
  have : P.IsPrime := Ideal.map_isPrime_of_surjective hgr (hker.symm ▸ h)
  have hP (r : R) : g.rangeRestrict r ∈ P ↔ r ∈ 𝔭 := by
    rw [← Ideal.mem_comap, Ideal.comap_map_of_surjective' _ hgr, hker, sup_eq_left.mpr h]
  -- a valuation subring `V` dominating the localisation of the range of `g` at `P`
  obtain ⟨V, hle, hloc⟩ := (LocalSubring.ofPrime g.range P).exists_le_valuationSubring
  have hmem (r : R) : g r ∈ V := hle (LocalSubring.le_ofPrime _ _ (g.rangeRestrict r).property)
  -- domination: `g r` is a unit of `V` exactly when `r ∉ 𝔭`
  have hunit (r : R) : IsUnit (⟨g r, hmem r⟩ : V) ↔ r ∉ 𝔭 := by
    rw [← hP, ← Ideal.mem_primeCompl_iff, ← IsLocalization.AtPrime.isUnit_to_map_iff
      (LocalSubring.ofPrime g.range P).toSubring P, ← isUnit_map_iff (Subring.inclusion hle)]
    -- both elements of `V` have underlying element `g r` of `K`
    rfl
  have hval (r : R) : V.valuation (g r) < 1 ↔ r ∈ 𝔭 := by
    rw [← not_iff_not, ← hunit, V.valuation_eq_one_iff, not_lt]
    exact ⟨fun h1 ↦ le_antisymm ((V.valuation_le_one_iff _).mpr (hmem r)) h1, Eq.ge⟩
  let w : Valuation R V.ValueGroup := V.valuation.comap g
  refine ⟨ofValuation w, ?_, fun r ↦ ?_, fun r ↦ ?_⟩
  · ext r
    rw [supp_ofValuation, Valuation.mem_supp_iff, Valuation.comap_apply, Valuation.zero_iff,
      ← RingHom.mem_ker, hkerg]
  · exact (isEquiv_valuation_ofValuation w).le_one_iff_le_one.mpr
      ((V.valuation_le_one_iff _).mpr (hmem r))
  · exact (isEquiv_valuation_ofValuation w).lt_one_iff_lt_one.trans (hval r)

end TauCeti.ValuationSpectrum
