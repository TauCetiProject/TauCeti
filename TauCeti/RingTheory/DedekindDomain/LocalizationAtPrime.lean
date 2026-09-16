/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import TauCeti.RingTheory.Localization.AtPrime

/-!
# The localisation of a Dedekind domain at a height-one prime, inside its fraction field

Let `O` be a Dedekind domain with fraction field `K` and let `v` be a height-one prime of `O`.
Mathlib's `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` says that the
localisation `Oᵥ := Localization.AtPrime v.asIdeal` is a discrete valuation ring, as a theorem with
the nonzero-prime hypothesis explicit. This file records it as an instance for height-one primes,
which carry that hypothesis as `v.ne_bot`. Together with the `Algebra Oᵥ K`, `IsScalarTower O Oᵥ K`
and `IsFractionRing Oᵥ K` instances of `TauCeti/RingTheory/Localization/AtPrime.lean`, every result
Mathlib states over a discrete valuation ring `R` with fraction field `K` — in particular its theory
of integral and minimal Weierstrass equations — now applies to `Oᵥ ⊆ K` by instance search, for
arbitrary `O` and `K`.

The one lemma is the bridge from the local rings back to `O`: an element of `K` that comes from
`Oᵥ` has `v`-adic valuation at most one. Combined with Mathlib's
`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`, which is `O = ⋂ᵥ Oᵥ` in
valuation terms, it lets a property that holds over every localisation descend to `O`. It is stated
for any `IsLocalization.AtPrime` model of `Oᵥ` mapping to `K` over `O`, not only for
`Localization.AtPrime v.asIdeal` itself.

## Main declarations

* `IsDedekindDomain.HeightOneSpectrum.isDiscreteValuationRing_localizationAtPrime`:
  `IsDiscreteValuationRing (Localization.AtPrime v.asIdeal)`, as an instance;
* `IsDedekindDomain.HeightOneSpectrum.valuation_algebraMap_le_one_of_isLocalization_atPrime`:
  `v (x) ≤ 1` for `x` in the image of the localisation at `v`.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {O : Type*} [CommRing O] [IsDedekindDomain O] {K : Type*} [Field K] [Algebra O K]
  [IsFractionRing O K] (v : HeightOneSpectrum O)

/-- The localisation of a Dedekind domain at a height-one prime is a discrete valuation ring. This
is Mathlib's `IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain` made an instance:
a height-one prime is nonzero by definition, so the theorem's `P ≠ ⊥` hypothesis is `v.ne_bot`. -/
instance isDiscreteValuationRing_localizationAtPrime :
    IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O v.ne_bot _

/-- **Elements of the localisation at `v` have `v`-adic valuation at most one.** Writing `x` as
`r / s` with `s ∉ v`, the valuation of `s` is one and that of `r` is at most one. Stated for any
`IsLocalization.AtPrime` model `S` of the localisation with a map to `K` over `O`; the instances
above make `Localization.AtPrime v.asIdeal` such a model. -/
theorem valuation_algebraMap_le_one_of_isLocalization_atPrime {S : Type*} [CommRing S]
    [Algebra O S] [IsLocalization.AtPrime S v.asIdeal] [Algebra S K] [IsScalarTower O S K]
    (x : S) : v.valuation K (algebraMap S K x) ≤ 1 := by
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl x
  dsimp only
  rw [← IsLocalization.mk'_eq_algebraMap_mk'_of_submonoid_le (S := S) (T := K)
    v.asIdeal.primeCompl_le_nonZeroDivisors, valuation_of_mk',
    (v.intValuation_eq_one_iff_mem_primeCompl s).mpr s.2, div_one]
  exact v.intValuation_le_one r

end IsDedekindDomain.HeightOneSpectrum

end
