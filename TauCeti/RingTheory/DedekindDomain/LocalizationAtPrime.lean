/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
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

The remaining results are the two bridges between `v` and `Oᵥ`. Downwards: an element of `K` that
comes from `Oᵥ` has `v`-adic valuation at most one; hence, by Mathlib's
`IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one`, an element that comes from
every `Oᵥ` comes from `O`. The latter is `O = ⋂ᵥ Oᵥ` inside `K`, and is what lets a property that
holds over every localisation descend to `O`. The ring-of-integers identification is stated for any
`IsLocalization.AtPrime` model of `Oᵥ` mapping to `K` over `O`, not only for
`Localization.AtPrime v.asIdeal` itself.

Sideways: `Oᵥ` is exactly the ring of integers of the `v`-adic valuation, and the discrete
valuation `Oᵥ` carries as a discrete valuation ring — Mathlib's
`IsDiscreteValuationRing.maximalIdeal Oᵥ`, the phrasing of every statement it makes over a discrete
valuation ring — is the `v`-adic valuation itself. Without that identification a result proved at
`Oᵥ` cannot be compared with the `v`-adic factorisation of an element of `O`.

## Main declarations

* `IsDedekindDomain.HeightOneSpectrum.isDiscreteValuationRing_localizationAtPrime`:
  `IsDiscreteValuationRing (Localization.AtPrime v.asIdeal)`, as an instance;
* `IsDedekindDomain.HeightOneSpectrum.isInteger_of_forall_isInteger_localizationAtPrime`:
  an element of `K` lying in every `Localization.AtPrime v.asIdeal` lies in `O`;
* `IsDedekindDomain.HeightOneSpectrum.isUnit_of_forall_isUnit_localizationAtPrime`:
  a nonzero element of `K` that is a unit in every such localisation is a unit of `O`;
* `IsDedekindDomain.HeightOneSpectrum.integers_valuation_of_isLocalizationAtPrime`:
  any model of `Oᵥ` is the ring of integers of the `v`-adic valuation on `K`;
* `IsDedekindDomain.HeightOneSpectrum.irreducible_algebraMap_localizationAtPrime`:
  a `v`-adic uniformiser of `O` is irreducible in `Oᵥ`;
* `IsDedekindDomain.HeightOneSpectrum.valuation_maximalIdeal_localizationAtPrime`:
  the valuation of `Oᵥ` as a discrete valuation ring is the `v`-adic valuation.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {O : Type*} [CommRing O] [IsDedekindDomain O] {K : Type*} [Field K] [Algebra O K]
  [IsFractionRing O K] (v : HeightOneSpectrum O)

/-- The localisation of a Dedekind domain at a height-one prime is a discrete valuation ring. With
the `Algebra`, `IsScalarTower` and `IsFractionRing` instances of
`TauCeti/RingTheory/Localization/AtPrime.lean`, this is what lets Mathlib's theory over a discrete
valuation ring and its fraction field apply at each height-one prime of `O`. -/
instance isDiscreteValuationRing_localizationAtPrime :
    IsDiscreteValuationRing (Localization.AtPrime v.asIdeal) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain O v.ne_bot _

/-- Any model of the localisation at `v` mapping to `K` over `O` is the ring of integers
of the `v`-adic valuation. This gives the valuation bound on its elements as `map_le_one`,
and makes the unit and divisibility API of `Valuation.Integers` available. -/
theorem integers_valuation_of_isLocalizationAtPrime (S : Type*) [CommRing S]
    [Algebra O S] [IsLocalization.AtPrime S v.asIdeal] [Algebra S K] [IsScalarTower O S K] :
    (v.valuation K).Integers S where
  hom_inj := by
    let := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization v.asIdeal.primeCompl S K
    exact IsFractionRing.injective S K
  map_le_one x := by
    -- Write `x = r / s` with `s ∉ v`: the valuation of `s` is one and that of `r` at most one.
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective v.asIdeal.primeCompl x
    dsimp only
    rw [← IsLocalization.mk'_eq_algebraMap_mk'_of_submonoid_le (S := S) (T := K)
      v.asIdeal.primeCompl_le_nonZeroDivisors, valuation_of_mk',
      (v.intValuation_eq_one_iff_mem_primeCompl s).mpr s.2, div_one]
    exact v.intValuation_le_one r
  exists_of_le_one {x} hx := by
    obtain ⟨a, s, hs⟩ := v.exists_primeCompl_mul_eq_of_integer x hx
    refine ⟨IsLocalization.mk' S a s, ?_⟩
    rw [← IsLocalization.mk'_eq_algebraMap_mk'_of_submonoid_le
      (S := S) (T := K) v.asIdeal.primeCompl_le_nonZeroDivisors,
      IsLocalization.mk'_eq_iff_eq_mul]
    exact hs.symm

/-- **`O` is the intersection of its localisations at height-one primes**, inside `K`: an element
of `K` that comes from `Localization.AtPrime v.asIdeal` for every `v` comes from `O`. This is the
form in which a property holding over every localisation descends to `O`, as for the coefficients
of a Weierstrass equation in
`WeierstrassCurve.isIntegral_of_forall_isIntegral_localizationAtPrime`. -/
theorem isInteger_of_forall_isInteger_localizationAtPrime (x : K)
    (h : ∀ v : HeightOneSpectrum O, IsLocalization.IsInteger (Localization.AtPrime v.asIdeal) x) :
    IsLocalization.IsInteger O x := by
  -- Coming from every localisation bounds every `v`-adic valuation by one, which is the
  -- hypothesis of `mem_integers_of_valuation_le_one`.
  refine RingHom.mem_rangeS.mpr
    (RingHom.mem_range.mp (mem_integers_of_valuation_le_one K x fun v => ?_))
  obtain ⟨r, rfl⟩ := RingHom.mem_rangeS.mp (h v)
  exact (v.integers_valuation_of_isLocalizationAtPrime
    (Localization.AtPrime v.asIdeal)).map_le_one r

/-- A nonzero element of the fraction field which is the image of a unit in every height-one
localisation is the image of a unit of the Dedekind domain. The nonzero assumption also covers
the case where the height-one spectrum is empty. -/
theorem isUnit_of_forall_isUnit_localizationAtPrime (x : K)
    (hx : x ≠ 0)
    (h : ∀ v : HeightOneSpectrum O, ∃ u : (Localization.AtPrime v.asIdeal)ˣ,
      algebraMap (Localization.AtPrime v.asIdeal) K u = x) :
    ∃ u : Oˣ, algebraMap O K u = x := by
  obtain ⟨a, ha⟩ := isInteger_of_forall_isInteger_localizationAtPrime x
    fun v => let ⟨u, hu⟩ := h v; ⟨u, hu⟩
  obtain ⟨b, hb⟩ := isInteger_of_forall_isInteger_localizationAtPrime x⁻¹ fun v => by
    obtain ⟨u, hu⟩ := h v
    exact ⟨↑u⁻¹, by rw [map_units_inv, hu]⟩
  have hab : a * b = 1 := IsFractionRing.injective O K (by
    rw [map_mul, ha, hb, map_one, mul_inv_cancel₀ hx])
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, ha⟩

/-- **A `v`-adic uniformiser of `O` is irreducible in the localisation at `v`.** This is what
identifies the discrete valuation of `Oᵥ` with the `v`-adic valuation in
`valuation_maximalIdeal_localizationAtPrime`. -/
theorem irreducible_algebraMap_localizationAtPrime {ϖ : O}
    (hϖ : v.intValuation ϖ = WithZero.exp (-1 : ℤ)) :
    Irreducible (algebraMap O (Localization.AtPrime v.asIdeal) ϖ) := by
  have hv := v.integers_valuation_of_isLocalizationAtPrime
    (Localization.AtPrime v.asIdeal) (K := FractionRing O)
  have hϖL : v.valuation (FractionRing O)
      (algebraMap (Localization.AtPrime v.asIdeal) (FractionRing O)
        (algebraMap O (Localization.AtPrime v.asIdeal) ϖ)) = WithZero.exp (-1 : ℤ) := by
    rw [← IsScalarTower.algebraMap_apply, valuation_of_algebraMap, hϖ]
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
  refine le_antisymm (fun y hy => Ideal.mem_span_singleton.2 (hv.le_iff_dvd.1 ?_)) ?_
  · -- A nonunit of `Oᵥ` has image of valuation less than one, hence at most `exp (-1)`.
    rw [hϖL]
    refine (WithZero.lt_mul_exp_iff_le (by simp)).1 ?_
    rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    exact lt_of_le_of_ne (hv.map_le_one y) fun h =>
      (IsLocalRing.mem_maximalIdeal y).1 hy (hv.isUnit_iff_valuation_eq_one.2 h)
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe,
      IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rw [hv.isUnit_iff_valuation_eq_one, hϖL] at hu
    simp at hu

/-- **The valuation of the discrete valuation ring `Oᵥ` is the `v`-adic valuation.** Mathlib's
theory of minimal Weierstrass equations, like every other statement it makes over a discrete
valuation ring, is phrased through `IsDiscreteValuationRing.maximalIdeal Oᵥ`; this lemma reads such
a statement as one about `v`, which is what lets the local data at the height-one primes of `O` be
assembled into a single object over `O`. -/
theorem valuation_maximalIdeal_localizationAtPrime (x : K) :
    (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).valuation K x =
      v.valuation K x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := v.intValuation_exists_uniformizer
  have hirr := v.irreducible_algebraMap_localizationAtPrime hϖ
  -- In the fraction field, every nonzero element is a unit times an integer power of `ϖ`.
  obtain ⟨n, u, rfl⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hirr hx
  have hleft := (IsDiscreteValuationRing.maximalIdeal _).intValuation_singleton
    hirr.ne_zero hirr.maximalIdeal_eq
  have hu : (IsDiscreteValuationRing.maximalIdeal (Localization.AtPrime v.asIdeal)).intValuation
      (u : Localization.AtPrime v.asIdeal) = 1 := by
    simp [IsDiscreteValuationRing.maximalIdeal]
  have hright : v.valuation K (algebraMap (Localization.AtPrime v.asIdeal) K
      (algebraMap O (Localization.AtPrime v.asIdeal) ϖ)) = WithZero.exp (-1 : ℤ) := by
    rw [← IsScalarTower.algebraMap_apply, valuation_of_algebraMap, hϖ]
  simp only [Units.smul_def, Algebra.smul_def, map_mul, map_zpow₀, valuation_of_algebraMap,
    hleft, hu, one_mul, hright,
    (v.integers_valuation_of_isLocalizationAtPrime
      (Localization.AtPrime v.asIdeal) (K := K)).valuation_unit u]

end IsDedekindDomain.HeightOneSpectrum

end
