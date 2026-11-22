/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.SInteger.IntegralClosure
public import TauCeti.RingTheory.DedekindDomain.SInteger.Spectrum
public import TauCeti.RingTheory.DedekindDomain.SInteger.Unit

/-!
# Enlarging the set of inverted primes

Let `R` be a Dedekind domain with fraction field `K`, and let `S ⊆ S'` be arbitrary sets of
height-one primes of `R`. The `S`-integers are contained in the `S'`-integers
(`Set.integer_mono`), and this file studies the inclusion `𝒪_S → 𝒪_{S'}`, Mathlib's
`Subalgebra.inclusion (Set.integer_mono K h)`. It is the identity for `S = S'` and the inclusions
compose in towers `S ⊆ S' ⊆ S''`, by Mathlib's `Subalgebra.inclusion_self` and
`Subalgebra.inclusion_inclusion`.

* **Uniqueness.** Every `R`-algebra map `𝒪_S → 𝒪_{S'}` is the inclusion inside `K`
  (`IsDedekindDomain.coe_algebraMap_integer`), so the algebra structure in the localization
  statement below is no extra datum.
* **Localization.** Whenever `𝒪_{S'}` is the localization of `R` at a submonoid `M`, it is the
  localization of `𝒪_S` at the image of `M`
  (`IsDedekindDomain.integer_isLocalization_algebraMapSubmonoid`). When the class group of `R` is
  torsion, Mathlib's instance `IsDedekindDomain.isLocalizationSInteger` supplies this for the
  candidate denominators `M = Localization.submonoid S'`, for every `S'`; then `𝒪_S → 𝒪_{S'}`
  is the localization of `𝒪_S` at the images of the candidate denominators for `S'`. Given
  denominator presentations of both rings, the induced map of localizations is the inclusion
  (`IsDedekindDomain.coe_isLocalization_map_integer`).
* **Primes.** Exactly the newly inverted primes disappear: a height-one prime of `𝒪_S` extends to
  the unit ideal of `𝒪_{S'}` exactly when the prime of `R` below it lies in `S'`
  (`IsDedekindDomain.map_inclusion_asIdeal_eq_top_iff`); a prime over `v ∉ S'` extends to the
  prime of `𝒪_{S'}` above `v`. Contraction along the inclusion
  (`IsDedekindDomain.integerPrimeUnderOfSubset`) is injective on height-one primes, preserves the
  prime of `R` below, and its image consists of the primes of `𝒪_S` lying over no prime of `S'`.
* **Units.** Under Mathlib's identification `Set.unitEquivUnitsInteger` of `S`-units with units
  of `𝒪_S`, the inclusion on units is the inclusion `S.unit K ≤ S'.unit K`
  (`IsDedekindDomain.units_map_inclusion_unitEquivUnitsInteger`).
* **Extensions.** For an integral extension `R ⊆ B` of Dedekind domains with fraction fields
  `K ⊆ L`, the passage from `𝒪_{K,S}` to its integral closure `𝒪_{L,T}`, for `T` the primes of
  `B` above `S`, commutes with enlarging `S`
  (`IsDedekindDomain.algebraMap_integer_primesAbove_comp_inclusion`).

Without a torsion hypothesis `𝒪_{S'}` need not be a localization of `R` at all (see the module
docstring of `TauCeti/RingTheory/DedekindDomain/SInteger/Localization.lean`), but the statements
on primes, units and extensions hold for arbitrary `R`, `S` and `S'`.

## References

* Charles A. Weibel, *The K-book: An Introduction to Algebraic K-theory*, Chapter I, Section 3,
  pp. 21–22, and Chapter V, 6.1, p. 406.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

open scoped nonZeroDivisors

variable {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K]
  [IsFractionRing R K]

namespace IsDedekindDomain

variable {S S' : Set (HeightOneSpectrum R)}

section Localization

/-- **Every `R`-algebra map between rings of `S`-integers is the inclusion inside `K`.** An
`S`-integer `x = a / b` with `a, b ∈ R` satisfies `x * b = a`, and an `R`-algebra map preserves
this equation, which determines the image inside `K`. -/
theorem coe_algebraMap_integer [Algebra (S.integer K) (S'.integer K)]
    [IsScalarTower R (S.integer K) (S'.integer K)] (x : S.integer K) :
    (algebraMap (S.integer K) (S'.integer K) x : K) = x := by
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj R⁰ (x : K)
  have hb : algebraMap R K b ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.property
  have hx : x * algebraMap R (S.integer K) b = algebraMap R (S.integer K) a :=
    Subtype.ext hab
  have hy := congrArg (fun y : S'.integer K ↦ (y : K))
    (congrArg (algebraMap (S.integer K) (S'.integer K)) hx)
  simp only [map_mul, ← IsScalarTower.algebraMap_apply, Subalgebra.coe_mul,
    Subalgebra.coe_algebraMap] at hy
  exact mul_right_cancel₀ hb (hy.trans hab.symm)

/-- **Enlarging the inverted primes is a localization.** If the `S'`-integers are the
localization of `R` at a submonoid `M`, they are the localization of the `S`-integers at the
image of `M`, for any `R`-algebra structure on `𝒪_{S'}` over `𝒪_S` (which is necessarily the
inclusion, by `coe_algebraMap_integer`). When the class group of `R` is torsion, Mathlib's
instance `IsDedekindDomain.isLocalizationSInteger` provides `M = Localization.submonoid S'`, the
candidate denominators for `S'`. -/
theorem integer_isLocalization_algebraMapSubmonoid [Algebra (S.integer K) (S'.integer K)]
    [IsScalarTower R (S.integer K) (S'.integer K)] (M : Submonoid R)
    [IsLocalization M (S'.integer K)] :
    IsLocalization (Algebra.algebraMapSubmonoid (S.integer K) M) (S'.integer K) where
  map_units := by
    rintro ⟨_, m, hm, rfl⟩
    rw [← IsScalarTower.algebraMap_apply]
    exact IsLocalization.map_units _ ⟨m, hm⟩
  surj z := by
    obtain ⟨⟨a, m⟩, hz⟩ := IsLocalization.surj M z
    refine ⟨⟨algebraMap R _ a, ⟨_, m, m.property, rfl⟩⟩, ?_⟩
    simpa only [← IsScalarTower.algebraMap_apply] using hz
  exists_of_eq {x y} hxy := ⟨1, by
    rw [Subtype.ext_iff, coe_algebraMap_integer, coe_algebraMap_integer, ← Subtype.ext_iff] at hxy
    rw [hxy]⟩

/-- **The inclusion is the map of denominator presentations.** Given presentations
`𝒪_S = M⁻¹R` and `𝒪_{S'} = M'⁻¹R` with `M ≤ M'`, the map of localizations induced by the identity
of `R` is the inclusion inside `K`. -/
theorem coe_isLocalization_map_integer {M M' : Submonoid R} [IsLocalization M (S.integer K)]
    [IsLocalization M' (S'.integer K)] (hM : M ≤ M') (x : S.integer K) :
    (IsLocalization.map (S'.integer K) (RingHom.id R) hM x : K) = x := by
  let : Algebra (S.integer K) (S'.integer K) :=
    (IsLocalization.map (S'.integer K) (RingHom.id R) hM : S.integer K →+* S'.integer K).toAlgebra
  have : IsScalarTower R (S.integer K) (S'.integer K) :=
    .of_algebraMap_eq fun r ↦
      (IsLocalization.map_eq (S := S.integer K) (Q := S'.integer K) (g := RingHom.id R) hM r).symm
  exact coe_algebraMap_integer K x

end Localization

section Primes

/-- Extending a height-one prime of `𝒪_S` to `𝒪_{S'}` gives the extension to `𝒪_{S'}` of the
prime of `R` below it. -/
theorem map_inclusion_asIdeal (h : S ⊆ S') (P : HeightOneSpectrum (S.integer K)) :
    P.asIdeal.map (Subalgebra.inclusion (Set.integer_mono K h)) =
      (integerPrimeUnder K S P).asIdeal.map (algebraMap R (S'.integer K)) := by
  conv_lhs => rw [← integer_map_comap_eq K S P.asIdeal, ← integerPrimeUnder_asIdeal]
  rw [← Ideal.map_coe, Ideal.map_map, AlgHom.comp_algebraMap]

/-- **Exactly the newly inverted primes disappear.** A height-one prime of `𝒪_S` extends to the
unit ideal of `𝒪_{S'}` exactly when the prime of `R` below it lies in `S'`. -/
theorem map_inclusion_asIdeal_eq_top_iff (h : S ⊆ S') (P : HeightOneSpectrum (S.integer K)) :
    P.asIdeal.map (Subalgebra.inclusion (Set.integer_mono K h)) = ⊤ ↔
      integerPrimeUnder K S P ∈ S' := by
  rw [map_inclusion_asIdeal K h]
  exact ⟨fun htop ↦ by_contra fun hv ↦ integer_map_asIdeal_ne_top K S' hv htop,
    integer_map_asIdeal_eq_top K S'⟩

/-- A height-one prime of `𝒪_S` lying over a prime `v ∉ S'` of `R` extends to the prime of
`𝒪_{S'}` above `v`. -/
theorem map_inclusion_asIdeal_eq_integerPrimeOverOfNotMem (h : S ⊆ S')
    {P : HeightOneSpectrum (S.integer K)} (hP : integerPrimeUnder K S P ∉ S') :
    P.asIdeal.map (Subalgebra.inclusion (Set.integer_mono K h)) =
      (integerPrimeOverOfNotMem K S' hP).asIdeal := by
  rw [map_inclusion_asIdeal K h, integerPrimeOverOfNotMem_asIdeal]

/-- The height-one prime of `𝒪_S` below a height-one prime of `𝒪_{S'}`, for `S ⊆ S'`: its
contraction along the inclusion `𝒪_S → 𝒪_{S'}`. -/
noncomputable def integerPrimeUnderOfSubset (h : S ⊆ S') (P : HeightOneSpectrum (S'.integer K)) :
    HeightOneSpectrum (S.integer K) :=
  comapOfNeBot (Subalgebra.inclusion (Set.integer_mono K h)) P fun hbot ↦
    integer_comap_ne_bot K S' P.ne_bot <| by
      rw [← AlgHom.comp_algebraMap (Subalgebra.inclusion (Set.integer_mono K h)),
        ← Ideal.comap_comap, hbot]
      exact Ideal.comap_bot_of_injective _ fun a b hab ↦
        IsFractionRing.injective R K (congrArg Subtype.val hab)

@[simp]
lemma integerPrimeUnderOfSubset_asIdeal (h : S ⊆ S') (P : HeightOneSpectrum (S'.integer K)) :
    (integerPrimeUnderOfSubset K h P).asIdeal =
      P.asIdeal.comap (Subalgebra.inclusion (Set.integer_mono K h)) :=
  comapOfNeBot_asIdeal _ _ _

/-- Contracting a prime of `𝒪_{S'}` to `𝒪_S` and then to `R` is contracting it to `R`. -/
@[simp]
lemma integerPrimeUnder_integerPrimeUnderOfSubset (h : S ⊆ S')
    (P : HeightOneSpectrum (S'.integer K)) :
    integerPrimeUnder K S (integerPrimeUnderOfSubset K h P) = integerPrimeUnder K S' P :=
  HeightOneSpectrum.ext <| by
    rw [integerPrimeUnder_asIdeal, integerPrimeUnderOfSubset_asIdeal, integerPrimeUnder_asIdeal,
      ← Ideal.comap_coe (f := Subalgebra.inclusion _), Ideal.comap_comap, AlgHom.comp_algebraMap]

/-- The prime of `𝒪_{S'}` above `v ∉ S'` contracts to the prime of `𝒪_S` above `v`. -/
@[simp]
lemma integerPrimeUnderOfSubset_integerPrimeOverOfNotMem (h : S ⊆ S') {v : HeightOneSpectrum R}
    (hv : v ∉ S') :
    integerPrimeUnderOfSubset K h (integerPrimeOverOfNotMem K S' hv) =
      integerPrimeOverOfNotMem K S fun hvS ↦ hv (h hvS) := by
  rw [← integerPrimeOverOfNotMem_integerPrimeUnder K S (integerPrimeUnderOfSubset K h _)]
  simp

/-- Distinct height-one primes of `𝒪_{S'}` contract to distinct primes of `𝒪_S`. -/
theorem integerPrimeUnderOfSubset_injective (h : S ⊆ S') :
    Function.Injective (integerPrimeUnderOfSubset K h) := fun P Q hPQ ↦
  (integerHeightOneSpectrumEquiv K S').symm.injective <| Subtype.ext <| by
    simpa using congrArg (integerPrimeUnder K S) hPQ

/-- The height-one primes of `𝒪_S` below a prime of `𝒪_{S'}` are exactly those lying over no
prime of `S'`. -/
theorem range_integerPrimeUnderOfSubset (h : S ⊆ S') :
    Set.range (integerPrimeUnderOfSubset K h) = {P | integerPrimeUnder K S P ∉ S'} := by
  ext P
  refine ⟨?_, fun hP ↦ ⟨integerPrimeOverOfNotMem K S' hP, by simp⟩⟩
  rintro ⟨Q, rfl⟩
  simpa using integerPrimeUnder_notMem K S' Q

end Primes

section Units

/-- Under Mathlib's identification of `S`-units with the units of the `S`-integers, the inclusion
`𝒪_S → 𝒪_{S'}` acts on units as the inclusion of `S`-units into `S'`-units. -/
@[simp]
theorem units_map_inclusion_unitEquivUnitsInteger (h : S ⊆ S') (u : S.unit K) :
    Units.map (Subalgebra.inclusion (Set.integer_mono K h) : S.integer K →* S'.integer K)
        (S.unitEquivUnitsInteger K u) =
      S'.unitEquivUnitsInteger K (Subgroup.inclusion (Set.unit_mono K h) u) :=
  Units.ext <| Subtype.ext <| by simp [Set.unitEquivUnitsInteger]

end Units

section Extension

variable {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B] [Algebra.IsIntegral R B]
  (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L] [Algebra R L]
  [IsScalarTower R K L] [IsScalarTower R B L]

/-- **The `S`-integers of an extension are compatible with enlarging `S`.** For `S ⊆ S'` with
`T` and `T'` the primes of `B` above them, the square formed by the inclusions
`𝒪_{K,S} → 𝒪_{K,S'}` and `𝒪_{L,T} → 𝒪_{L,T'}` and the integral-closure maps
`𝒪_{K,S} → 𝒪_{L,T}` and `𝒪_{K,S'} → 𝒪_{L,T'}` commutes. -/
theorem algebraMap_integer_primesAbove_comp_inclusion (h : S ⊆ S') :
    (algebraMap (S'.integer K) ((primesAbove R B S').integer L)).comp
        (Subalgebra.inclusion (Set.integer_mono K h) : S.integer K →+* S'.integer K) =
      (Subalgebra.inclusion (Set.integer_mono L (primesAbove_mono R B h)) :
        (primesAbove R B S).integer L →+* (primesAbove R B S').integer L).comp
        (algebraMap (S.integer K) ((primesAbove R B S).integer L)) :=
  RingHom.ext fun _ ↦ Subtype.ext <| by simp

end Extension

end IsDedekindDomain
