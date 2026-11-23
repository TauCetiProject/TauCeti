/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.AdicValuation.Ramification
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import TauCeti.RingTheory.DedekindDomain.IntegralClosure
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic

/-!
# `S`-integers in an extension of Dedekind domains

Let `R ⊆ B` be Dedekind domains with `B` integral over `R`, with fraction fields `K ⊆ L`, and let
`S` be an arbitrary set of height-one primes of `R`. Write `T = primesAbove R B S` for the full
set of primes of `B` lying over `S`. This file shows that the ring of `T`-integers of `L` is the
integral closure of the ring of `S`-integers of `K`:

`𝒪_{L,T} = integral closure of 𝒪_{K,S} in L`.

So the `S`-integers of an extension are obtained by inverting exactly the primes above `S`, and no
others. In fact `𝒪_{L,T}` is spanned over `𝒪_{K,S}` by `B`, so when `B` is a finite `R`-module (for
instance when `L / K` is finite and separable), `𝒪_{L,T}` is a finite projective `𝒪_{K,S}`-module,
of rank `[L : K]`. This is the finite projective algebra along which
`S`-integer rings are compared under a field extension, for instance by transfer maps.

Every element of `𝒪_{K,S}` is `w`-integral at each prime `w` of `B` outside `T`, since the
valuation at `w` is a positive power of the valuation at the prime of `R` below it. This gives
the algebra map `𝒪_{K,S} → 𝒪_{L,T}`, and integral elements lie in `𝒪_{L,T}` because that ring
is integrally closed. Conversely, the contraction to `R` of the denominator ideal in `B` of an
element of `𝒪_{L,T}` extends to the unit ideal of `𝒪_{K,S}`: a prime of `R` outside `S`
containing it would, by going up, lie under a prime of `B` outside `T` containing the denominator
ideal. Writing `1` through that ideal exhibits the element as an `𝒪_{K,S}`-combination of
elements of `B`, so `𝒪_{L,T}` is spanned over `𝒪_{K,S}` by `B`.

## Main definitions

* `IsDedekindDomain.integerAlgebraIntegerPrimesAbove`: the algebra structure of `𝒪_{L,T}` over
  `𝒪_{K,S}`, given by the inclusion `K → L`.

## Main results

* `IsDedekindDomain.mem_span_of_mem_integer_primesAbove`: every `T`-integer of `L` lies in the
  `𝒪_{K,S}`-span of the image of `B`.
* `IsDedekindDomain.mem_integer_primesAbove_iff`: an element of `L` is a `T`-integer exactly when
  it is integral over `𝒪_{K,S}`.
* `IsDedekindDomain.isIntegralClosure_integer_primesAbove`: `𝒪_{L,T}` is an integral closure of
  `𝒪_{K,S}` in `L`.
* `IsDedekindDomain.finrank_integer_primesAbove`: the rank of `𝒪_{L,T}` over `𝒪_{K,S}` is
  `[L : K]`.
* The instances `Module.Finite` of `𝒪_{L,T}` over `𝒪_{K,S}`, for `B` finite over `R` and for
  `L / K` finite and separable, and `Module.Projective`, whenever `𝒪_{L,T}` is finite.

## References

* Charles A. Weibel, *The K-book*, Chapter I, Section 3, p. 21, and Chapter V, 6.6.3, p. 410.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {B : Type*} [CommRing B] [IsDedekindDomain B] [Algebra R B]
  [Algebra.IsIntegral R B] (L : Type*) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra K L]
  [Algebra R L] [IsScalarTower R K L] [IsScalarTower R B L] (S : Set (HeightOneSpectrum R))

/-- The image in `L` of an `S`-integer of `K` is an integer at every prime of `B` not lying over
`S`: the valuation at such a prime is a positive power of the valuation at the prime below it. -/
theorem algebraMap_mem_integer_primesAbove (x : S.integer K) :
    algebraMap K L x ∈ (primesAbove R B S).integer L := by
  have : Module.IsTorsionFree R L := .trans_faithfulSMul R K L
  have : FaithfulSMul R B := .tower_bot R B L
  refine (Set.mem_integer_iff L _).mpr fun w hw ↦ ?_
  rw [← valuation_liesOver L (under R w) w]
  exact pow_le_one₀ zero_le
    (S.integer_valuation_le_one K x (mt (mem_primesAbove_iff R B S w).mpr hw))

/-- The ring of `T`-integers of `L`, for `T` the primes of `B` above `S`, as an algebra over the
ring of `S`-integers of `K`, through the inclusion `K → L`. -/
noncomputable instance integerAlgebraIntegerPrimesAbove :
    Algebra (S.integer K) ((primesAbove R B S).integer L) :=
  ((algebraMap (S.integer K) L).codRestrict _
    (algebraMap_mem_integer_primesAbove L S)).toAlgebra

/-- The algebra map from the `S`-integers of `K` to the `T`-integers of `L` is the inclusion
`K → L`. -/
@[simp] theorem coe_algebraMap_integer_primesAbove (x : S.integer K) :
    (algebraMap (S.integer K) ((primesAbove R B S).integer L) x : L) = algebraMap K L x :=
  (rfl)

/-- The inclusions `𝒪_{K,S} → 𝒪_{L,T} → L` compose to the inclusion `𝒪_{K,S} → K → L`. -/
instance : IsScalarTower (S.integer K) ((primesAbove R B S).integer L) L :=
  .of_algebraMap_eq fun _ ↦ (rfl)

/-- The inclusions `R → 𝒪_{K,S} → 𝒪_{L,T}` compose to the inclusion `R → 𝒪_{L,T}`. -/
instance : IsScalarTower R (S.integer K) ((primesAbove R B S).integer L) :=
  .of_algebraMap_eq fun r ↦ Subtype.ext (IsScalarTower.algebraMap_apply R K L r)

/-- A `T`-integer of `L` is an `𝒪_{K,S}`-combination of elements of `B`. The contraction to `R` of
its denominator ideal in `B` extends to the unit ideal of `𝒪_{K,S}`, so `1` is a combination of
elements `c` of `𝒪_{K,S}` with `c • x` in the image of `B`. -/
theorem mem_span_of_mem_integer_primesAbove {x : L}
    (hx : x ∈ (primesAbove R B S).integer L) :
    x ∈ Submodule.span (S.integer K) (Set.range (algebraMap B L)) := by
  set I := (Algebra.denIdeal (R := B) L x).under R
  -- the elements `c` of `𝒪_{K,S}` with `c • x` in the span form an ideal containing the image of
  -- `I`
  let N : Ideal (S.integer K) := (Submodule.span (S.integer K) (Set.range (algebraMap B L))).comap
    (LinearMap.toSpanSingleton (S.integer K) L x)
  have hIN : I.map (algebraMap R (S.integer K)) ≤ N := by
    refine Ideal.map_le_iff_le_comap.mpr fun r hr ↦ ?_
    obtain ⟨b, hb⟩ := (Algebra.mem_denIdeal_iff L).mp hr
    have hrx : algebraMap R (S.integer K) r • x = algebraMap B L b := by
      rw [Algebra.smul_def, ← IsScalarTower.algebraMap_apply,
        IsScalarTower.algebraMap_apply R B L, hb]
    simp only [N, Ideal.mem_comap, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, hrx]
    exact Submodule.subset_span ⟨b, rfl⟩
  suffices h : I.map (algebraMap R (S.integer K)) = ⊤ by
    simpa [N] using hIN (h ▸ Submodule.mem_top : (1 : S.integer K) ∈ _)
  -- otherwise `I` lies in a prime `v ∉ S` of `R`
  by_contra h
  have hden : Algebra.denIdeal (R := B) L x ≠ ⊥ := Algebra.denIdeal_ne_bot L (nonZeroDivisors B) x
  obtain ⟨v, hv, hIv⟩ := exists_notMem_le_of_integer_map_ne_top K S
    (fun h0 ↦ hden (Ideal.eq_bot_of_under_eq_bot h0)) h
  -- by going up, a prime `w` of `B` over `v` contains the denominator ideal of `x`, but `x` is
  -- integral at `w` since `w` does not lie over `S`
  obtain ⟨Q, hIQ, hQ, hQP⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal
    (Algebra.denIdeal L x) hIv
  let w : HeightOneSpectrum B := ⟨Q, hQ, fun h0 ↦ hden (le_bot_iff.mp (h0 ▸ hIQ))⟩
  have hw : w ∉ primesAbove R B S := by
    rwa [mem_primesAbove_iff, show under R w = v from HeightOneSpectrum.ext hQP]
  exact denIdeal_not_le L ((Set.mem_integer_iff L _).mp hx w hw) hIQ

/-- **The `T`-integers of `L` are the integral closure of the `S`-integers of `K`**, for `T` the
primes of `B` above `S`: an element of `L` is a `T`-integer exactly when it is integral over
`𝒪_{K,S}`. -/
theorem mem_integer_primesAbove_iff {x : L} :
    x ∈ (primesAbove R B S).integer L ↔ IsIntegral (S.integer K) x := by
  refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
  · -- the elements of `B` are integral over `R`, hence over `𝒪_{K,S}`
    refine (mem_integralClosure_iff _ _).mp ((Subalgebra.mem_toSubmodule _).mp
      (Submodule.span_le (p := (integralClosure (S.integer K) L).toSubmodule).mpr ?_
        (mem_span_of_mem_integer_primesAbove L S hx)))
    rintro _ ⟨b, rfl⟩
    exact ((Algebra.IsIntegral.isIntegral (R := R) b).map (IsScalarTower.toAlgHom R B L)).tower_top
  -- `x` is integral over the integrally closed ring `𝒪_{L,T}`, whose fraction field is `L`
  obtain ⟨y, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := (primesAbove R B S).integer L)).mp
    (hx.tower_top (A := (primesAbove R B S).integer L))
  exact y.property

/-- The `T`-integers of `L` are an integral closure of the `S`-integers of `K` in `L`. -/
instance isIntegralClosure_integer_primesAbove :
    IsIntegralClosure ((primesAbove R B S).integer L) (S.integer K) L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := (mem_integer_primesAbove_iff L S).symm.trans ⟨fun hx ↦ ⟨⟨x, hx⟩, rfl⟩,
    by rintro ⟨y, rfl⟩; exact y.property⟩

/-- The rank of the `T`-integers of `L` over the `S`-integers of `K` is the degree `[L : K]`. -/
theorem finrank_integer_primesAbove :
    Module.finrank (S.integer K) ((primesAbove R B S).integer L) = Module.finrank K L :=
  (IsFractionRing.finrank_eq (S.integer K) K ((primesAbove R B S).integer L) L).symm

/-- When `B` is a finite `R`-module, the `T`-integers of `L` are a finite module over the
`S`-integers of `K`: they are spanned by the images of generators of `B` over `R`. -/
instance [Module.Finite R B] : Module.Finite (S.integer K) ((primesAbove R B S).integer L) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := R) (M := B)
  let f := (IsScalarTower.toAlgHom R B L).toLinearMap
  -- the span of `B` over `𝒪_{K,S}` is spanned by the images of the generators `s`
  let P := Submodule.span (S.integer K) (Set.range (algebraMap B L))
  have hspan : P = Submodule.span (S.integer K) (f '' s) := by
    rw [← Submodule.span_span_of_tower R, ← Submodule.map_span, hs]
    simp [P, f, LinearMap.coe_range]
  have : IsNoetherian (S.integer K) P :=
    isNoetherian_of_fg_of_noetherian P (hspan ▸ Submodule.fg_span (s.finite_toSet.image f))
  -- the inclusion `𝒪_{L,T} → L` lands in that span
  let ι := (IsScalarTower.toAlgHom (S.integer K) ((primesAbove R B S).integer L) L).toLinearMap
  exact Module.Finite.of_injective
    (ι.codRestrict P fun y ↦ mem_span_of_mem_integer_primesAbove L S y.property)
    ((LinearMap.injective_codRestrict_iff _).mpr
      (IsIntegralClosure.algebraMap_injective _ (S.integer K) L))

/-- For a finite separable extension `L / K`, the `T`-integers of `L` are a finite module over the
`S`-integers of `K`. -/
instance [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Module.Finite (S.integer K) ((primesAbove R B S).integer L) :=
  IsIntegralClosure.finite (S.integer K) K L _

/-- The `T`-integers of `L` are a projective module over the `S`-integers of `K` whenever they are
a finite module. -/
instance [Module.Finite (S.integer K) ((primesAbove R B S).integer L)] :
    Module.Projective (S.integer K) ((primesAbove R B S).integer L) :=
  have := TauCeti.IsIntegralClosure.flat (S.integer K) L ((primesAbove R B S).integer L)
  have := Module.finitePresentation_of_finite (S.integer K) ((primesAbove R B S).integer L)
  Module.Flat.projective_of_finitePresentation

end IsDedekindDomain
