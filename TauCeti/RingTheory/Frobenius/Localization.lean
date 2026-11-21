/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Frobenius.Splitting
public import TauCeti.RingTheory.Localization.PowMul

/-!
# Localization of Frobenius splittings

A Frobenius splitting `σ` extends uniquely to any localization, with formula
`σ(a / s ^ p) = σ(a) / s`. Equivalently, its value on `a / s` is
`σ(a * s ^ (p - 1)) / s`. No regularity condition on the denominators is needed.
In particular the construction includes localizations that are the zero ring.

Compatible ideals remain compatible after localization. Conversely, compatibility of an
ideal of the localization is equivalent to compatibility of its contraction. Uniqueness
ensures that successive restrictions of a splitting agree, as needed when restricting
splittings on affine charts to their overlaps. The splitting on a compatible quotient
commutes with localization.

## References

* M. Brion and S. Kumar, *Frobenius splitting methods in geometry and representation theory*,
  Birkhäuser (2005), §1.1.
-/

public section

namespace TauCeti.FrobeniusSplitting

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]
  (σ : FrobeniusSplitting R p)

section

variable (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]

/-- Extend a Frobenius splitting to a localization. The extension is uniquely determined
by agreement on the original ring and twisted linearity. -/
noncomputable def localization : FrobeniusSplitting S p where
  char_eq_zero := by rw [← map_natCast (algebraMap R S), σ.char_eq_zero, map_zero]
  toAddMonoidHom := σ.toAddMonoidHom.localizationOfPowMul M S σ.map_pow_mul
  map_pow_mul' := σ.toAddMonoidHom.localizationOfPowMul_pow_mul M S σ.map_pow_mul
  map_one' := by
    simpa only [map_one, coe_toAddMonoidHom] using
      σ.toAddMonoidHom.localizationOfPowMul_algebraMap M S σ.map_pow_mul 1

/-- The localized splitting removes a p-th power from a denominator. -/
@[simp↓]
theorem localization_mk'_pow (a : R) (s : M) :
    σ.localization M S (IsLocalization.mk' S a (s ^ p)) =
      IsLocalization.mk' S (σ a) s :=
  σ.toAddMonoidHom.localizationOfPowMul_mk'_pow M S σ.map_pow_mul a s

/-- The power-denominator formula for a denominator written as a subtype constructor. -/
@[simp]
theorem localization_mk'_pow_mk (a s : R) (hs : s ∈ M) {hsp : s ^ p ∈ M} :
    σ.localization M S (IsLocalization.mk' S a ⟨s ^ p, hsp⟩) =
      IsLocalization.mk' S (σ a) ⟨s, hs⟩ := by
  rw [← SubmonoidClass.mk_pow s hs, localization_mk'_pow]

/-- Localization of a splitting agrees with it on the original ring. -/
@[simp]
theorem localization_algebraMap (a : R) :
    σ.localization M S (algebraMap R S a) = algebraMap R S (σ a) :=
  σ.toAddMonoidHom.localizationOfPowMul_algebraMap M S σ.map_pow_mul a

/-- The denominator formula on an ordinary fraction; denominators may be zero divisors. -/
theorem localization_mk' (a : R) (s : M) :
    σ.localization M S (IsLocalization.mk' S a s) =
      IsLocalization.mk' S (σ (a * (s : R) ^ (p - 1))) s :=
  σ.toAddMonoidHom.localizationOfPowMul_mk' M S σ.map_pow_mul a s

variable {S} in
include M in
/-- A ring homomorphism out of a localization commutes with splittings if it does so
on the image of the original ring. -/
theorem map_eq_of_isLocalization {T : Type*} [CommRing T] {τ : FrobeniusSplitting S p}
    {υ : FrobeniusSplitting T p} (f : S →+* T)
    (h : ∀ a : R, f (τ (algebraMap R S a)) = υ (f (algebraMap R S a))) (x : S) :
    f (τ x) = υ (f x) :=
  IsLocalization.map_apply_eq_of_map_pow_mul M f τ.map_pow_mul υ.map_pow_mul h x

variable {S} in
include M in
/-- Two splittings on a localization are equal if they agree on the image of the original ring. -/
theorem ext_of_isLocalization {τ υ : FrobeniusSplitting S p}
    (h : ∀ a : R, τ (algebraMap R S a) = υ (algebraMap R S a)) : τ = υ :=
  DFunLike.coe_injective (IsLocalization.eq_of_map_pow_mul M τ.map_pow_mul υ.map_pow_mul h)

/-- The localized splitting of `σ` is the unique splitting on `S` agreeing with `σ` along
`algebraMap R S`. -/
theorem localization_unique {τ : FrobeniusSplitting S p}
    (hτ : ∀ a, τ (algebraMap R S a) = algebraMap R S (σ a)) :
    τ = σ.localization M S :=
  ext_of_isLocalization M fun a ↦ (hτ a).trans (σ.localization_algebraMap M S a).symm

/-- An algebra homomorphism between localizations of the same base ring intertwines
the extensions of the same splitting. -/
theorem localization_map {T : Type*} [CommRing T] [Algebra R T]
    (N : Submonoid R) [IsLocalization N T] (f : S →ₐ[R] T) (x : S) :
    f (σ.localization M S x) = σ.localization N T (f x) :=
  map_eq_of_isLocalization M (f : S →+* T) (fun a ↦ by
    simp only [AlgHom.coe_toRingHom, localization_algebraMap, AlgHom.commutes]) x

/-- Localizing in two stages agrees with direct localization whenever both presentations
of the final ring are given. This is the restriction law for repeated affine overlaps. -/
theorem localization_localization (N : Submonoid S) (L : Submonoid R)
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsLocalization N T] [IsLocalization L T] :
    (σ.localization M S).localization N T = σ.localization L T := by
  ext x
  exact DFunLike.congr_fun
    (σ.toAddMonoidHom.localizationOfPowMul_localizationOfPowMul M S σ.map_pow_mul N L T) x

/-- Compatibility of an ideal in a localization can be tested on its contraction. -/
theorem localization_isCompatible_iff (J : Ideal S) :
    (σ.localization M S).IsCompatible J ↔ σ.IsCompatible (J.comap (algebraMap R S)) := by
  rw [isCompatible_iff, isCompatible_iff]
  exact σ.toAddMonoidHom.localizationOfPowMul_mem_iff M S σ.map_pow_mul J

end

namespace IsCompatible

variable {σ} {I : Ideal R} (hI : σ.IsCompatible I)
  (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]

include hI in
/-- Extension of a compatible ideal is compatible with the localized splitting. -/
theorem localization_map :
    (σ.localization M S).IsCompatible (I.map (algebraMap R S)) :=
  ((σ.localization M S).isCompatible_iff _).mpr fun _ hx ↦
    σ.toAddMonoidHom.localizationOfPowMul_mem_map M S σ.map_pow_mul
      ((σ.isCompatible_iff I).mp hI) hx

/-- Descending to a compatible quotient and localizing commute. -/
theorem localization_map_quotient :
    (hI.localization_map M S).quotient = hI.quotient.localization
      (Algebra.algebraMapSubmonoid (R ⧸ I) M) (S ⧸ I.map (algebraMap R S)) := by
  apply localization_unique
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  have h (b : R) : algebraMap (R ⧸ I) (S ⧸ I.map (algebraMap R S)) (Ideal.Quotient.mk I b) =
      Ideal.Quotient.mk _ (algebraMap R S b) := Ideal.quotientMap_mk
  rw [h, quotient_mk, quotient_mk, localization_algebraMap, h]

end IsCompatible

end TauCeti.FrobeniusSplitting
