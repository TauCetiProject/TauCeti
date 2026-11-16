/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Frobenius.Splitting
public import Mathlib.RingTheory.Localization.Ideal

/-!
# Localization of Frobenius splittings

A Frobenius splitting `σ` extends uniquely to any localization, with formula
`σ(a / s ^ p) = σ(a) / s`. Equivalently, its value on `a / s` is
`σ(a * s ^ (p - 1)) / s`. No regularity condition on the denominators is needed.
In particular the construction includes localizations that are the zero ring.

Compatible ideals remain compatible after localization. Conversely, compatibility of an
ideal of the localization is equivalent to compatibility of its contraction. Uniqueness
ensures that successive restrictions of a splitting agree, as needed when restricting
splittings on affine charts to their overlaps.

## References

* M. Brion and S. Kumar, *Frobenius splitting methods in geometry and representation theory*,
  Birkhäuser (2005), §1.1.
-/

public section

namespace TauCeti.FrobeniusSplitting

variable {R : Type*} [CommRing R] {p : ℕ} [Fact p.Prime]
  (σ : FrobeniusSplitting R p) (M : Submonoid R)
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization M S]

include M in
private theorem map_apply_eq_of_map_eq {a b : R}
    (h : algebraMap R S a = algebraMap R S b) :
    algebraMap R S (σ a) = algebraMap R S (σ b) := by
  obtain ⟨s, hs⟩ := (IsLocalization.eq_iff_exists M S).mp h
  have hp : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_le
  have he : (s : R) ^ p * a = (s : R) ^ p * b := by
    simpa only [← mul_assoc, ← pow_succ, hp] using congrArg ((s : R) ^ (p - 1) * ·) hs
  have he' := congrArg (algebraMap R S) (congrArg σ he)
  simp only [σ.map_pow_mul, map_mul] at he'
  exact (IsLocalization.map_units S s).mul_right_inj.mp he'

private theorem fraction_eq_of_pow_fraction_eq {a b : R} {s t : M}
    (h : IsLocalization.mk' S a (s ^ p) = IsLocalization.mk' S b (t ^ p)) :
    IsLocalization.mk' S (σ a) s = IsLocalization.mk' S (σ b) t := by
  rw [IsLocalization.mk'_eq_iff_eq] at h ⊢
  have he := σ.map_apply_eq_of_map_eq M S h
  simpa only [SubmonoidClass.coe_pow, σ.map_pow_mul, map_mul] using he

private noncomputable def fractionMap (x : S) : S :=
  let h : ∃ q : R × M, IsLocalization.mk' S q.1 (q.2 ^ p) = x := by
    obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
    refine ⟨⟨a * (s : R) ^ (p - 1), s⟩, ?_⟩
    simpa only [SubmonoidClass.coe_pow, ← pow_succ',
      Nat.sub_add_cancel (Fact.out : p.Prime).one_le] using
      (IsLocalization.mk'_cancel (S := S) a s (s ^ (p - 1)))
  IsLocalization.mk' S (σ h.choose.1) h.choose.2

private theorem fractionMap_mk'_pow (a : R) (s : M) :
    σ.fractionMap M S (IsLocalization.mk' S a (s ^ p)) =
      IsLocalization.mk' S (σ a) s := by
  unfold fractionMap
  extract_lets h
  exact σ.fraction_eq_of_pow_fraction_eq M S h.choose_spec

private theorem fractionMap_add (x y : S) :
    σ.fractionMap M S (x + y) = σ.fractionMap M S x + σ.fractionMap M S y := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq M y
  -- Replace both denominators by p-th powers before using twisted linearity.
  have hrep (a : R) (s : M) :
      IsLocalization.mk' S a s =
        IsLocalization.mk' S (a * (s : R) ^ (p - 1)) (s ^ p) := by
    simpa only [SubmonoidClass.coe_pow, ← pow_succ',
      Nat.sub_add_cancel (Fact.out : p.Prime).one_le] using
      (IsLocalization.mk'_cancel (S := S) a s (s ^ (p - 1))).symm
  rw [hrep a s, hrep b t]
  generalize a * (s : R) ^ (p - 1) = c, b * (t : R) ^ (p - 1) = d
  rw [← IsLocalization.mk'_add, ← mul_pow, fractionMap_mk'_pow,
    fractionMap_mk'_pow, fractionMap_mk'_pow, ← IsLocalization.mk'_add]
  congr 1
  simp only [map_add, SubmonoidClass.coe_pow, mul_comm c, mul_comm d, σ.map_pow_mul]
  simp only [mul_comm]

private theorem fractionMap_pow_mul (x y : S) :
    σ.fractionMap M S (x ^ p * y) = x * σ.fractionMap M S y := by
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  obtain ⟨b, t, rfl⟩ := IsLocalization.exists_mk'_eq M y
  have ht : IsLocalization.mk' S b t =
      IsLocalization.mk' S (b * (t : R) ^ (p - 1)) (t ^ p) := by
    simpa only [SubmonoidClass.coe_pow, ← pow_succ',
      Nat.sub_add_cancel (Fact.out : p.Prime).one_le] using
      (IsLocalization.mk'_cancel (S := S) b t (t ^ (p - 1))).symm
  rw [ht]
  generalize b * (t : R) ^ (p - 1) = c
  rw [← IsLocalization.mk'_pow, ← IsLocalization.mk'_mul, ← mul_pow,
    fractionMap_mk'_pow, fractionMap_mk'_pow, σ.map_pow_mul, IsLocalization.mk'_mul]

/-- Extend a Frobenius splitting to a localization. The extension is uniquely determined
by agreement on the original ring and twisted linearity. -/
noncomputable def localization : FrobeniusSplitting S p where
  char_eq_zero := by rw [← map_natCast (algebraMap R S), σ.char_eq_zero, map_zero]
  toAddMonoidHom :=
    { toFun := σ.fractionMap M S
      map_zero' := by
        simpa using σ.fractionMap_mk'_pow M S 0 1
      map_add' := σ.fractionMap_add M S }
  map_pow_mul' := σ.fractionMap_pow_mul M S
  map_one' := by
    have h : σ.fractionMap M S 1 = 1 := by
      simpa only [one_pow, IsLocalization.mk'_one, map_one] using
        σ.fractionMap_mk'_pow M S 1 1
    exact h

/-- The localized splitting removes a p-th power from a denominator. -/
@[simp]
theorem localization_mk'_pow (a : R) (s : M) :
    σ.localization M S (IsLocalization.mk' S a (s ^ p)) =
      IsLocalization.mk' S (σ a) s :=
  σ.fractionMap_mk'_pow M S a s

/-- Localization of a splitting agrees with it on the original ring. -/
@[simp]
theorem localization_algebraMap (a : R) :
    σ.localization M S (algebraMap R S a) = algebraMap R S (σ a) := by
  simpa only [one_pow, IsLocalization.mk'_one] using σ.localization_mk'_pow M S a 1

/-- The denominator formula on an ordinary fraction; denominators may be zero divisors. -/
theorem localization_mk' (a : R) (s : M) :
    σ.localization M S (IsLocalization.mk' S a s) =
      IsLocalization.mk' S (σ (a * (s : R) ^ (p - 1))) s := by
  have h : IsLocalization.mk' S a s =
      IsLocalization.mk' S (a * (s : R) ^ (p - 1)) (s ^ p) := by
    simpa only [SubmonoidClass.coe_pow, ← pow_succ',
      Nat.sub_add_cancel (Fact.out : p.Prime).one_le] using
      (IsLocalization.mk'_cancel (S := S) a s (s ^ (p - 1))).symm
  rw [h, localization_mk'_pow]

/-- A splitting on a localization is uniquely determined by its values on the base ring. -/
theorem localization_unique (τ : FrobeniusSplitting S p)
    (hτ : ∀ a, τ (algebraMap R S a) = algebraMap R S (σ a)) :
    τ = σ.localization M S := by
  ext x
  obtain ⟨a, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  apply (IsLocalization.map_units S s).mul_right_inj.mp
  rw [← τ.map_pow_mul, ← (σ.localization M S).map_pow_mul]
  have he : algebraMap R S (s : R) ^ p * IsLocalization.mk' S a s =
      algebraMap R S (a * (s : R) ^ (p - 1)) := by
    conv_lhs => rw [← Nat.sub_add_cancel (Fact.out : p.Prime).one_le, pow_succ,
      mul_assoc, IsLocalization.mk'_spec']
    rw [map_mul, map_pow, mul_comm]
  rw [he, hτ, localization_algebraMap]

/-- Localizing in two stages agrees with direct localization whenever both presentations
of the final ring are given. This is the restriction law for repeated affine overlaps. -/
theorem localization_localization (N : Submonoid S) (L : Submonoid R)
    (T : Type*) [CommRing T] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [IsLocalization N T] [IsLocalization L T] :
    (σ.localization M S).localization N T = σ.localization L T := by
  apply σ.localization_unique L T
  intro a
  rw [IsScalarTower.algebraMap_apply R S T, localization_algebraMap,
    localization_algebraMap, ← IsScalarTower.algebraMap_apply R S T]

/-- Extension of a compatible ideal is compatible with the localized splitting. -/
theorem IsCompatible.map_localization {I : Ideal R} (hI : σ.IsCompatible I) :
    (σ.localization M S).IsCompatible (I.map (algebraMap R S)) := by
  rw [isCompatible_iff]
  intro x hx
  obtain ⟨⟨a, s⟩, hx⟩ := (IsLocalization.mem_map_algebraMap_iff M S).mp hx
  rw [(IsLocalization.eq_mk'_iff_mul_eq.mpr hx), localization_mk']
  apply IsLocalization.mk'_mem_iff.mpr
  exact Ideal.mem_map_of_mem _ ((σ.isCompatible_iff I).mp hI _
    (I.mul_mem_right _ a.prop))

/-- Compatibility of an ideal in a localization can be tested on its contraction. -/
theorem localization_isCompatible_iff (J : Ideal S) :
    (σ.localization M S).IsCompatible J ↔ σ.IsCompatible (J.comap (algebraMap R S)) := by
  constructor
  · intro h
    rw [isCompatible_iff] at h ⊢
    intro a ha
    simpa only [Ideal.mem_comap, localization_algebraMap] using h _ ha
  · intro h
    have he : (J.comap (algebraMap R S)).map (algebraMap R S) = J :=
      IsLocalization.map_under M S J
    rw [← he]
    exact IsCompatible.map_localization σ M S h

end TauCeti.FrobeniusSplitting
