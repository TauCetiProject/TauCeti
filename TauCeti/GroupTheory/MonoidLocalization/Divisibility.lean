/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.GroupTheory.MonoidLocalization.Divisibility

/-!
# Relative primality and squarefreeness in localizations of monoids

In a commutative decomposition monoid, both relatively prime elements
(`Submonoid.LocalizationMap.map_isRelPrime`) and squarefree elements
(`Submonoid.LocalizationMap.map_squarefree`) retain their property in every localization. No zero
element or cancellation hypothesis is needed.

Localizing a commutative semiring `R` also localizes the multiplicative monoid of its polynomial
ring `R[X]` (Mathlib's `Polynomial.isLocalization`), so whenever `R[X]` is a decomposition monoid
(for instance, when `R` is a GCD domain), these results transfer relative primality and
squarefreeness of polynomials from `R[X]` to `S[X]` for every localization `S` of `R`, such as the
fraction field (`IsRelPrime.map_localization_map`, `Squarefree.map_localization_map`).

## Implementation notes

Both proofs rest on Mathlib's description of divisibility and units in a localization,
`Submonoid.LocalizationMap.map_dvd_map` and `Submonoid.LocalizationMap.map_isUnit_iff`, together
with `exists_dvd_and_dvd_of_dvd_mul` and `IsRelPrime.dvd_of_dvd_mul_left` /
`IsRelPrime.dvd_of_dvd_mul_right` in a decomposition monoid. For `map_squarefree`, avoiding
cancellation uses `IsRelPrime.of_squarefree_mul` to show that if `a * a ∣ m * x` with `x`
squarefree, then `a ∣ m * m` (rather than `a ∣ m`, which fails without cancellation).
-/

public section

namespace Submonoid.LocalizationMap

variable {M N : Type*} [CommMonoid M] {S : Submonoid M} [CommMonoid N] (f : LocalizationMap S N)

/-- In a commutative decomposition monoid, relatively prime elements stay relatively prime in every
localization. -/
theorem map_isRelPrime [DecompositionMonoid M] {x y : M} (h : IsRelPrime x y) :
    IsRelPrime (f x) (f y) := by
  intro d hx hy
  obtain ⟨⟨a, s⟩, hd⟩ := f.surj d
  have hs := f.map_units s
  refine isUnit_of_mul_isUnit_left (hd ▸ f.map_isUnit_iff.2 ?_)
  obtain ⟨m₁, hm₁, ha₁⟩ := f.map_dvd_map.1 (hd ▸ hs.mul_right_dvd.2 hx)
  obtain ⟨m₂, hm₂, ha₂⟩ := f.map_dvd_map.1 (hd ▸ hs.mul_right_dvd.2 hy)
  obtain ⟨a₁, a₂, h₁, h₂, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul ha₁
  exact ⟨m₁ * m₂, mul_mem hm₁ hm₂, mul_dvd_mul h₁
    ((h.of_dvd_left h₂).dvd_of_dvd_mul_right ((dvd_mul_left a₂ a₁).trans ha₂))⟩

/-- In a commutative decomposition monoid, squarefree elements stay squarefree in every
localization. -/
theorem map_squarefree [DecompositionMonoid M] {x : M} (hx : Squarefree x) :
    Squarefree (f x) := by
  intro d hd
  obtain ⟨⟨a, s⟩, hda⟩ := f.surj d
  have hs := f.map_units s
  refine isUnit_of_mul_isUnit_left (hda ▸ f.map_isUnit_iff.2 ?_)
  -- `f (a * a)` is `d * d` times the unit `f s * f s`, so it divides `f x` as `d * d` does.
  have ha : f (a * a) ∣ f x := by
    rwa [map_mul, ← hda, mul_mul_mul_comm, (hs.mul hs).mul_right_dvd]
  obtain ⟨m, hm, ham⟩ := f.map_dvd_map.1 ha
  -- Split `a = u * v` with `u ∣ m` and `v ∣ x`; we show `v ∣ m`, so `a ∣ m * m ∈ S`.
  obtain ⟨u, v, hu, hv, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul ((dvd_mul_left a a).trans ham)
  have hvx : v * v ∣ m * x := (mul_dvd_mul (dvd_mul_left v u) (dvd_mul_left v u)).trans ham
  obtain ⟨b, c, hb, hc, hbc⟩ := exists_dvd_and_dvd_of_dvd_mul hvx
  obtain ⟨b₁, b₂, hb₁, hb₂, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul ⟨c, hbc⟩
  obtain ⟨e, rfl⟩ := hb₁
  obtain ⟨p, q, hp, hq, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hb₂
  obtain ⟨r, rfl⟩ := hq
  -- In `v = (b₁ * q) * r`, the remainder `r` is relatively prime to `b = b₁ * (p * q)`,
  -- hence `r * r ∣ c ∣ x`, forcing `IsUnit r` and therefore `v ∣ b ∣ m`.
  have hrel : IsRelPrime (b₁ * q) r :=
    IsRelPrime.of_squarefree_mul (mul_assoc b₁ q r ▸ hx.squarefree_of_dvd hv)
  have hb₁r : IsRelPrime b₁ r := hrel.of_dvd_left (dvd_mul_right b₁ q)
  have hbr : IsRelPrime (b₁ * (p * q)) r :=
    hb₁r.mul_left ((hb₁r.of_dvd_left hp).mul_left (hrel.of_dvd_left (dvd_mul_left q b₁)))
  have hrv : r ∣ b₁ * (q * r) := by
    rw [← mul_assoc]
    exact dvd_mul_left r (b₁ * q)
  have hrc : r * r ∣ c :=
    (hbr.mul_right hbr).symm.dvd_of_dvd_mul_left (hbc ▸ mul_dvd_mul hrv hrv)
  have hur : IsUnit r := hx r (hrc.trans hc)
  have hvm : b₁ * (q * r) ∣ m := by
    rw [← mul_assoc, hur.mul_right_dvd]
    exact (mul_dvd_mul_left b₁ (dvd_mul_left q p)).trans hb
  exact ⟨m * m, mul_mem hm hm, mul_dvd_mul hu hvm⟩

end Submonoid.LocalizationMap
