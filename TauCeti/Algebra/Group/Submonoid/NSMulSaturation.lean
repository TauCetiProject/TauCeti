/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Saturated

/-!
# Saturation of a submonoid by positive powers

Given a submonoid `s` of a commutative monoid `M`, its *saturation* is the submonoid of all
elements whose positive power lies in `s`, that is `{x : M | ∃ n, 0 < n ∧ x ^ n ∈ s}`. This is the
least `PowSaturated` submonoid containing `s` (a submonoid `t` is `PowSaturated` when `x ^ n ∈ t`
forces `n = 0` or `x ∈ t`). Applying saturation to an already `PowSaturated` submonoid is a no-op.

All declarations are stated multiplicatively and translated with `@[to_additive]` to their
additive counterparts, e.g. `Submonoid.powSaturation` becomes `AddSubmonoid.nsmulSaturation` and
`Submonoid.mem_powSaturation` becomes `AddSubmonoid.mem_nsmulSaturation`.

## Main results

* `Submonoid.powSaturation`: the elements of `M` having a positive power in `s`.
* `Submonoid.mem_powSaturation`: the membership criterion.
* `Submonoid.le_powSaturation`: `s` is contained in its saturation.
* `Submonoid.powSaturation_mono`: the saturation is monotone in `s`.
* `Submonoid.powSaturated_powSaturation`: the saturation is `PowSaturated`.
* `Submonoid.powSaturation_le_iff_le`: the saturation is the least `PowSaturated` submonoid
  containing `s`.
* `Submonoid.powSaturation_eq_self`: saturating an already `PowSaturated` submonoid is a no-op.
* `Submonoid.powSaturation_eq_self_iff`: a submonoid equals its saturation iff it is `PowSaturated`.
* `Submonoid.powSaturation_idem`: saturation is idempotent.
* `Submonoid.powSaturation_inf` and `Submonoid.powSaturation_comap`: saturation commutes with
  binary intersections and pullbacks along monoid homomorphisms.
* `Submonoid.powSaturated_comap_subtype_iff` and
  `Submonoid.powSaturated_comap_subgroup_subtype_iff`: saturation inside an ambient submonoid or
  subgroup containing `s` is characterized by `s.powSaturation ⊓ H = s`.
-/

public section

namespace Submonoid

section Monoid

variable {G H : Type*} [Monoid G] [Monoid H]

/-- The whole monoid is `PowSaturated`. -/
@[to_additive (attr := simp) /-- The whole additive monoid is `NSMulSaturated`. -/]
theorem powSaturated_top : (⊤ : Submonoid G).PowSaturated :=
  fun _ _ _ ↦ .inr trivial

/-- The intersection of two `PowSaturated` submonoids is `PowSaturated`. -/
@[to_additive /-- The intersection of two `NSMulSaturated` additive submonoids is
`NSMulSaturated`. -/]
theorem PowSaturated.inf {s t : Submonoid G} (hs : s.PowSaturated) (ht : t.PowSaturated) :
    (s ⊓ t).PowSaturated := by
  intro n g h
  rcases hs h.1 with rfl | hgs
  · exact .inl rfl
  · exact (ht h.2).imp_right fun hgt ↦ ⟨hgs, hgt⟩

/-- Pulling back a `PowSaturated` submonoid along a monoid homomorphism yields a `PowSaturated`
submonoid. -/
@[to_additive /-- Pulling back an `NSMulSaturated` additive submonoid along an additive monoid
homomorphism yields an `NSMulSaturated` additive submonoid. -/]
theorem PowSaturated.comap {t : Submonoid H} (ht : t.PowSaturated) (f : G →* H) :
    (t.comap f).PowSaturated :=
  fun _ _ hg ↦ ht (by simpa [map_pow] using hg)

end Monoid

variable {M N : Type*} [CommMonoid M] [CommMonoid N]

/-- The saturation of a submonoid `s` is the submonoid of elements whose positive power lies in
`s`, `{x | ∃ n, 0 < n ∧ x ^ n ∈ s}`. It is the least `PowSaturated` submonoid containing `s`. -/
@[to_additive /-- The saturation of an additive submonoid `s` is the additive
submonoid of elements whose positive multiple lies in `s`, `{x | ∃ n, 0 < n ∧ n • x ∈ s}`. It is
the least `NSMulSaturated` additive submonoid containing `s`. -/]
def powSaturation (s : Submonoid M) : Submonoid M where
  carrier := {x | ∃ n, 0 < n ∧ x ^ n ∈ s}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    intro x y hx hy
    obtain ⟨n, hnpos, hnx⟩ : ∃ n, 0 < n ∧ x ^ n ∈ s := hx
    obtain ⟨m, hmpos, hmy⟩ : ∃ m, 0 < m ∧ y ^ m ∈ s := hy
    have hkx : x ^ (n * m) ∈ s := by rw [Nat.mul_comm, pow_mul' x m n]; exact pow_mem hnx m
    have hky : y ^ (n * m) ∈ s := by rw [Nat.mul_comm, pow_mul y m n]; exact pow_mem hmy n
    exact ⟨n * m, Nat.mul_pos hnpos hmpos, by simpa [mul_pow] using mul_mem hkx hky⟩

/-- An element belongs to the saturation of `s` if and only if some positive power of it lies in
`s`. -/
@[to_additive (attr := simp) /-- An element belongs to the saturation of an additive submonoid `s`
if and only if some positive multiple of it lies in `s`. -/]
theorem mem_powSaturation {s : Submonoid M} {x : M} :
    x ∈ s.powSaturation ↔ ∃ n, 0 < n ∧ x ^ n ∈ s :=
  Iff.rfl

/-- Every submonoid is contained in its saturation. -/
@[to_additive (attr := simp) /-- Every additive submonoid is contained in its saturation. -/]
theorem le_powSaturation {s : Submonoid M} : s ≤ s.powSaturation :=
  fun _ hx => mem_powSaturation.2 ⟨1, by simpa [pow_one] using hx⟩

/-- The saturation is monotone in the submonoid. -/
@[to_additive (attr := gcongr) /-- The saturation is monotone in the additive submonoid. -/]
theorem powSaturation_mono {s t : Submonoid M} (hst : s ≤ t) :
    s.powSaturation ≤ t.powSaturation := by
  rintro x hx
  obtain ⟨n, hnpos, hnx⟩ : ∃ n, 0 < n ∧ x ^ n ∈ s := mem_powSaturation.mp hx
  exact mem_powSaturation.2 ⟨n, hnpos, hst hnx⟩

/-- The saturation of a submonoid is itself `PowSaturated`. -/
@[to_additive (attr := simp) /-- The saturation of an additive submonoid is itself
`NSMulSaturated`. -/]
theorem powSaturated_powSaturation {s : Submonoid M} : PowSaturated s.powSaturation := by
  intro n g hng
  obtain ⟨k, hkpos, hkg⟩ : ∃ k, 0 < k ∧ (g ^ n) ^ k ∈ s := mem_powSaturation.mp hng
  by_cases hn0 : n = 0
  · left; exact hn0
  · right
    exact mem_powSaturation.2 ⟨k * n, Nat.mul_pos hkpos (Nat.pos_of_ne_zero hn0),
      by rw [pow_mul' g k n]; exact hkg⟩

/-- The saturation of `s` is contained in the `PowSaturated` submonoid `t` if and only if `s` is:
the saturation is the least `PowSaturated` submonoid containing `s`. -/
@[to_additive /-- The saturation of `s` is contained in the `NSMulSaturated` additive submonoid `t`
if and only if `s` is: the saturation is the least `NSMulSaturated` additive submonoid containing
`s`. -/]
theorem powSaturation_le_iff_le {s t : Submonoid M} (ht : PowSaturated t) :
    s.powSaturation ≤ t ↔ s ≤ t :=
  ⟨fun h => le_trans le_powSaturation h,
   fun h => by
     rintro x hx
     obtain ⟨n, hnpos, hnx⟩ : ∃ n, 0 < n ∧ x ^ n ∈ s := mem_powSaturation.mp hx
     exact Or.resolve_left (ht (h hnx)) (Nat.pos_iff_ne_zero.mp hnpos)⟩

/-- The saturation of an already `PowSaturated` submonoid `s` is `s` itself. -/
@[to_additive (attr := simp) /-- The saturation of an already `NSMulSaturated` additive submonoid
`s` is `s` itself. -/]
theorem powSaturation_eq_self {s : Submonoid M} (hs : PowSaturated s) : s.powSaturation = s := by
  apply le_antisymm
  · exact (powSaturation_le_iff_le (s := s) (t := s) hs).mpr (le_refl s)
  · exact le_powSaturation

/-- A submonoid equals its saturation if and only if it is `PowSaturated`. -/
@[to_additive /-- An additive submonoid equals its saturation if and only if it is
`NSMulSaturated`. -/]
theorem powSaturation_eq_self_iff {s : Submonoid M} : s.powSaturation = s ↔ s.PowSaturated :=
  ⟨fun h ↦ h ▸ powSaturated_powSaturation, powSaturation_eq_self⟩

/-- Saturating a submonoid twice is the same as saturating it once. -/
@[to_additive /-- Saturating an additive submonoid twice is the same as saturating it once. -/]
theorem powSaturation_idem (s : Submonoid M) : s.powSaturation.powSaturation = s.powSaturation :=
  powSaturation_eq_self powSaturated_powSaturation

/-- Saturation commutes with binary intersection of submonoids. -/
@[to_additive (attr := simp) /-- Saturation commutes with binary intersection of additive
submonoids. -/]
theorem powSaturation_inf (s t : Submonoid M) :
    (s ⊓ t).powSaturation = s.powSaturation ⊓ t.powSaturation := by
  refine le_antisymm (le_inf (powSaturation_mono inf_le_left) (powSaturation_mono inf_le_right)) ?_
  rintro x ⟨hx, hy⟩
  obtain ⟨n, hn, hnx⟩ := mem_powSaturation.mp hx
  obtain ⟨m, hm, hmx⟩ := mem_powSaturation.mp hy
  refine mem_powSaturation.mpr ⟨n * m, Nat.mul_pos hn hm, ?_, ?_⟩
  · rw [pow_mul]
    exact pow_mem hnx m
  · rw [Nat.mul_comm, pow_mul]
    exact pow_mem hmx n

/-- Saturation commutes with pullback along a monoid homomorphism. -/
@[to_additive (attr := simp) /-- Saturation commutes with pullback along an additive monoid
homomorphism. -/]
theorem powSaturation_comap (t : Submonoid N) (f : M →* N) :
    (t.comap f).powSaturation = t.powSaturation.comap f := by
  ext x
  simp [mem_powSaturation, map_pow]

/-- The pullback of `t` along `f` is `PowSaturated` if and only if it agrees with the pullback of
the saturation of `t`. -/
@[to_additive /-- The pullback of `t` along `f` is `NSMulSaturated` if and only if it agrees with
the pullback of the saturation of `t`. -/]
theorem powSaturated_comap_iff {t : Submonoid N} {f : M →* N} :
    (t.comap f).PowSaturated ↔ t.powSaturation.comap f = t.comap f := by
  rw [← powSaturation_eq_self_iff, powSaturation_comap]

/-- For a submonoid `s` contained in an ambient submonoid `H`, the pullback of `s` to `H` is
`PowSaturated` if and only if the saturation of `s` meets `H` in `s`. -/
@[to_additive /-- For an additive submonoid `s` contained in an ambient additive submonoid `H`,
the pullback of `s` to `H` is `NSMulSaturated` if and only if the saturation of `s` meets `H` in
`s`. -/]
theorem powSaturated_comap_subtype_iff {s H : Submonoid M} (hs : s ≤ H) :
    (s.comap H.subtype).PowSaturated ↔ s.powSaturation ⊓ H = s := by
  rw [powSaturated_comap_iff]
  refine ⟨fun h ↦ le_antisymm (fun x hx ↦ ?_) (le_inf le_powSaturation hs), fun h ↦ ?_⟩
  · have hx' : (⟨x, hx.2⟩ : H) ∈ s.powSaturation.comap H.subtype := hx.1
    rwa [h] at hx'
  · ext ⟨x, hx⟩
    simp only [mem_comap, coe_subtype]
    exact ⟨fun hsat ↦ h ▸ ⟨hsat, hx⟩, fun hmem ↦ le_powSaturation hmem⟩

/-- For a submonoid `s` contained in a subgroup `H` of a commutative group, the pullback of `s` to
`H` is `PowSaturated` if and only if the saturation of `s` meets `H` in `s`. -/
@[to_additive /-- For an additive submonoid `s` contained in an additive subgroup `H` of an abelian
group, the pullback of `s` to `H` is `NSMulSaturated` if and only if the saturation of `s` meets
`H` in `s`. -/]
theorem powSaturated_comap_subgroup_subtype_iff {G : Type*} [CommGroup G] {s : Submonoid G}
    {H : Subgroup G} (hs : s ≤ H.toSubmonoid) :
    (s.comap H.subtype).PowSaturated ↔ s.powSaturation ⊓ H.toSubmonoid = s :=
  powSaturated_comap_subtype_iff hs

end Submonoid
