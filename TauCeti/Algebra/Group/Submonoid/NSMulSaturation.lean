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
* `Submonoid.powSaturation_eq_self` and `Submonoid.powSaturation_eq_self_iff`: saturating an
  already `PowSaturated` submonoid is a no-op, and this characterizes `PowSaturated` submonoids.
* `Submonoid.powSaturation_idem`: saturation is idempotent.
* `Submonoid.PowSaturated.comap` and `Submonoid.PowSaturated.inf`: preimages and intersections of
  `PowSaturated` submonoids are `PowSaturated`.
* `Submonoid.powSaturation_comap`: saturation commutes with preimage along a monoid homomorphism.
* `Submonoid.powSaturated_comap_subtype_iff`: for `s ≤ t`, the pullback of `s` to `t` is
  `PowSaturated` iff `s.powSaturation ⊓ t = s`.
-/

public section

namespace Submonoid

section Monoid

variable {M N : Type*} [Monoid M] [Monoid N]

/-- The preimage of a `PowSaturated` submonoid under a monoid homomorphism is `PowSaturated`. -/
@[to_additive /-- The preimage of an `NSMulSaturated` additive submonoid under an additive monoid
homomorphism is `NSMulSaturated`. -/]
theorem PowSaturated.comap {t : Submonoid N} (ht : t.PowSaturated) (f : M →* N) :
    (t.comap f).PowSaturated :=
  fun _ _ h ↦ ht (by simpa using h)

/-- The intersection of two `PowSaturated` submonoids is `PowSaturated`. -/
@[to_additive /-- The intersection of two `NSMulSaturated` additive submonoids is
`NSMulSaturated`. -/]
theorem PowSaturated.inf {s t : Submonoid M} (hs : s.PowSaturated) (ht : t.PowSaturated) :
    (s ⊓ t).PowSaturated := fun n _ h ↦ by
  rcases eq_or_ne n 0 with rfl | hn
  · exact .inl rfl
  · exact .inr ⟨(hs h.1).resolve_left hn, (ht h.2).resolve_left hn⟩

end Monoid

variable {M : Type*} [CommMonoid M]

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

/-- Taking the saturation twice is taking it once. -/
@[to_additive /-- Taking the saturation twice is taking it once. -/]
theorem powSaturation_idem (s : Submonoid M) :
    s.powSaturation.powSaturation = s.powSaturation :=
  powSaturation_eq_self powSaturated_powSaturation

/-- Saturation commutes with preimage under any monoid homomorphism. -/
@[to_additive /-- Saturation commutes with preimage under any additive monoid homomorphism. -/]
theorem powSaturation_comap {N : Type*} [CommMonoid N] (s : Submonoid M) (f : N →* M) :
    (s.comap f).powSaturation = s.powSaturation.comap f := by
  ext x
  simp

/-- For submonoids `s ≤ t`, the pullback of `s` to `t` is `PowSaturated` in `t` if and only if
the saturation of `s` in `M` meets `t` in `s`. -/
@[to_additive /-- For additive submonoids `s ≤ t`, the pullback of `s` to `t` is `NSMulSaturated`
in `t` if and only if the saturation of `s` in `M` meets `t` in `s`. -/]
theorem powSaturated_comap_subtype_iff {s t : Submonoid M} (hst : s ≤ t) :
    (s.comap t.subtype).PowSaturated ↔ s.powSaturation ⊓ t = s := by
  refine ⟨fun h ↦ le_antisymm (fun x hx ↦ ?_) (le_inf le_powSaturation hst),
    fun h n x hnx ↦ or_iff_not_imp_left.mpr fun hn ↦ ?_⟩
  · obtain ⟨n, hn, hnx⟩ := mem_powSaturation.mp hx.1
    exact (h (g := ⟨x, hx.2⟩) (by simpa using hnx)).resolve_left hn.ne'
  · exact h.le ⟨mem_powSaturation.mpr ⟨n, Nat.pos_of_ne_zero hn, by simpa using hnx⟩, x.2⟩

end Submonoid
