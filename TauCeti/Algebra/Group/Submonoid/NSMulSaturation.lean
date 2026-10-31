/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Subgroup.Saturated

/-!
# Saturation of an additive submonoid by positive multiples

Given an additive submonoid `s` of a commutative additive monoid `M`, its *saturation* is the
additive submonoid of all elements whose positive multiple lies in `s`, that is
`{x : M | ∃ n, 0 < n ∧ n • x ∈ s}`. This is the least additive submonoid containing `s` that is
`NSMulSaturated` (an additive submonoid `t` is `NSMulSaturated` when `n • x ∈ t` forces
`n = 0` or `x ∈ t`). Applying saturation to an already `NSMulSaturated` submonoid is a no-op.

## Main results

* `AddSubmonoid.nsmulSaturation`: the elements of `M` having a positive multiple in `s`.
* `AddSubmonoid.mem_nsmulSaturation_iff`: the membership criterion.
* `AddSubmonoid.le_nsmulSaturation`: `s` is contained in its saturation.
* `AddSubmonoid.nsmulSaturation_mono`: the saturation is monotone in `s`.
* `AddSubmonoid.nsmulSaturation_NSMulSaturated`: the saturation is `NSMulSaturated`.
* `AddSubmonoid.nsmulSaturation_le_iff_le`: the saturation is the least `NSMulSaturated` additive
  submonoid containing `s`.
* `AddSubmonoid.nsmulSaturation_eq_self`: saturating an already `NSMulSaturated` submonoid is a
  no-op.
-/

public section

namespace AddSubmonoid

variable {M : Type*} [AddCommMonoid M]

/-- The saturation of an additive submonoid `s` is the additive submonoid of elements whose positive
multiple lies in `s`, `{x | ∃ n, 0 < n ∧ n • x ∈ s}`. It is the least `NSMulSaturated` additive
submonoid containing `s`. -/
def nsmulSaturation (s : AddSubmonoid M) : AddSubmonoid M where
  carrier := {x | ∃ n, 0 < n ∧ n • x ∈ s}
  zero_mem' := ⟨1, by simp⟩
  add_mem' := by
    intro x y hx hy
    obtain ⟨n, hnpos, hnx⟩ : ∃ n, 0 < n ∧ n • x ∈ s := hx
    obtain ⟨m, hmpos, hmy⟩ : ∃ m, 0 < m ∧ m • y ∈ s := hy
    have hkx : (n * m) • x ∈ s := by rw [Nat.mul_comm, mul_nsmul' x m n]; exact nsmul_mem hnx m
    have hky : (n * m) • y ∈ s := by rw [Nat.mul_comm, mul_nsmul y m n]; exact nsmul_mem hmy n
    exact ⟨n * m, Nat.mul_pos hnpos hmpos, by simpa [nsmul_add] using add_mem hkx hky⟩

/-- An element belongs to the saturation of `s` if and only if some positive multiple of it lies in
`s`. -/
theorem mem_nsmulSaturation_iff {s : AddSubmonoid M} {x : M} :
    x ∈ s.nsmulSaturation ↔ ∃ n, 0 < n ∧ n • x ∈ s :=
  Iff.rfl

/-- Every additive submonoid is contained in its saturation. -/
@[simp]
theorem le_nsmulSaturation {s : AddSubmonoid M} : s ≤ s.nsmulSaturation :=
  fun _ hx => mem_nsmulSaturation_iff.2 ⟨1, by simpa [one_nsmul] using hx⟩

/-- The saturation is monotone in the additive submonoid. -/
@[gcongr]
theorem nsmulSaturation_mono {s t : AddSubmonoid M} (hst : s ≤ t) :
    s.nsmulSaturation ≤ t.nsmulSaturation := by
  rintro x hx
  obtain ⟨n, hnpos, hnx⟩ : ∃ n, 0 < n ∧ n • x ∈ s := mem_nsmulSaturation_iff.mp hx
  exact mem_nsmulSaturation_iff.2 ⟨n, hnpos, hst hnx⟩

/-- The saturation of an additive submonoid is itself `NSMulSaturated`. -/
@[simp]
theorem nsmulSaturation_NSMulSaturated {s : AddSubmonoid M} : NSMulSaturated s.nsmulSaturation := by
  intro n g hng
  obtain ⟨k, hkpos, hkg⟩ : ∃ k, 0 < k ∧ k • (n • g) ∈ s := mem_nsmulSaturation_iff.mp hng
  by_cases hn0 : n = 0
  · left; exact hn0
  · right
    exact mem_nsmulSaturation_iff.2 ⟨k * n, Nat.mul_pos hkpos (Nat.pos_of_ne_zero hn0),
      by rw [mul_nsmul' g k n]; exact hkg⟩

/-- The saturation of `s` is contained in the `NSMulSaturated` additive submonoid `t` if and only if
`s` is: the saturation is the least `NSMulSaturated` additive submonoid containing `s`. -/
theorem nsmulSaturation_le_iff_le {s t : AddSubmonoid M} (ht : NSMulSaturated t) :
    s.nsmulSaturation ≤ t ↔ s ≤ t :=
  ⟨fun h => le_trans le_nsmulSaturation h,
   fun h => by
     rintro x hx
     obtain ⟨n, hnpos, hnx⟩ : ∃ n, 0 < n ∧ n • x ∈ s := mem_nsmulSaturation_iff.mp hx
     exact Or.resolve_left (ht (h hnx)) (Nat.pos_iff_ne_zero.mp hnpos)⟩

/-- The saturation of an already `NSMulSaturated` additive submonoid `s` is `s` itself. -/
@[simp]
theorem nsmulSaturation_eq_self {s : AddSubmonoid M} (hs : NSMulSaturated s) :
    s.nsmulSaturation = s := by
  apply le_antisymm
  · exact (nsmulSaturation_le_iff_le (s := s) (t := s) hs).mpr (le_refl s)
  · exact le_nsmulSaturation

end AddSubmonoid
