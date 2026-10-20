/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.Order.Group.Basic

/-!
# Integer multiples of a positive element of an ordered group

In a linearly ordered additive commutative group, the integer multiples of a positive element `d`
form a discrete copy of `ℤ`: a nonnegative multiple is a natural-number multiple, and a positive
multiple is at least `d`. These facts turn a bound on a quantity taking values in
`AddSubgroup.zmultiples d` into a bound on a natural number, so a strictly increasing sequence of
such values below a fixed bound is finite, with no Archimedean hypothesis on the group.

## Main results

* `TauCeti.exists_nsmul_eq_of_mem_zmultiples`: a nonnegative integer multiple of `d > 0` is a
  natural-number multiple of `d`.
* `TauCeti.le_of_mem_zmultiples`: a positive integer multiple of `d > 0` is at least `d`.
-/

public section

namespace TauCeti

variable {K : Type*} [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K] {d x : K}

/-- A nonnegative integer multiple of a positive element `d` is a natural-number multiple of `d`. -/
theorem exists_nsmul_eq_of_mem_zmultiples (hd : 0 < d) (hx : x ∈ AddSubgroup.zmultiples d)
    (h : 0 ≤ x) : ∃ n : ℕ, n • d = x := by
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  have hn : 0 ≤ n := by
    rwa [← zero_zsmul d, zsmul_le_zsmul_iff_left hd] at h
  lift n to ℕ using hn
  exact ⟨n, (natCast_zsmul d n).symm⟩

/-- A positive integer multiple of a positive element `d` is at least `d`. -/
theorem le_of_mem_zmultiples (hd : 0 < d) (hx : x ∈ AddSubgroup.zmultiples d) (h : 0 < x) :
    d ≤ x := by
  obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
  rw [← zero_zsmul d, zsmul_lt_zsmul_iff_left hd] at h
  calc d = (1 : ℤ) • d := (one_zsmul d).symm
    _ ≤ n • d := zsmul_le_zsmul_left hd.le (by omega)

end TauCeti
