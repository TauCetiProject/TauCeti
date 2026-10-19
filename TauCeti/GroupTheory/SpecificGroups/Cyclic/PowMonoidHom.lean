/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# The `d`-th power criterion in a finite cyclic group

Let `G` be a finite cyclic commutative group of order `N` and let `d` be any natural number, not
assumed to divide `N`. Write `g = gcd(N, d)`. The `d`-th powers of `G` are exactly the elements
killed by the `(N / g)`-th power map, and they form the unique subgroup of order `N / g`. In
particular `a` is a `d`-th power exactly when `a ^ (N / g) = 1`. For `d = 0` the exponent is
`N / N = 1` and the criterion reads `a = 1`; for `d` dividing `N` it is the familiar
`a ^ (N / d) = 1`, which for the units modulo an odd prime and `d = 2` is Euler's criterion.

This is the group theory behind the `n`-th power residue criteria: applied to the cyclic unit group
of a finite field it decides which elements are `n`-th powers, and the kernel of the `d`-th power
map (of order `g`, Mathlib's `IsCyclic.card_powMonoidHom_ker`) counts their roots.

## Main results

* `TauCeti.pow_pow_card_div_gcd_eq_one`: in any group of order `N`, `(x ^ d) ^ (N / gcd(N, d)) = 1`.
* `IsCyclic.range_powMonoidHom_eq_ker`: in a finite cyclic group the image of the `d`-th power
  map is the kernel of the `(N / gcd(N, d))`-th power map.
* `IsCyclic.range_powMonoidHom_gcd`: the `d`-th powers are the `gcd(N, d)`-th powers.
* `IsCyclic.mem_range_powMonoidHom_iff`: `a` is a `d`-th power iff `a ^ (N / gcd(N, d)) = 1`.
* `IsCyclic.eq_range_powMonoidHom_iff`: the `d`-th powers form the unique subgroup of order
  `N / gcd(N, d)`.

## References

* Victor Shoup, *A Computational Introduction to Number Theory and Algebra* (2nd ed.),
  Theorem 6.32 (iii) and (vi), and Example 7.61.
-/

public section

variable {G : Type*}

namespace TauCeti

/-- In a group of order `N`, every `d`-th power is killed by the `(N / gcd(N, d))`-th power map:
`(x ^ d) ^ (N / gcd(N, d)) = 1`. For an infinite group `N = 0` and the exponent is `0`. -/
theorem pow_pow_card_div_gcd_eq_one [Group G] (x : G) (d : ℕ) :
    (x ^ d) ^ (Nat.card G / (Nat.card G).gcd d) = 1 := by
  -- `d * (N / g) = N * (d / g)` with `g = gcd(N, d)` dividing both `N` and `d`.
  rw [← pow_mul, ← Nat.mul_div_assoc _ (Nat.gcd_dvd_left _ _), mul_comm d,
    Nat.mul_div_assoc _ (Nat.gcd_dvd_right _ _), pow_mul, pow_card_eq_one', one_pow]

end TauCeti

namespace IsCyclic

variable [CommGroup G] [IsCyclic G] [Finite G]

/-- **The `d`-th power criterion in a finite cyclic group**, as an equality of subgroups: the image
of the `d`-th power map of a finite cyclic group of order `N` is the kernel of the
`(N / gcd(N, d))`-th power map. -/
theorem range_powMonoidHom_eq_ker (d : ℕ) :
    (powMonoidHom d : G →* G).range =
      (powMonoidHom (Nat.card G / (Nat.card G).gcd d) : G →* G).ker := by
  -- The image lies in the kernel, and both have `N / gcd(N, d)` elements.
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact TauCeti.pow_pow_card_div_gcd_eq_one x d
  · rw [card_powMonoidHom_ker, card_powMonoidHom_range,
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))]

/-- In a finite cyclic group of order `N`, the `d`-th powers are exactly the `gcd(N, d)`-th
powers. -/
theorem range_powMonoidHom_gcd (d : ℕ) :
    (powMonoidHom ((Nat.card G).gcd d) : G →* G).range = (powMonoidHom d : G →* G).range := by
  rw [range_powMonoidHom_eq_ker, range_powMonoidHom_eq_ker, Nat.gcd_gcd_self_right_left]

/-- **The `d`-th power criterion in a finite cyclic group.** In a finite cyclic group of order
`N`, an element `x` is a `d`-th power exactly when `x ^ (N / gcd(N, d)) = 1`. The natural number
`d` is arbitrary: when `d ∣ N` the exponent is `N / d`, and when `d = 0` the criterion reads
`x = 1`. -/
theorem mem_range_powMonoidHom_iff (d : ℕ) (x : G) :
    x ∈ (powMonoidHom d : G →* G).range ↔ x ^ (Nat.card G / (Nat.card G).gcd d) = 1 := by
  rw [range_powMonoidHom_eq_ker, MonoidHom.mem_ker, powMonoidHom_apply]

/-- In a finite cyclic group of order `N`, the `d`-th powers form the unique subgroup of order
`N / gcd(N, d)`. -/
theorem eq_range_powMonoidHom_iff (H : Subgroup G) (d : ℕ) :
    H = (powMonoidHom d : G →* G).range ↔ Nat.card H = Nat.card G / (Nat.card G).gcd d := by
  rw [subgroup_eq_iff_card_eq, card_powMonoidHom_range]

end IsCyclic

/-! ### Examples -/

section Examples

/-- The exponent is `N / gcd(N, d)`: in a cyclic group of order `12`, the cubes are the elements
with `x ^ 4 = 1`. -/
example {G : Type*} [CommGroup G] [IsCyclic G] [Finite G] (hG : Nat.card G = 12) (x : G) :
    x ∈ (powMonoidHom 3 : G →* G).range ↔ x ^ 4 = 1 := by
  rw [IsCyclic.mem_range_powMonoidHom_iff, hG]
  rfl

/-- In a cyclic group of order `12`, every element is a fifth power, since `gcd(12, 5) = 1`. -/
example {G : Type*} [CommGroup G] [IsCyclic G] [Finite G] (hG : Nat.card G = 12) :
    (powMonoidHom 5 : G →* G).range = ⊤ := by
  refine ((IsCyclic.eq_range_powMonoidHom_iff ⊤ 5).2 ?_).symm
  rw [Subgroup.card_top, hG]
  rfl

/-- For `d = 0` the criterion reads `x = 1`: the only `0`-th power is `1`. -/
example {G : Type*} [CommGroup G] [IsCyclic G] [Finite G] (x : G) :
    x ∈ (powMonoidHom 0 : G →* G).range ↔ x = 1 := by
  rw [IsCyclic.mem_range_powMonoidHom_iff, Nat.gcd_zero_right, Nat.div_self Nat.card_pos,
    pow_one]

/-- In a cyclic group of even order `N` the squares are the elements with `x ^ (N / 2) = 1`; for
the units modulo an odd prime this is Euler's criterion `ZMod.euler_criterion_units`. -/
example {G : Type*} [CommGroup G] [IsCyclic G] [Finite G] (hG : Even (Nat.card G)) (x : G) :
    x ∈ (powMonoidHom 2 : G →* G).range ↔ x ^ (Nat.card G / 2) = 1 := by
  rw [IsCyclic.mem_range_powMonoidHom_iff, Nat.gcd_eq_right (even_iff_two_dvd.1 hG)]

end Examples
