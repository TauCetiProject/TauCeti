/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
import TauCeti.GroupTheory.OrderOfElement.Basic

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

The inclusion of the image in the kernel holds in any group of order `N`, indeed for any `x` with
`x ^ N = 1` in a monoid; it is `TauCeti.pow_pow_div_gcd_eq_one` in
`TauCeti.GroupTheory.OrderOfElement.Basic`. That the `d`-th powers are the `gcd(N, d)`-th powers
holds in any commutative group of order `N`, indeed of exponent dividing `N`; it is
`TauCeti.range_powMonoidHom_gcd` in `TauCeti.Algebra.Group.PowMonoidHom`.

## Main results

* `IsCyclic.range_powMonoidHom_eq_ker`: in a finite cyclic group the image of the `d`-th power
  map is the kernel of the `(N / gcd(N, d))`-th power map.
* `IsCyclic.mem_range_powMonoidHom_iff`: `a` is a `d`-th power iff `a ^ (N / gcd(N, d)) = 1`.

Each result has an additive version, stated for `nsmulAddMonoidHom` in an additive cyclic group
(`IsAddCyclic.range_nsmulAddMonoidHom_eq_ker`, `IsAddCyclic.mem_range_nsmulAddMonoidHom_iff`).

That the `d`-th powers form the unique subgroup of order `N / gcd(N, d)` is already Mathlib's
`IsCyclic.subgroup_eq_iff_card_eq` combined with `IsCyclic.card_powMonoidHom_range`; an example
below applies it.

## References

* Victor Shoup, *A Computational Introduction to Number Theory and Algebra* (2nd ed.),
  Theorem 6.32 (iii) and (vi), and Example 7.61.
-/

public section

variable {G : Type*}

namespace IsCyclic

variable [CommGroup G] [IsCyclic G] [Finite G]

/-- **The `d`-th power criterion in a finite cyclic group**, as an equality of subgroups: the image
of the `d`-th power map of a finite cyclic group of order `N` is the kernel of the
`(N / gcd(N, d))`-th power map. -/
@[to_additive
/-- **The `d`-th multiple criterion in a finite additive cyclic group**, as an equality of
subgroups: the image of multiplication by `d` on a finite additive cyclic group of order `N` is
the kernel of multiplication by `N / gcd(N, d)`. -/]
theorem range_powMonoidHom_eq_ker (d : ℕ) :
    (powMonoidHom d : G →* G).range =
      (powMonoidHom (Nat.card G / (Nat.card G).gcd d) : G →* G).ker := by
  -- The image lies in the kernel, and both have `N / gcd(N, d)` elements.
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact TauCeti.pow_pow_div_gcd_eq_one pow_card_eq_one' d
  · rw [card_powMonoidHom_ker, card_powMonoidHom_range,
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))]

/-- **The `d`-th power criterion in a finite cyclic group.** In a finite cyclic group of order
`N`, an element `x` is a `d`-th power exactly when `x ^ (N / gcd(N, d)) = 1`. The natural number
`d` is arbitrary: when `d ∣ N` the exponent is `N / d`, and when `d = 0` the criterion reads
`x = 1`. -/
@[to_additive
/-- **The `d`-th multiple criterion in a finite additive cyclic group.** In a finite additive
cyclic group of order `N`, an element `x` is a `d`-th multiple exactly when
`(N / gcd(N, d)) • x = 0`. -/]
theorem mem_range_powMonoidHom_iff (d : ℕ) (x : G) :
    x ∈ (powMonoidHom d : G →* G).range ↔ x ^ (Nat.card G / (Nat.card G).gcd d) = 1 := by
  rw [range_powMonoidHom_eq_ker, MonoidHom.mem_ker, powMonoidHom_apply]

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
  -- The `d`-th powers form the unique subgroup of order `N / gcd(N, d)`.
  rw [eq_comm, IsCyclic.subgroup_eq_iff_card_eq, IsCyclic.card_powMonoidHom_range,
    Subgroup.card_top, hG]
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
