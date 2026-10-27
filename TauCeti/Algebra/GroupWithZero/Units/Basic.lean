/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Set.Finite.Basic
-- `Nat.card` occurs in the statement about a group with zero with two elements below.
public import Mathlib.SetTheory.Cardinal.Finite
-- Non-public: `Nat.card_units` counts the units of a group with zero, in one proof only.
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Units and powers in groups with zero

Elementary facts about a group with zero `G₀` and its units, and local ring homomorphisms.

A product `a ^ i * a⁻¹ ^ (n - i)`, in which the two exponents are natural numbers adding up to
`n`, is the integer power `a ^ (2 * i - n)`.  Such a product is what a diagonal matrix
`diag(a, a⁻¹)` contributes to a monomial of degree `n`, so the identity is the exponent
bookkeeping behind a weight computation.

Mathlib splits an integer power as a quotient (`zpow_sub₀`, `zpow_natCast_sub_natCast₀`) and
subtracts natural-number exponents (`pow_sub₀`, `inv_pow_sub₀`); this is the corresponding
statement for the exponents `i` and `n - i` of `a` and `a⁻¹`.

A group with zero with two elements has a trivial unit group: by `Nat.card_units` the units are
one fewer than the elements, so there is exactly one of them.  This is why a field with two
elements has no pair of distinct units, hence none of the invariants indexed by such a pair.

A local ring homomorphism reflects units, and it carries the natural number `n` to `n`; so `n` is
invertible in the source as soon as it is invertible in the target. For an algebra map of fields
`K → L` this is how invertibility of `n` travels from `L` down to `K`.

Finally, the units of an infinite group with zero are infinite: deleting zero leaves infinitely
many elements, each of which defines a unit. In particular, its unit group is nontrivial.

Mathlib's `div_mul_div_cancel₀` cancels `b` in `a / b * (b / c) = a / c` for `b ≠ 0`. The identity
also holds when `b = 0` as long as `a = 0` then, as for the elapsed time `max 0 (min t d)` of a time
interval of length `d`; this is the companion of Mathlib's `div_mul_cancel_of_imp`.

## Main results

* `TauCeti.pow_mul_inv_pow_eq_zpow₀`: `a ^ i * a⁻¹ ^ (n - i) = a ^ (2 * i - n)` for `i ≤ n`.
* `TauCeti.subsingleton_units_of_natCard_eq_two`: a group with zero with two elements has a
  trivial unit group.
* `TauCeti.isUnit_natCast_of_isUnit_natCast`: a natural number invertible in the target of a
  local ring homomorphism is invertible in its source.
* `TauCeti.instInfiniteUnitsOfInfiniteGroupWithZero`: the units of an infinite group with zero
  are infinite.
* `TauCeti.div_mul_div_cancel_of_imp`: `a / b * (b / c) = a / c` when `b = 0` forces `a = 0`.
-/

public section

namespace TauCeti

/-- The units of an infinite group with zero form an infinite group. -/
instance instInfiniteUnitsOfInfiniteGroupWithZero {G₀ : Type*} [GroupWithZero G₀] [Infinite G₀] :
    Infinite G₀ˣ := by
  have : Infinite {x : G₀ // x ≠ 0} :=
    (Set.finite_singleton (0 : G₀)).infinite_compl.to_subtype
  exact unitsEquivNeZero.infinite_iff.mpr this

/-- **A power of `a` times a power of `a⁻¹` is an integer power of `a`**: for `i ≤ n`, the
exponents `i` and `n - i` combine to `i - (n - i) = 2 * i - n`. -/
theorem pow_mul_inv_pow_eq_zpow₀ {G₀ : Type*} [GroupWithZero G₀] {a : G₀} (ha : a ≠ 0) {i n : ℕ}
    (hi : i ≤ n) : a ^ i * a⁻¹ ^ (n - i) = a ^ (2 * (i : ℤ) - n) := by
  -- the exponent `2 * i - n` is the exponent of `a` minus the exponent of `a⁻¹`
  have hexp : 2 * (i : ℤ) - n = (i : ℤ) - ((n - i : ℕ) : ℤ) := by omega
  rw [hexp, zpow_sub₀ ha, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]

/-- **A group with zero with two elements has a trivial unit group.** Its units are one fewer than
its elements, by `Nat.card_units`, so there is exactly one of them. -/
theorem subsingleton_units_of_natCard_eq_two {G₀ : Type*} [GroupWithZero G₀]
    (h : Nat.card G₀ = 2) : Subsingleton G₀ˣ :=
  (Nat.card_eq_one_iff_unique.1 (by rw [Nat.card_units G₀, h])).1

/-- **A natural number invertible after a local ring homomorphism was already invertible**: `f`
carries `n` to `n`, and a local homomorphism reflects units. -/
theorem isUnit_natCast_of_isUnit_natCast {R S F : Type*} [Semiring R] [Semiring S] [FunLike F R S]
    [RingHomClass F R S] (f : F) [IsLocalHom f] {n : ℕ} (hn : IsUnit (n : S)) : IsUnit (n : R) :=
  IsUnit.of_map f (n : R) (by rwa [map_natCast])

/-- `a / b * (b / c) = a / c`, also for `b = 0` provided `a = 0` then. This is the degenerate-case
companion of Mathlib's `div_mul_div_cancel₀`, as `div_mul_cancel_of_imp` is of `div_mul_cancel₀`. -/
theorem div_mul_div_cancel_of_imp {G₀ : Type*} [GroupWithZero G₀] {a b c : G₀}
    (h : b = 0 → a = 0) : a / b * (b / c) = a / c := by
  rw [← mul_div_assoc, div_mul_cancel_of_imp h]

end TauCeti
