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
-- Non-public: the `IsLocalHom` instance for a monoid-with-zero homomorphism out of a group with
-- zero is used only in the proof below.
import Mathlib.Algebra.GroupWithZero.Units.Lemmas
-- Non-public: `Nat.card_units` counts the units of a group with zero, in one proof only.
import Mathlib.Algebra.GroupWithZero.Units.Fintype

/-!
# Units and powers in groups with zero

Four elementary facts about a group with zero `G₀` and its units, and one about local ring
homomorphisms.

A product `a ^ i * a⁻¹ ^ (n - i)`, in which the two exponents are natural numbers adding up to
`n`, is the integer power `a ^ (2 * i - n)`.  Such a product is what a diagonal matrix
`diag(a, a⁻¹)` contributes to a monomial of degree `n`, so the identity is the exponent
bookkeeping behind a weight computation.

Mathlib splits an integer power as a quotient (`zpow_sub₀`, `zpow_natCast_sub_natCast₀`) and
subtracts natural-number exponents (`pow_sub₀`, `inv_pow_sub₀`); this is the corresponding
statement for the exponents `i` and `n - i` of `a` and `a⁻¹`.

A monoid-with-zero homomorphism out of `G₀` carries units to units, and that is the only way one
of its values can be a unit: such a homomorphism is local, so a preimage of a unit is itself a
unit of `G₀`.  Membership of a unit in the range is therefore the same as being `Units.map` of a
unit, which is what turns a hypothesis about `Set.range (algebraMap F E)` into one about `Fˣ`.

A group with zero with two elements has a trivial unit group: by `Nat.card_units` the units are
one fewer than the elements, so there is exactly one of them.  This is why a field with two
elements has no pair of distinct units, hence none of the invariants indexed by such a pair.

A local ring homomorphism reflects units, and it carries the natural number `n` to `n`; so `n` is
invertible in the source as soon as it is invertible in the target. For an algebra map of fields
`K → L` this is how invertibility of `n` travels from `L` down to `K`.

Finally, the units of an infinite group with zero are nontrivial: deleting zero leaves at least two
elements, both of which define units.

## Main results

* `TauCeti.pow_mul_inv_pow_eq_zpow₀`: `a ^ i * a⁻¹ ^ (n - i) = a ^ (2 * i - n)` for `i ≤ n`.
* `TauCeti.mem_range_iff_exists_units_map_eq`: a unit lies in the range of a monoid-with-zero
  homomorphism out of a group with zero exactly when it is `Units.map` of a unit.
* `TauCeti.subsingleton_units_of_natCard_eq_two`: a group with zero with two elements has a
  trivial unit group.
* `TauCeti.isUnit_natCast_of_isUnit_natCast`: a natural number invertible in the target of a
  local ring homomorphism is invertible in its source.
* `TauCeti.instNontrivialUnitsOfInfiniteGroupWithZero`: the units of an infinite group with zero
  are nontrivial.
-/

public section

namespace TauCeti

/-- The units of an infinite group with zero form a nontrivial group. -/
instance instNontrivialUnitsOfInfiniteGroupWithZero {G₀ : Type*} [GroupWithZero G₀] [Infinite G₀] :
    Nontrivial G₀ˣ := by
  let U := {x : G₀ // x ∈ ({0} : Set G₀)ᶜ}
  let _ : Infinite U := (Set.toFinite ({0} : Set G₀)).infinite_compl.to_subtype
  obtain ⟨x, y, hxy⟩ := exists_pair_ne U
  refine ⟨Units.mk0 x (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using x.property),
    Units.mk0 y (by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using y.property), ?_⟩
  intro h
  apply hxy
  apply Subtype.ext
  exact congrArg Units.val h

/-- **A power of `a` times a power of `a⁻¹` is an integer power of `a`**: for `i ≤ n`, the
exponents `i` and `n - i` combine to `i - (n - i) = 2 * i - n`. -/
theorem pow_mul_inv_pow_eq_zpow₀ {G₀ : Type*} [GroupWithZero G₀] {a : G₀} (ha : a ≠ 0) {i n : ℕ}
    (hi : i ≤ n) : a ^ i * a⁻¹ ^ (n - i) = a ^ (2 * (i : ℤ) - n) := by
  -- the exponent `2 * i - n` is the exponent of `a` minus the exponent of `a⁻¹`
  have hexp : 2 * (i : ℤ) - n = (i : ℤ) - ((n - i : ℕ) : ℤ) := by omega
  rw [hexp, zpow_sub₀ ha, zpow_natCast, zpow_natCast, inv_pow, div_eq_mul_inv]

/-- **A unit in the range of a monoid-with-zero homomorphism out of a group with zero comes from a
unit.** Such a homomorphism is local, so a preimage of a unit is a unit of `G₀`; conversely every
value of `Units.map f` lies in the range of `f`. -/
theorem mem_range_iff_exists_units_map_eq {G₀ M₀ F : Type*} [GroupWithZero G₀] [MonoidWithZero M₀]
    [Nontrivial M₀] [FunLike F G₀ M₀] [MonoidWithZeroHomClass F G₀ M₀] (f : F) (u : M₀ˣ) :
    (u : M₀) ∈ Set.range f ↔ ∃ a : G₀ˣ, Units.map (f : G₀ →* M₀) a = u := by
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨(IsUnit.of_map f a (ha ▸ u.isUnit)).unit, Units.ext (by simp [ha])⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

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

end TauCeti

namespace Units

/-- A nonnegative power of the product of two units gives consecutive monomial exponents
after multiplication by the first unit. -/
theorem val_mul_zpow_natCast_mul {K : Type*} [CommGroupWithZero K] (u v : Kˣ) (n : ℕ) :
    ((u * v : Kˣ) : K) ^ (n : ℤ) * (u : K) = (u : K) ^ (n + 1) * (v : K) ^ n := by
  simp only [Units.val_mul, zpow_natCast, mul_pow, pow_succ]
  ac_rfl

/-- A strictly negative power of the product of two units gives the inverse monomial with
the consecutive exponents exchanged. -/
theorem val_mul_zpow_neg_natCast_succ_mul {K : Type*} [CommGroupWithZero K]
    (u v : Kˣ) (n : ℕ) :
    ((u * v : Kˣ) : K) ^ (-((n : ℤ) + 1)) * (u : K) =
      ((v : K) ^ (n + 1) * (u : K) ^ n)⁻¹ := by
  have h : (u * v) ^ (-((n : ℤ) + 1)) * u = (v ^ (n + 1) * u ^ n)⁻¹ := by
    simp [zpow_neg, zpow_add, mul_pow, pow_succ, mul_assoc, mul_left_comm, mul_comm]
  simpa only [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
    Units.val_pow_eq_pow_val] using congrArg (fun w : Kˣ ↦ (w : K)) h

end Units
