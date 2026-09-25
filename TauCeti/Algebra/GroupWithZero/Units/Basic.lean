/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Data.Set.Operations
-- Non-public: the `IsLocalHom` instance for a monoid-with-zero homomorphism out of a group with
-- zero is used only in the proof below.
import Mathlib.Algebra.GroupWithZero.Units.Lemmas

/-!
# Units and powers in groups with zero

Two elementary facts about a group with zero `G₀`.

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

## Main results

* `TauCeti.pow_mul_inv_pow_eq_zpow₀`: `a ^ i * a⁻¹ ^ (n - i) = a ^ (2 * i - n)` for `i ≤ n`.
* `TauCeti.mem_range_iff_exists_units_map_eq`: a unit lies in the range of a monoid-with-zero
  homomorphism out of a group with zero exactly when it is `Units.map` of a unit.
-/

public section

namespace TauCeti

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

end TauCeti
