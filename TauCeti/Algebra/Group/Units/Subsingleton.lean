/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Submonoid.Defs
public import Mathlib.Algebra.Group.Units.Hom
public import Mathlib.Algebra.Group.WithOne.Defs

/-!
# Trivial unit groups and zero-sum-free monoids

An additive monoid `A` is *zero-sum-free* when `a + b = 0 ↔ a = 0 ∧ b = 0`. In Mathlib this
condition is represented by `Subsingleton (AddUnits A)`, the additive dual of `Subsingleton Mˣ`;
for Dedekind-finite monoids (including all commutative monoids), `TauCeti.subsingleton_addUnits_iff`
records the equivalence of the two formulations.

Products and indexed products are already covered by `Prod.instSubsingletonAddUnits` and
`Pi.instSubsingletonAddUnits`, and multiplicative submonoids by `Submonoid.instSubsingletonUnits`.
This file supplies the remaining basic instances: additive submonoid classes (covering
`AddSubmonoid` and `Subsemiring`), `WithOne` and `WithZero`, and nontriviality of the units of a
nontrivial group (so no nontrivial ring is zero-sum-free).
-/

public section

namespace TauCeti

/-- In a Dedekind-finite monoid, the unit group is trivial if and only if `1` has no nontrivial
factorizations. -/
@[to_additive
/-- In a Dedekind-finite additive monoid (in particular, any additive commutative monoid), the
group of additive units is trivial if and only if `a + b = 0 ↔ a = 0 ∧ b = 0` for all `a` and
`b`. -/]
theorem subsingleton_units_iff {M : Type*} [Monoid M] [IsDedekindFiniteMonoid M] :
    Subsingleton Mˣ ↔ ∀ a b : M, a * b = 1 ↔ a = 1 ∧ b = 1 :=
  ⟨fun _ _ _ => mul_eq_one,
    fun h => .units_of_isUnit fun _ ⟨u, hu⟩ => hu ▸ ((h u ↑u⁻¹).mp u.val_inv).1⟩

@[to_additive]
instance instNontrivialUnits {G : Type*} [Group G] [Nontrivial G] : Nontrivial Gˣ :=
  let ⟨g, hg⟩ := exists_ne (1 : G)
  ⟨⟨1, Units.mk g g⁻¹ (mul_inv_cancel g) (inv_mul_cancel g),
    fun h => hg (congrArg Units.val h).symm⟩⟩

/-- A nontrivial group does not have a subsingleton unit group. -/
@[to_additive
/-- A nontrivial additive group (in particular, any nontrivial ring) is not zero-sum-free. -/]
theorem not_subsingleton_units_of_nontrivial (G : Type*) [Group G] [Nontrivial G] :
    ¬ Subsingleton Gˣ :=
  not_subsingleton Gˣ

@[to_additive]
instance instSubsingletonUnitsSubtype {M S : Type*} [Monoid M]
    [Subsingleton Mˣ] [SetLike S M] [SubmonoidClass S M] (s : S) :
    Subsingleton sˣ :=
  (Units.map_injective (f := SubmonoidClass.subtype s) Subtype.val_injective).subsingleton

@[to_additive]
instance instSubsingletonUnitsWithOne {M : Type*} [Semigroup M] : Subsingleton (WithOne M)ˣ :=
  .units_of_isUnit fun _ ⟨u, hu⟩ => by
    subst hu
    rcases u with ⟨v, w, hvw, -⟩
    cases v using WithOne.recOneCoe with
    | one => rfl
    | coe x =>
      cases w using WithOne.recOneCoe with
      | one => exact hvw
      | coe y => exact absurd (WithOne.coe_mul x y ▸ hvw) WithOne.coe_ne_one

end TauCeti
