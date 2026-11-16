/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Orbit products of finite group actions

Let a group `G` act on a commutative monoid `M` by monoid automorphisms. The *orbit product* of
`a : M` is `N(a) = ∏ g : G, g • a`. For a finite group it is `G`-invariant and multiplicative.

The orbit product is indexed by the group, not by the orbit: a nonfaithful action repeats
factors, and for the trivial action `N(a) = a ^ |G|`. So it is not the norm of a finite free
extension. Its use is to manufacture invariant elements with a prescribed multiplicative
property, such as an invariant unit (`IsUnit.orbitProd`) or an invariant pseudouniformiser of a
Tate ring with a continuous action (`TauCeti.Huber.IsPseudoUniformizer.orbitProd`).

## Main definitions

* `TauCeti.MulDistribMulAction.orbitProd G a`: the orbit product `∏ g : G, g • a`.

## Main results

* `TauCeti.MulDistribMulAction.smul_orbitProd`: the orbit product is `G`-invariant.
* `TauCeti.MulDistribMulAction.orbitProd_mul`: it is multiplicative.
* `TauCeti.MulDistribMulAction.orbitProd_eq_pow_card`: for an element fixed by `G` it is the
  `|G|`-th power; in particular it is the element itself for the trivial group
  (`TauCeti.MulDistribMulAction.orbitProd_of_subsingleton`).
* `TauCeti.MulDistribMulAction.orbitProd_mul_orbitProd_inv`: the orbit products of a unit and of
  its inverse are inverse to each other.
-/

public section

namespace TauCeti.MulDistribMulAction

section CommMonoid

variable (G : Type*) {M : Type*} [Group G] [CommMonoid M] [MulDistribMulAction G M]

/-- The *orbit product* `N(a) = ∏ g : G, g • a` of an element of a commutative monoid under a
group action. It is meant for finite groups, where it is `G`-invariant
(`TauCeti.MulDistribMulAction.smul_orbitProd`). The product is indexed by the group, so a
nonfaithful action repeats factors. -/
noncomputable def orbitProd (a : M) : M :=
  ∏ᶠ g : G, g • a

/-- Unfolding lemma for `TauCeti.MulDistribMulAction.orbitProd`. -/
theorem orbitProd_def (a : M) : orbitProd G a = ∏ᶠ g : G, g • a :=
  (rfl)

/-- For a finite group with a chosen `Fintype` structure, the orbit product is a `Finset`
product. -/
theorem orbitProd_eq_prod [Fintype G] (a : M) : orbitProd G a = ∏ g : G, g • a :=
  finprod_eq_prod_of_fintype _

/-- **The orbit product is invariant.** -/
@[simp]
theorem smul_orbitProd [Finite G] (g : G) (a : M) : g • orbitProd G a = orbitProd G a :=
  smul_finprod_perm a g

@[simp]
theorem orbitProd_one : orbitProd G (1 : M) = 1 := by
  simp [orbitProd_def, smul_one]

/-- **The orbit product is multiplicative.** -/
theorem orbitProd_mul [Finite G] (a b : M) :
    orbitProd G (a * b) = orbitProd G a * orbitProd G b := by
  simp only [orbitProd_def, smul_mul']
  exact finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)

/-- The orbit product commutes with powers. -/
theorem orbitProd_pow [Finite G] (a : M) (n : ℕ) : orbitProd G (a ^ n) = orbitProd G a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, orbitProd_mul, ih, pow_succ]

/-- The orbit products of a unit and of its inverse are inverse to each other. -/
theorem orbitProd_mul_orbitProd_inv [Finite G] (u : Mˣ) :
    orbitProd G (u : M) * orbitProd G (↑u⁻¹ : M) = 1 := by
  rw [← orbitProd_mul, Units.mul_inv, orbitProd_one]

/-- The orbit product of an element fixed by every group element is its `|G|`-th power. This
covers the trivial action, where `N(a) = a ^ |G|`. -/
theorem orbitProd_eq_pow_card [Finite G] {a : M} (ha : ∀ g : G, g • a = a) :
    orbitProd G a = a ^ Nat.card G := by
  cases nonempty_fintype G
  simp [orbitProd_eq_prod, ha, Nat.card_eq_fintype_card]

/-- For the trivial group, the orbit product of `a` is `a`. -/
@[simp]
theorem orbitProd_of_subsingleton [Subsingleton G] (a : M) : orbitProd G a = a := by
  have : Finite G := Finite.of_subsingleton
  rw [orbitProd_eq_pow_card G fun g ↦ by rw [Subsingleton.elim g 1, one_smul],
    Nat.card_of_subsingleton (1 : G), pow_one]

end CommMonoid

/-- The orbit product of zero is zero, the product having the factor `1 • 0 = 0`. -/
@[simp]
theorem orbitProd_zero (G : Type*) {M₀ : Type*} [Group G] [Finite G] [CommMonoidWithZero M₀]
    [MulDistribMulAction G M₀] : orbitProd G (0 : M₀) = 0 :=
  finprod_eq_zero _ 1 (one_smul G 0) (Set.toFinite _)

end TauCeti.MulDistribMulAction

/-- **The orbit product of a unit is a unit.** -/
theorem IsUnit.orbitProd (G : Type*) {M : Type*} [Group G] [Finite G] [CommMonoid M]
    [MulDistribMulAction G M] {a : M} (ha : IsUnit a) :
    IsUnit (TauCeti.MulDistribMulAction.orbitProd G a) := by
  obtain ⟨u, rfl⟩ := ha
  exact IsUnit.of_mul_eq_one _ (TauCeti.MulDistribMulAction.orbitProd_mul_orbitProd_inv G u)
