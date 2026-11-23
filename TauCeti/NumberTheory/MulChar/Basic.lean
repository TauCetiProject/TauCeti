/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Basic facts about multiplicative characters

To show that a multiplicative character takes values in a subset containing zero, it suffices
to check the values on units. This applies, for example, to subfields and subrings containing
the character values on units, since a multiplicative character vanishes on nonunits.

The trivial character takes only the values `0` and `1`, on nonunits and units respectively, so
it is unchanged by transport along a homomorphism of the domain that reflects units (such as an
isomorphism) and a homomorphism of the coefficients (`MulChar.map_one_apply`). Moreover, if a
homomorphism `f` of the coefficients carries `χ` to `χ'` along any map `e` of the domains, that is
`f (χ a) = χ' (e a)`, then it also carries `χ⁻¹` to `χ'⁻¹` and every power `χ ^ n` to `χ' ^ n`.
This is how Galois automorphisms of a number field act on characters such as power residue
symbols.

Since `(-1) * (-1) = 1`, every multiplicative character satisfies `χ (-1) * χ (-1) = 1`
(`MulChar.apply_neg_one_mul_self`), so `χ (-1) = ±1` when the coefficients form a domain. The
same holds for every integer power of `χ (-1)` (`MulChar.apply_neg_one_zpow_mul_self`).

A character of order dividing two is `1` at the square of every unit
(`MulChar.apply_sq_eq_one_of_sq_eq_one`). An integer-valued character pushed into a ring along
`Int.castRingHom` takes the casts of its integer values
(`MulChar.ringHomComp_intCast_apply_of_apply_eq`).

The trivial character is quadratic (`MulChar.isQuadratic_one`), and `MulChar.equivToUnitHom` and
its inverse carry the trivial character `1` and the trivial unit homomorphism `1` to each other
(`MulChar.equivToUnitHom_one`, `MulChar.equivToUnitHom_symm_one`, `MulChar.toUnitHom_one`).

Pushing a character along an injective ring homomorphism of the coefficients preserves its order
(`MulChar.orderOf_ringHomComp`).

A quadratic character takes the value `1` or `-1` at every unit
(`MulChar.IsQuadratic.apply_eq_one_or_eq_neg_one`), so it is trivial when `2 = 0` in the
coefficient ring (`MulChar.IsQuadratic.eq_one_of_two_eq_zero`). Quadratic characters are closed
under multiplication (`MulChar.IsQuadratic.mul`), and hence a
finite product of quadratic characters is quadratic (`MulChar.isQuadratic_prod`).

A character satisfies `χ ^ d = 1` if and only if it is trivial on the `d`-th powers of units
(`MulChar.pow_eq_one_iff_forall_mem_range_apply_eq_one`). At a unit `v`, the inverse character
takes the value `χ⁻¹ v = χ v⁻¹` (`MulChar.inv_apply_coe`). With values in a domain, the sum of a
character over a finite commutative monoid `M` is the cast of `#Mˣ` for the trivial character and
zero otherwise (`MulChar.sum_eq_ite`).

With values in a commutative group with zero, an integer power of a character at a unit is the
integer power of its value (`MulChar.zpow_apply_coe_eq_zpow`), the `ℤ`-exponent form of Mathlib's
`MulChar.pow_apply_coe`.

On a monoid with finitely many units, every value of a character is an algebraic integer
(`MulChar.isIntegral_apply`): `0` at nonunits and a root of unity at units.

On a monoid with zero without zero divisors, a product of character values `∏ⱼ χⱼ(yⱼ)` vanishes
when `∏ⱼ yⱼ = 0` (`MulChar.prod_apply_eq_zero_of_prod_eq_zero`).
-/

public section

namespace MulChar

/-- A multiplicative character takes values in a subset containing `0` whenever all its values
on units lie there. -/
theorem apply_mem_of_forall_unit {R R' S : Type*} [CommMonoid R]
    [CommMonoidWithZero R'] [SetLike S R'] [ZeroMemClass S R'] (χ : MulChar R R') (s : S)
    (hχ : ∀ u : Rˣ, χ (u : R) ∈ s) (a : R) : χ a ∈ s := by
  by_cases ha : IsUnit a
  · rw [← ha.unit_spec]
    exact hχ _
  · rw [MulChar.map_nonunit _ ha]
    exact zero_mem s

/-- The trivial character commutes with transport along a unit-reflecting homomorphism `e` of the
domain (such as an isomorphism) and a homomorphism `f` of the coefficients: both sides are `1` on
units and `0` on nonunits. -/
theorem map_one_apply {R S R' R'' F G : Type*} [CommMonoid R] [CommMonoid S]
    [CommMonoidWithZero R'] [CommMonoidWithZero R''] [FunLike F R' R'']
    [MonoidWithZeroHomClass F R' R''] [FunLike G R S] [MonoidHomClass G R S] (f : F) (e : G)
    [IsLocalHom e] (a : R) : f ((1 : MulChar R R') a) = (1 : MulChar S R'') (e a) := by
  by_cases ha : IsUnit a
  · rw [one_apply ha, one_apply (ha.map e), map_one]
  · rw [map_nonunit _ ha, map_nonunit _ (by rwa [isUnit_map_iff]), map_zero]

/-- The trivial character corresponds to the trivial homomorphism of unit groups under
`MulChar.equivToUnitHom`. -/
@[simp]
theorem equivToUnitHom_one {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R'] :
    equivToUnitHom (1 : MulChar R R') = 1 :=
  map_one mulEquivToUnitHom

/-- `MulChar.equivToUnitHom.symm` sends the trivial unit homomorphism `1` to `1`. -/
@[simp]
theorem equivToUnitHom_symm_one {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R'] :
    equivToUnitHom.symm (1 : Rˣ →* R'ˣ) = 1 :=
  map_one mulEquivToUnitHom.symm

/-- The trivial character restricts to the trivial homomorphism of unit groups. -/
theorem toUnitHom_one {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R'] :
    (1 : MulChar R R').toUnitHom = 1 :=
  equivToUnitHom_one

/-- A multiplicative character takes a value at `-1` whose square is `1`. -/
@[simp]
theorem apply_neg_one_mul_self {R R' : Type*} [CommMonoid R] [HasDistribNeg R]
    [CommMonoidWithZero R'] (χ : MulChar R R') : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

/-- An integer power of the value of a multiplicative character at `-1` squares to `1`. -/
theorem apply_neg_one_zpow_mul_self {R R' : Type*} [CommMonoid R] [HasDistribNeg R]
    [CommGroupWithZero R'] (χ : MulChar R R') (n : ℤ) : χ (-1) ^ n * χ (-1) ^ n = 1 := by
  rw [← mul_zpow, apply_neg_one_mul_self, one_zpow]

/-- A character of order dividing two is `1` at the square of a unit. -/
theorem apply_sq_eq_one_of_sq_eq_one {R R' : Type*} [CommMonoid R] [CommMonoidWithZero R']
    {χ : MulChar R R'} (hχ : χ ^ 2 = 1) {a : R} (ha : IsUnit a) : χ (a ^ 2) = 1 := by
  rw [map_pow, ← pow_apply' χ two_ne_zero, hχ, one_apply ha]

/-- An integer-valued character pushed into a ring takes the cast of its integer value. -/
theorem ringHomComp_intCast_apply_of_apply_eq {R R' : Type*} [CommMonoid R] [CommRing R']
    (χ : MulChar R ℤ) {a : R} {b : ℤ} (h : χ a = b) :
    χ.ringHomComp (Int.castRingHom R') a = b := by
  rw [ringHomComp_apply, h, eq_intCast]

/-- Pushing a multiplicative character along an injective ring homomorphism of the coefficients
preserves its order. -/
@[simp]
theorem orderOf_ringHomComp {R R' R'' : Type*} [CommMonoid R] [CommRing R'] [CommRing R'']
    {f : R' →+* R''} (hf : Function.Injective f) (χ : MulChar R R') :
    orderOf (χ.ringHomComp f) = orderOf χ := by
  rw [← ringHomCompHom_apply, orderOf_injective _ (injective_ringHomComp hf)]

/-- A quadratic character takes the value `1` or `-1` at a unit. -/
theorem IsQuadratic.apply_eq_one_or_eq_neg_one {M R : Type*} [CommMonoid M] [CommRing R]
    {χ : MulChar M R} (hχ : χ.IsQuadratic) {a : M} (ha : IsUnit a) : χ a = 1 ∨ χ a = -1 := by
  rcases hχ a with h | h | h
  · exact Or.inl (h.trans (isUnit_zero_iff.mp (h ▸ ha.map χ)))
  · exact Or.inl h
  · exact Or.inr h

/-- In a ring where `2 = 0`, `1` and `-1` coincide, so every quadratic character is trivial. -/
theorem IsQuadratic.eq_one_of_two_eq_zero {M R : Type*} [CommMonoid M] [CommRing R]
    {χ : MulChar M R} (hχ : χ.IsQuadratic) (hR : (2 : R) = 0) : χ = 1 := by
  refine ext fun u ↦ ?_
  rcases hχ.apply_eq_one_or_eq_neg_one u.isUnit with h | h
  · rw [h, one_apply_coe]
  · rw [h, neg_eq_iff_add_eq_zero.mpr (one_add_one_eq_two.trans hR), one_apply_coe]

/-- The product of two quadratic characters is quadratic. -/
theorem IsQuadratic.mul {M R : Type*} [CommMonoid M] [CommRing R] {χ ψ : MulChar M R}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) : (χ * ψ).IsQuadratic := by
  intro a
  rw [mul_apply]
  rcases hχ a with h | h | h <;> rcases hψ a with h' | h' | h' <;> simp [h, h']

/-- The trivial character is quadratic. -/
@[simp]
theorem isQuadratic_one {M R : Type*} [CommMonoid M] [CommRing R] :
    (1 : MulChar M R).IsQuadratic := by
  intro a
  by_cases ha : IsUnit a
  · exact Or.inr (Or.inl (one_apply ha))
  · exact Or.inl (map_nonunit 1 ha)

/-- A finite product of quadratic characters is quadratic. -/
theorem isQuadratic_prod {M R ι : Type*} [CommMonoid M] [CommRing R]
    {s : Finset ι} {χ : ι → MulChar M R} (hχ : ∀ i ∈ s, (χ i).IsQuadratic) :
    (∏ i ∈ s, χ i).IsQuadratic :=
  Finset.prod_induction χ IsQuadratic (fun _ _ ↦ IsQuadratic.mul) isQuadratic_one hχ

/-- A character satisfies `χ ^ d = 1` if and only if it is trivial on the `d`-th powers of units. -/
theorem pow_eq_one_iff_forall_mem_range_apply_eq_one {M R : Type*} [CommMonoid M]
    [CommMonoidWithZero R] (χ : MulChar M R) (d : ℕ) :
    χ ^ d = 1 ↔ ∀ h ∈ (powMonoidHom d : Mˣ →* Mˣ).range, χ h = 1 := by
  simp only [eq_one_iff, MonoidHom.mem_range, powMonoidHom_apply, forall_exists_index,
    forall_apply_eq_imp_iff, pow_apply_coe, Units.val_pow_eq_pow_val, map_pow]

/-- At a unit `v`, the inverse of a character takes the value `χ v⁻¹`, with the inverse in `Mˣ`. -/
theorem inv_apply_coe {M R : Type*} [CommMonoid M] [CommMonoidWithZero R] (χ : MulChar M R)
    (v : Mˣ) : χ⁻¹ v = χ ↑v⁻¹ := by
  have h : mulEquivToUnitHom χ⁻¹ v = mulEquivToUnitHom χ v⁻¹ := by
    simp only [map_inv, MonoidHom.inv_apply]
  simpa only [mulEquivToUnitHom_apply, coe_equivToUnitHom] using congrArg Units.val h

/-- The sum of a character over a finite commutative monoid `M` is the cast of the number of
units of `M` for the trivial character and zero otherwise. This puts Mathlib's
`MulChar.sum_eq_zero_of_ne_one` and `MulChar.sum_one_eq_card_units` into one statement. -/
@[simp]
theorem sum_eq_ite {M R : Type*} [CommMonoid M] [Fintype M] [CommRing R] [IsDomain R]
    (χ : MulChar M R) [Decidable (χ = 1)] :
    ∑ a, χ a = if χ = 1 then (Nat.card Mˣ : R) else 0 := by
  classical
  split_ifs with hχ
  · rw [hχ, sum_one_eq_card_units, Nat.card_eq_fintype_card]
  · exact sum_eq_zero_of_ne_one hχ

/-- With values in a commutative group with zero, an integer power of a character takes the
integer power of its value at a unit: `(χ ^ n) a = χ a ^ n`. Mathlib's `MulChar.zpow_apply_coe`
instead moves the power onto the unit, `(χ ^ n) a = χ (a ^ n)`. -/
theorem zpow_apply_coe_eq_zpow {R R' : Type*} [CommMonoid R] [CommGroupWithZero R']
    (χ : MulChar R R') (n : ℤ) (a : Rˣ) : (χ ^ n) a = χ a ^ n := by
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · simp [pow_apply_coe]
  · rw [zpow_neg, zpow_natCast, inv_apply_eq_inv, pow_apply_coe, zpow_neg, zpow_natCast,
      Ring.inverse_eq_inv']

/-- The values of a multiplicative character of a monoid with finitely many units are algebraic
integers: `0` at nonunits and roots of unity at units. -/
theorem isIntegral_apply {M R : Type*} [CommMonoid M] [Finite Mˣ] [CommRing R]
    (χ : MulChar M R) (x : M) : IsIntegral ℤ (χ x) := by
  by_cases hx : IsUnit x
  · obtain ⟨u, rfl⟩ := hx
    simpa using χ.toUnitHom.isIntegral_coe_apply u
  · rw [map_nonunit χ hx]
    exact isIntegral_zero

/-- A product of character values `∏ⱼ χⱼ(yⱼ)` vanishes when `∏ⱼ yⱼ = 0`: in a monoid with zero
without zero divisors some `yⱼ` is then `0`, where every character vanishes. -/
theorem prod_apply_eq_zero_of_prod_eq_zero {M R ι : Type*} [CommMonoidWithZero M] [Nontrivial M]
    [NoZeroDivisors M] [CommMonoidWithZero R] {s : Finset ι} (χ : ι → MulChar M R) {y : ι → M}
    (hy : ∏ j ∈ s, y j = 0) : ∏ j ∈ s, χ j (y j) = 0 := by
  obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.mp hy
  exact Finset.prod_eq_zero hj (by rw [hj0, MulChar.map_zero])

section Transport

variable {R S R' R'' F : Type*} [CommMonoid R] [CommMonoid S] [CommMonoidWithZero R']
  [CommMonoidWithZero R''] [FunLike F R' R''] [MonoidWithZeroHomClass F R' R''] {f : F}
  {e : R → S} {χ : MulChar R R'} {χ' : MulChar S R''}

/-- If a homomorphism `f` of the coefficients carries `χ` to `χ'` along a map `e` of the domains,
then it carries `χ⁻¹` to `χ'⁻¹`. -/
theorem map_inv_apply_of_map_apply (h : ∀ a, f (χ a) = χ' (e a)) (a : R) :
    f (χ⁻¹ a) = χ'⁻¹ (e a) := by
  rw [inv_apply_eq_inv, inv_apply_eq_inv, ← h]
  by_cases ha : IsUnit a
  · exact (ha.map χ).map_ringInverse f
  · rw [map_nonunit _ ha, map_zero, Ring.inverse_zero, map_zero, Ring.inverse_zero]

/-- If a homomorphism `f` of the coefficients carries `χ` to `χ'` along a map `e` of the domains,
then it carries `χ ^ n` to `χ' ^ n`. -/
theorem map_pow_apply_of_map_apply (h : ∀ a, f (χ a) = χ' (e a)) (n : ℕ) (a : R) :
    f ((χ ^ n) a) = (χ' ^ n) (e a) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [pow_zero, pow_zero, ← inv_mul χ, ← inv_mul χ', mul_apply, mul_apply, map_mul,
      map_inv_apply_of_map_apply h, h]
  · rw [pow_apply' _ hn, pow_apply' _ hn, map_pow, h]

end Transport

end MulChar
