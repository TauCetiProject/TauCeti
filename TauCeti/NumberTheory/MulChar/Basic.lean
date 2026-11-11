/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic

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
(`MulChar.apply_neg_one_mul_self`), so `χ (-1) = ±1` when the coefficients form a domain.

Pushing a character along an injective ring homomorphism of the coefficients preserves its order
(`MulChar.orderOf_ringHomComp`).

Quadratic characters are closed under multiplication (`MulChar.IsQuadratic.mul`), and hence a
finite product of quadratic characters is quadratic (`MulChar.isQuadratic_prod`).
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

/-- A multiplicative character takes a value at `-1` whose square is `1`. -/
@[simp]
theorem apply_neg_one_mul_self {R R' : Type*} [CommMonoid R] [HasDistribNeg R]
    [CommMonoidWithZero R'] (χ : MulChar R R') : χ (-1) * χ (-1) = 1 := by
  rw [← map_mul, neg_one_mul, neg_neg, map_one]

/-- Pushing a multiplicative character along an injective ring homomorphism of the coefficients
preserves its order. -/
@[simp]
theorem orderOf_ringHomComp {R R' R'' : Type*} [CommMonoid R] [CommRing R'] [CommRing R'']
    {f : R' →+* R''} (hf : Function.Injective f) (χ : MulChar R R') :
    orderOf (χ.ringHomComp f) = orderOf χ := by
  rw [← ringHomCompHom_apply, orderOf_injective _ (injective_ringHomComp hf)]

/-- The product of two quadratic characters is quadratic. -/
theorem IsQuadratic.mul {M R : Type*} [CommMonoid M] [CommRing R] {χ ψ : MulChar M R}
    (hχ : χ.IsQuadratic) (hψ : ψ.IsQuadratic) : (χ * ψ).IsQuadratic := by
  intro a
  rw [mul_apply]
  rcases hχ a with h | h | h <;> rcases hψ a with h' | h' | h' <;> simp [h, h']

/-- A finite product of quadratic characters is quadratic. -/
theorem isQuadratic_prod {M R ι : Type*} [CommMonoid M] [CommRing R]
    {s : Finset ι} {χ : ι → MulChar M R} (hχ : ∀ i ∈ s, (χ i).IsQuadratic) :
    (∏ i ∈ s, χ i).IsQuadratic := by
  refine Finset.prod_induction χ IsQuadratic (fun _ _ ↦ IsQuadratic.mul) (fun a ↦ ?_) hχ
  by_cases ha : IsUnit a
  · exact Or.inr (Or.inl (one_apply ha))
  · exact Or.inl (map_nonunit 1 ha)

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
