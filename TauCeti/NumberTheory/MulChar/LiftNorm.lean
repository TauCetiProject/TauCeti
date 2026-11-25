/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.RingTheory.Norm.Defs
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Norm.Basic
import TauCeti.FieldTheory.Finite.Card
import TauCeti.FieldTheory.Finite.EulerCriterion
import TauCeti.RingTheory.Norm.Units

/-!
# Lifting multiplicative characters through the norm

For an extension `E/F` of commutative rings and a multiplicative character `χ` of `F`, the
character `χ.liftNorm E` of `E` agrees with `χ ∘ N_{E/F}` on the units of `E` and vanishes on the
non-units, where `N_{E/F} = Algebra.norm F` is the norm. For a finite-dimensional extension of
fields it is `χ ∘ N_{E/F}` everywhere (`MulChar.liftNorm_apply`). For a finite extension of
finite fields this is the operation that carries a character of `F` to the character of `E`
whose Gauss sum (against the trace lift of an additive character) the Hasse–Davenport relation
compares with the Gauss sum of `χ`.

Lifting is a group homomorphism `MulChar F R →* MulChar E R` (`MulChar.liftNormHom`). For finite
fields the norm is surjective on units (`FiniteField.unitsMap_norm_surjective`), so lifting is
injective and preserves orders. Its image consists exactly of the characters of `E` that are
trivial on the elements of norm one, equivalently those whose `(#F - 1)`-th power is trivial: in
the cyclic group `Eˣ` the elements of norm one are the `(#F - 1)`-th powers
(`TauCeti.FiniteField.norm_eq_one_iff_exists_pow_eq`). Consequently, for `d ∣ #F - 1`, the
characters of `E` of order dividing `d` are exactly the lifts of the characters of `F` of order
dividing `d`. The quadratic character of `F` lifts to the quadratic character of `E`, in every
characteristic.

## Main definitions

* `MulChar.liftNorm`: the lift of a multiplicative character of `F` to `E` through the norm,
  equal to `χ ∘ N_{E/F}` on units (and everywhere for finite-dimensional field extensions).
* `MulChar.liftNormHom`: lifting as a monoid homomorphism `MulChar F R →* MulChar E R`.

## Main results

* `MulChar.liftNorm_apply`: for a finite-dimensional extension of fields,
  `χ.liftNorm E x = χ (Algebra.norm F x)` for every `x`.
* `MulChar.liftNorm_injective`: over finite fields, lifting is injective.
* `MulChar.orderOf_liftNorm`: over finite fields, lifting preserves the order of a character.
* `MulChar.exists_liftNorm_eq_iff_forall_norm_eq_one` and `MulChar.exists_liftNorm_eq_iff`: a
  character of `E` is a lift exactly when it is trivial on the units of norm one, equivalently when
  its `(#F - 1)`-th power is trivial.
* `MulChar.exists_liftNorm_eq_of_pow_eq_one`: for `d ∣ #F - 1`, every character of `E` of order
  dividing `d` is the lift of a character of `F` of order dividing `d`.
* `MulChar.liftNorm_quadraticChar`: the quadratic character of `F` lifts to the quadratic
  character of `E`.

## References

* K. Ireland and M. Rosen, *A Classical Introduction to Modern Number Theory*, Chapter 11, §4.
* R. Lidl and H. Niederreiter, *Finite Fields*, Chapter 5, §5.2.
-/

public section

namespace MulChar

section CommRing

variable {F : Type*} [CommRing F] (E : Type*) [CommRing E] [Algebra F E]
  {R : Type*} [CommMonoidWithZero R]

/-- The **lift of a multiplicative character through the norm**: for an extension `E/F` and a
multiplicative character `χ` of `F`, the character of `E` that agrees with `χ ∘ N_{E/F}` on the
units of `E` and vanishes on the non-units. It is built from the unit homomorphism
`x ↦ χ (N_{E/F} x)` on `Eˣ`; for a finite-dimensional extension of fields it is `χ ∘ N_{E/F}`
everywhere (`MulChar.liftNorm_apply`). -/
noncomputable def liftNorm (χ : MulChar F R) : MulChar E R :=
  ofUnitHom (χ.toUnitHom.comp (TauCeti.Algebra.normUnits F))

variable {E}

/-- On a unit `x` of `E`, the lift of `χ` takes the value `χ (N_{E/F} x)`. -/
@[simp]
theorem liftNorm_apply_coe (χ : MulChar F R) (x : Eˣ) :
    χ.liftNorm E x = χ (Algebra.norm F (x : E)) := by
  rw [liftNorm, ofUnitHom_coe, MonoidHom.comp_apply, coe_toUnitHom, TauCeti.Algebra.coe_normUnits]

variable (E)

/-- The lift of the trivial character is trivial. -/
@[simp]
theorem liftNorm_one : (1 : MulChar F R).liftNorm E = 1 := by
  ext x
  rw [liftNorm_apply_coe, one_apply_coe, ← TauCeti.Algebra.coe_normUnits, one_apply_coe]

/-- Lifting is multiplicative. -/
@[simp]
theorem liftNorm_mul (χ χ' : MulChar F R) :
    (χ * χ').liftNorm E = χ.liftNorm E * χ'.liftNorm E := by
  ext x
  simp only [liftNorm_apply_coe, coeToFun_mul, Pi.mul_apply]

/-- Lifting multiplicative characters through the norm, as a monoid homomorphism. -/
noncomputable def liftNormHom : MulChar F R →* MulChar E R where
  toFun χ := χ.liftNorm E
  map_one' := liftNorm_one E
  map_mul' := liftNorm_mul E

/-- The homomorphism `MulChar.liftNormHom` is `MulChar.liftNorm`. -/
@[simp]
theorem liftNormHom_apply (χ : MulChar F R) : liftNormHom E χ = χ.liftNorm E := (rfl)

/-- Lifting commutes with powers. -/
@[simp]
theorem liftNorm_pow (χ : MulChar F R) (n : ℕ) : (χ ^ n).liftNorm E = χ.liftNorm E ^ n :=
  map_pow (liftNormHom E) χ n

/-- Lifting commutes with inverses. -/
@[simp]
theorem liftNorm_inv (χ : MulChar F R) : χ⁻¹.liftNorm E = (χ.liftNorm E)⁻¹ :=
  map_inv (liftNormHom E) χ

/-- Lifting commutes with changing the values along a ring homomorphism. -/
@[simp]
theorem liftNorm_ringHomComp {R R' : Type*} [CommRing R] [CommRing R'] (χ : MulChar F R)
    (f : R →+* R') : (χ.ringHomComp f).liftNorm E = (χ.liftNorm E).ringHomComp f := by
  ext x
  simp only [liftNorm_apply_coe, ringHomComp_apply]

end CommRing

section Field

variable {F : Type*} [Field F] {E : Type*} [Field E] [Algebra F E]
  {R : Type*} [CommMonoidWithZero R]

/-- For a finite-dimensional extension of fields, the lift of `χ` is `χ ∘ N_{E/F}`. -/
@[simp]
theorem liftNorm_apply [FiniteDimensional F E] (χ : MulChar F R) (x : E) :
    χ.liftNorm E x = χ (Algebra.norm F x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [map_nonunit _ not_isUnit_zero, Algebra.norm_zero, map_nonunit _ not_isUnit_zero]
  · exact liftNorm_apply_coe χ (Units.mk0 x hx)

variable [Finite E]

variable (E) in
/-- For an extension of finite fields, lifting characters through the norm is injective, the norm
being surjective on units. -/
theorem liftNorm_injective : Function.Injective (liftNorm (F := F) (R := R) E) := by
  intro χ χ' h
  ext u
  obtain ⟨x, rfl⟩ := FiniteField.unitsMap_norm_surjective F E u
  simpa only [liftNorm_apply_coe, Units.coe_map] using
    DFunLike.congr_fun h (x : E)

/-- For an extension of finite fields, two characters with the same lift are equal. -/
@[simp]
theorem liftNorm_inj {χ χ' : MulChar F R} : χ.liftNorm E = χ'.liftNorm E ↔ χ = χ' :=
  (liftNorm_injective E).eq_iff

/-- For an extension of finite fields, a character lifts to the trivial character only if it is
trivial. -/
@[simp]
theorem liftNorm_eq_one_iff {χ : MulChar F R} : χ.liftNorm E = 1 ↔ χ = 1 :=
  (liftNorm_injective E).eq_iff' (liftNorm_one E)

variable (E) in
/-- For an extension of finite fields, the lift of a character through the norm has the same order
as the character. -/
theorem orderOf_liftNorm (χ : MulChar F R) : orderOf (χ.liftNorm E) = orderOf χ :=
  orderOf_injective (liftNormHom E) (liftNorm_injective E) χ

/-- **The image of lifting, by the kernel of the norm.** For an extension of finite fields, a
character of `E` is the lift of a character of `F` exactly when it is trivial on the units of norm
one. -/
theorem exists_liftNorm_eq_iff_forall_norm_eq_one {χ' : MulChar E R} :
    (∃ χ : MulChar F R, χ.liftNorm E = χ') ↔
      ∀ x : Eˣ, Algebra.norm F (x : E) = 1 → χ' x = 1 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨χ, rfl⟩ x hx
    rw [liftNorm_apply_coe, hx, map_one]
  -- Factor the unit homomorphism of `χ'` through the surjective norm `Eˣ → Fˣ`.
  let N : Eˣ →* Fˣ := TauCeti.Algebra.normUnits F
  have hker : N.ker ≤ χ'.toUnitHom.ker := fun x hx ↦ by
    rw [MonoidHom.mem_ker, ← Units.val_eq_one, coe_toUnitHom]
    exact h x (by simpa [N, Units.ext_iff] using hx)
  have hN : Function.Surjective N := fun u ↦ by
    obtain ⟨x, rfl⟩ := FiniteField.unitsMap_norm_surjective F E u
    exact ⟨x, Units.ext (by simp [N])⟩
  refine ⟨ofUnitHom (N.liftOfSurjective hN ⟨χ'.toUnitHom, hker⟩), ext fun x ↦ ?_⟩
  rw [liftNorm_apply_coe, ← TauCeti.Algebra.coe_normUnits, ofUnitHom_coe]
  exact congrArg Units.val
    (N.liftOfRightInverse_comp_apply _ _ ⟨χ'.toUnitHom, hker⟩ x) |>.trans (coe_toUnitHom χ' x)

/-- **The image of lifting.** For an extension of finite fields, a character `χ'` of `E` is the
lift of a character of `F` exactly when `χ' ^ (#F - 1) = 1`. -/
theorem exists_liftNorm_eq_iff {χ' : MulChar E R} :
    (∃ χ : MulChar F R, χ.liftNorm E = χ') ↔ χ' ^ (Nat.card F - 1) = 1 := by
  have : Finite F := Finite.of_injective _ (algebraMap F E).injective
  rw [exists_liftNorm_eq_iff_forall_norm_eq_one]
  refine ⟨fun h ↦ ext fun x ↦ ?_, fun h x hx ↦ ?_⟩
  · -- `x ^ (#F - 1)` has norm `N(x) ^ (#F - 1) = 1`.
    have hx : (TauCeti.Algebra.normUnits F x) ^ (Nat.card F - 1) = 1 := by
      rw [← Nat.card_units, pow_card_eq_one']
    rw [pow_apply_coe, one_apply_coe, ← map_pow, ← Units.val_pow_eq_pow_val]
    exact h _ (by simpa [Units.ext_iff] using hx)
  · -- An element of norm one is a `(#F - 1)`-th power.
    have hq : Nat.card F - 1 ≠ 0 := Nat.sub_ne_zero_of_lt Finite.one_lt_card
    obtain ⟨b, hb⟩ := (TauCeti.FiniteField.norm_eq_one_iff_exists_pow_eq x.ne_zero).1 hx
    have hb0 : b ≠ 0 := ne_zero_pow hq (hb ▸ x.ne_zero)
    rw [← hb, map_pow, ← pow_apply' _ hq, h, one_apply (Ne.isUnit hb0)]

/-- For an extension of finite fields and `d ∣ #F - 1`, every character of `E` of order dividing
`d` is the lift of a character of `F` of order dividing `d`. Conversely a lift has order dividing
`d` exactly when the character does (`MulChar.liftNorm_pow`, `MulChar.liftNorm_eq_one_iff`). -/
theorem exists_liftNorm_eq_of_pow_eq_one {d : ℕ} (hd : d ∣ Nat.card F - 1) {χ' : MulChar E R}
    (h : χ' ^ d = 1) : ∃ χ : MulChar F R, χ ^ d = 1 ∧ χ.liftNorm E = χ' := by
  obtain ⟨k, hk⟩ := hd
  obtain ⟨χ, hχ⟩ := exists_liftNorm_eq_iff.2 (by rw [hk, pow_mul, h, one_pow])
  exact ⟨χ, liftNorm_eq_one_iff (E := E).1 (by rw [liftNorm_pow, hχ, h]), hχ⟩

end Field

section Quadratic

variable (F : Type*) [Field F] [Fintype F] (E : Type*) [Field E] [Fintype E] [Algebra F E]

variable [DecidableEq F] [DecidableEq E]

/-- **The quadratic character lifts to the quadratic character.** For an extension `E/F` of
finite fields, the quadratic character of `F` composed with the norm is the quadratic character
of `E`: a nonzero `x ∈ E` is a square exactly when its norm is a square in `F`. In characteristic
two both characters are trivial. -/
@[simp]
theorem liftNorm_quadraticChar : (quadraticChar F).liftNorm E = quadraticChar E := by
  have : Module.Finite F E := .of_finite
  ext x
  rw [liftNorm_apply_coe]
  have hN : Algebra.norm F (x : E) ≠ 0 := (Algebra.norm_ne_zero_iff).2 x.ne_zero
  have hE : ringChar E = ringChar F := (Algebra.ringChar_eq F E).symm
  by_cases hF : ringChar F = 2
  · rw [quadraticChar_eq_one_of_char_two hF hN, quadraticChar_eq_one_of_char_two (hE.trans hF)
      x.ne_zero]
  -- Compare the values `±1` in `E`, where `1 ≠ -1`, through Euler's criterion on both sides.
  refine Int.cast_injOn_of_ringChar_ne_two (R := E) (hE ▸ hF) ?_ ?_ ?_
  · rcases quadraticChar_dichotomy hN with h | h <;> simp [h]
  · rcases quadraticChar_dichotomy x.ne_zero with h | h <;> simp [h]
  · rw [← map_intCast (algebraMap F E), quadraticChar_eq_pow_of_char_ne_two' hF,
      quadraticChar_eq_pow_of_char_ne_two' (hE ▸ hF), map_pow,
      FiniteField.algebraMap_norm_eq_pow, ← pow_mul]
    simp only [Fintype.card_eq_nat_card]
    rw [TauCeti.FiniteField.card_div_two_eq_mul_card_div_two (F := F) (F' := E)
      (Nat.odd_iff.2 (by simpa using FiniteField.odd_card_of_char_ne_two hF))]

end Quadratic

end MulChar
