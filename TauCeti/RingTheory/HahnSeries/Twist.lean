/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Indicator
public import Mathlib.RingTheory.HahnSeries.Multiplication

/-!
# Twisting Hahn series by a character of the exponent monoid

Let `χ : Multiplicative Γ →* R` be a character of the exponent monoid `Γ` with values in a
commutative semiring `R`. Multiplying the coefficient of `t ^ g` by `χ g` is an `R`-algebra
endomorphism of `HahnSeries Γ R`, the **twist** by `χ`: it can only shrink supports, and it is
multiplicative because `χ (g + h) = χ g * χ h` for every pair of exponents `(g, h)` contributing to
a coefficient of a product. Twisting by a product of characters is the composite of the twists,
so unit-valued characters give `R`-algebra automorphisms.

For Laurent series and `χ k = a ^ k` this is the rescaling `f (X) ↦ f (a X)`. For rational
exponents, a character of `ℚ` trivial on `ℤ` built from a compatible system of roots of unity
gives the coefficientwise Galois action on Puiseux series, `t ^ (k / n) ↦ ζₙ ^ k t ^ (k / n)`.

## Main definitions

* `HahnSeries.twist χ`: the `R`-algebra endomorphism of `HahnSeries Γ R` multiplying the
  coefficient of `t ^ g` by `χ g`.
* `HahnSeries.twistEquiv`: the twists by unit-valued characters, as a homomorphism to the
  `R`-algebra automorphisms of `HahnSeries Γ R`.

## Main results

* `HahnSeries.coeff_twist`, `HahnSeries.coeff_twistEquiv`: the twisted coefficients.
* `HahnSeries.twist_one`, `HahnSeries.twist_mul`: twisting is a monoid action of the characters.
* `HahnSeries.twist_single`: the twist of a monomial.
-/

public section

open Finset

namespace HahnSeries

variable {Γ R : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [IsOrderedCancelAddMonoid Γ]
  [CommSemiring R]

/-- The coefficientwise twist of a Hahn series by `χ`, before bundling: its coefficient of `t ^ g`
is `χ g` times that of `x`. -/
private def twistFun (χ : Multiplicative Γ →* R) (x : HahnSeries Γ R) : HahnSeries Γ R where
  coeff g := χ (.ofAdd g) * x.coeff g
  isPWO_support' := x.isPWO_support.mono (Function.support_mul_subset_right _ _)

omit [IsOrderedCancelAddMonoid Γ] in
private theorem coeff_twistFun (χ : Multiplicative Γ →* R) (x : HahnSeries Γ R) (g : Γ) :
    (twistFun χ x).coeff g = χ (.ofAdd g) * x.coeff g :=
  rfl

omit [IsOrderedCancelAddMonoid Γ] in
private theorem support_twistFun_subset (χ : Multiplicative Γ →* R) (x : HahnSeries Γ R) :
    (twistFun χ x).support ⊆ x.support :=
  Function.support_mul_subset_right _ _

/-- The **twist** of Hahn series by a character `χ` of the exponent monoid: the `R`-algebra
endomorphism multiplying the coefficient of `t ^ g` by `χ g`. -/
noncomputable def twist (χ : Multiplicative Γ →* R) : HahnSeries Γ R →ₐ[R] HahnSeries Γ R where
  toFun := twistFun χ
  map_one' := by
    ext g
    rw [coeff_twistFun, coeff_one]
    split_ifs with h
    · rw [h, ofAdd_zero, map_one, one_mul]
    · rw [mul_zero]
  map_mul' x y := by
    ext a
    -- Sum both products over the antidiagonal of the untwisted supports: the extra pairs have a
    -- vanishing twisted coefficient.
    have hsub := antidiagonal_mono_right (hs := x.isPWO_support) (a := a)
      (support_twistFun_subset χ y) (hu := (twistFun χ y).isPWO_support) (ht := y.isPWO_support)
    rw [coeff_twistFun, coeff_mul, coeff_mul_left' x.isPWO_support (support_twistFun_subset χ x),
      mul_sum, sum_subset hsub fun ij hij hij' ↦ ?_]
    · refine sum_congr rfl fun ij hij ↦ ?_
      rw [coeff_twistFun, coeff_twistFun, ← (mem_antidiagonal.1 hij).2.2, ofAdd_add, map_mul,
        mul_mul_mul_comm]
    · simp only [mem_antidiagonal, mem_support, ne_eq, not_and] at hij hij'
      rw [not_not.1 fun h ↦ hij' hij.1 h hij.2.2, mul_zero]
  map_zero' := by
    ext g
    rw [coeff_twistFun, coeff_zero, mul_zero]
  map_add' x y := by
    ext g
    rw [coeff_twistFun, coeff_add, coeff_add, coeff_twistFun, coeff_twistFun, mul_add]
  commutes' r := by
    ext g
    rw [coeff_twistFun, algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, C_apply,
      coeff_single]
    split_ifs with h
    · rw [h, ofAdd_zero, map_one, one_mul]
    · rw [mul_zero]

/-- The twist by `χ` multiplies the coefficient of `t ^ g` by `χ g`. -/
@[simp]
theorem coeff_twist (χ : Multiplicative Γ →* R) (x : HahnSeries Γ R) (g : Γ) :
    (twist χ x).coeff g = χ (.ofAdd g) * x.coeff g :=
  (rfl)

/-- Twisting does not enlarge the support. -/
theorem support_twist_subset (χ : Multiplicative Γ →* R) (x : HahnSeries Γ R) :
    (twist χ x).support ⊆ x.support :=
  support_twistFun_subset χ x

/-- The twist of the monomial `r t ^ g` by `χ` is `χ g r t ^ g`. -/
@[simp]
theorem twist_single (χ : Multiplicative Γ →* R) (g : Γ) (r : R) :
    twist χ (single g r) = single g (χ (.ofAdd g) * r) := by
  ext h
  rw [coeff_twist, coeff_single, coeff_single]
  split_ifs with hh
  · rw [hh]
  · rw [mul_zero]

/-- Twisting by the trivial character is the identity. -/
@[simp]
theorem twist_one : twist (1 : Multiplicative Γ →* R) = AlgHom.id R (HahnSeries Γ R) := by
  ext x g
  rw [coeff_twist, MonoidHom.one_apply, one_mul, AlgHom.id_apply]

/-- Twisting by a product of characters is the composite of the twists. -/
theorem twist_mul (χ ψ : Multiplicative Γ →* R) : twist (χ * ψ) = (twist χ).comp (twist ψ) := by
  ext x g
  rw [coeff_twist, AlgHom.comp_apply, coeff_twist, coeff_twist, MonoidHom.mul_apply, mul_assoc]

/-- The twists by unit-valued characters, as a homomorphism to the `R`-algebra automorphisms of
`HahnSeries Γ R`: the automorphism attached to `χ` multiplies the coefficient of `t ^ g` by
`χ g`, and its inverse twists by `χ⁻¹`. -/
noncomputable def twistEquiv :
    (Multiplicative Γ →* Rˣ) →* (HahnSeries Γ R ≃ₐ[R] HahnSeries Γ R) :=
  (AlgEquiv.algHomUnitsEquiv R (HahnSeries Γ R)).toMonoidHom.comp
    ({ toFun χ := twist ((Units.coeHom R).comp χ)
       map_one' := by rw [MonoidHom.comp_one, twist_one]; rfl
       map_mul' χ ψ := by rw [MonoidHom.comp_mul, twist_mul]; rfl } :
      (Multiplicative Γ →* Rˣ) →* (HahnSeries Γ R →ₐ[R] HahnSeries Γ R)).toHomUnits

/-- The automorphism attached to a unit-valued character `χ` is the twist by `χ`. -/
theorem twistEquiv_apply (χ : Multiplicative Γ →* Rˣ) (x : HahnSeries Γ R) :
    twistEquiv χ x = twist ((Units.coeHom R).comp χ) x :=
  (rfl)

/-- The automorphism attached to a unit-valued character `χ` multiplies the coefficient of `t ^ g`
by `χ g`. -/
@[simp]
theorem coeff_twistEquiv (χ : Multiplicative Γ →* Rˣ) (x : HahnSeries Γ R) (g : Γ) :
    (twistEquiv χ x).coeff g = (χ (.ofAdd g) : R) * x.coeff g :=
  (rfl)

/-- Twisting by a unit-valued character preserves the support. -/
@[simp]
theorem support_twistEquiv (χ : Multiplicative Γ →* Rˣ) (x : HahnSeries Γ R) :
    (twistEquiv χ x).support = x.support := by
  ext g
  simp only [mem_support, coeff_twistEquiv, ne_eq, Units.mul_right_eq_zero]

end HahnSeries
