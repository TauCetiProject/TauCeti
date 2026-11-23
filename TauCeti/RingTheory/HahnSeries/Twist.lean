/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.HahnSeries.Multiplication
public import TauCeti.Algebra.Algebra.Equiv

/-!
# Twisting Hahn series by a character of the exponent monoid

Let `χ : Multiplicative Γ →* R` be a character of the exponent monoid `Γ` with values in a
commutative semiring `R`, and let `A` be an `R`-algebra. Multiplying the coefficient of `t ^ g` by
`χ g` is an `R`-algebra endomorphism of `HahnSeries Γ A`, the **twist** by `χ`: it can only shrink
supports, and it is multiplicative because `χ (g + h) = χ g * χ h` for every pair of exponents
`(g, h)` contributing to a coefficient of a product, while scalars from `R` commute with the
coefficients in `A`. Twisting by a product of characters is the composite of the twists, so
unit-valued characters give `R`-algebra automorphisms. Taking the coefficients in an arbitrary
`R`-algebra `A`, rather than in `R` itself, follows the convention of Mathlib's
`HahnSeries.embDomainAlgHom`.

For Laurent series and `χ k = a ^ k` this is the rescaling `f (X) ↦ f (a X)`. For rational
exponents, a character of `ℚ` trivial on `ℤ` built from a compatible system of roots of unity
gives the coefficientwise Galois action on Puiseux series, `t ^ (k / n) ↦ ζₙ ^ k t ^ (k / n)`.

## Main definitions

* `HahnSeries.twist χ`: the `R`-algebra endomorphism of `HahnSeries Γ A` multiplying the
  coefficient of `t ^ g` by `χ g`.
* `HahnSeries.twistEquiv`: the twists by unit-valued characters, as a homomorphism to the
  `R`-algebra automorphisms of `HahnSeries Γ A`.

## Main results

* `HahnSeries.coeff_twist`, `HahnSeries.coeff_twistEquiv`, `HahnSeries.coeff_twistEquiv_symm`:
  the twisted coefficients.
* `HahnSeries.twistEquiv_symm`: the inverse of the twist by `χ` is the twist by `χ⁻¹`.
* `HahnSeries.twist_one`, `HahnSeries.twist_mul`: twisting is a monoid action of the characters.
* `HahnSeries.twist_single`, `HahnSeries.twistEquiv_single`: the twist of a monomial.
* `HahnSeries.support_twistEquiv`, `HahnSeries.orderTop_twistEquiv`: twisting by a unit-valued
  character preserves supports and orders.
-/

public section

open Finset

namespace HahnSeries

variable {Γ R A : Type*} [AddCommMonoid Γ] [PartialOrder Γ] [CommSemiring R] [Semiring A]
  [Algebra R A]

/-- The coefficientwise twist of a Hahn series by `χ`, before bundling: its coefficient of `t ^ g`
is `χ g` times that of `x`. -/
private def twistFun (χ : Multiplicative Γ →* R) (x : HahnSeries Γ A) : HahnSeries Γ A where
  coeff g := χ (.ofAdd g) • x.coeff g
  isPWO_support' :=
    x.isPWO_support.mono (Function.support_smul_subset_right (fun g ↦ χ (.ofAdd g)) x.coeff)

/-- The coefficient equation of `twistFun`, from which `HahnSeries.coeff_twist` is derived. -/
private theorem coeff_twistFun (χ : Multiplicative Γ →* R) (x : HahnSeries Γ A) (g : Γ) :
    (twistFun χ x).coeff g = χ (.ofAdd g) • x.coeff g :=
  rfl

/-- The support inclusion for `twistFun`, from which `HahnSeries.support_twist_subset` is
derived. -/
private theorem support_twistFun_subset (χ : Multiplicative Γ →* R) (x : HahnSeries Γ A) :
    (twistFun χ x).support ⊆ x.support := fun g hg ↦
  (mem_support x g).2 fun h ↦ (mem_support _ g).1 hg (by rw [coeff_twistFun, h, smul_zero])

/-- The monomial rule for `twistFun`, from which `HahnSeries.twist_single` is derived. -/
private theorem twistFun_single (χ : Multiplicative Γ →* R) (g : Γ) (a : A) :
    twistFun χ (single g a) = single g (χ (.ofAdd g) • a) := by
  classical
  ext h
  rw [coeff_twistFun, coeff_single, coeff_single, ← Pi.single_apply, ← Pi.single_apply]
  exact Pi.apply_single (fun i (b : A) ↦ χ (.ofAdd i) • b) (fun _ ↦ smul_zero _) g a h

variable [IsOrderedCancelAddMonoid Γ]

/-- The **twist** of Hahn series by a character `χ` of the exponent monoid: the `R`-algebra
endomorphism multiplying the coefficient of `t ^ g` by `χ g`. -/
noncomputable def twist (χ : Multiplicative Γ →* R) : HahnSeries Γ A →ₐ[R] HahnSeries Γ A where
  toFun := twistFun χ
  map_one' := by
    rw [← single_zero_one, twistFun_single, ofAdd_zero, map_one, one_smul]
  map_mul' x y := by
    ext a
    -- Sum both products over the antidiagonal of the untwisted supports: the extra pairs have a
    -- vanishing twisted coefficient.
    have hsub := antidiagonal_mono_right (hs := x.isPWO_support) (a := a)
      (support_twistFun_subset χ y) (hu := (twistFun χ y).isPWO_support) (ht := y.isPWO_support)
    rw [coeff_twistFun, coeff_mul, coeff_mul_left' x.isPWO_support (support_twistFun_subset χ x),
      smul_sum, sum_subset hsub fun ij hij hij' ↦ ?_]
    · refine sum_congr rfl fun ij hij ↦ ?_
      rw [coeff_twistFun, coeff_twistFun, ← (mem_antidiagonal.1 hij).2.2, ofAdd_add, map_mul,
        smul_mul_smul_comm]
    · simp only [mem_antidiagonal, mem_support, ne_eq, not_and] at hij hij'
      rw [not_not.1 fun h ↦ hij' hij.1 h hij.2.2, mul_zero]
  map_zero' := by
    ext g
    rw [coeff_twistFun, coeff_zero, smul_zero]
  map_add' x y := by
    ext g
    rw [coeff_twistFun, coeff_add, coeff_add, coeff_twistFun, coeff_twistFun, smul_add]
  commutes' r := by
    rw [algebraMap_apply, C_apply, twistFun_single, ofAdd_zero, map_one, one_smul]

/-- The twist by `χ` multiplies the coefficient of `t ^ g` by `χ g`. -/
@[simp]
theorem coeff_twist (χ : Multiplicative Γ →* R) (x : HahnSeries Γ A) (g : Γ) :
    (twist χ x).coeff g = χ (.ofAdd g) • x.coeff g :=
  coeff_twistFun χ x g

/-- Twisting does not enlarge the support. -/
theorem support_twist_subset (χ : Multiplicative Γ →* R) (x : HahnSeries Γ A) :
    (twist χ x).support ⊆ x.support :=
  support_twistFun_subset χ x

/-- The twist of the monomial `a t ^ g` by `χ` is `χ g a t ^ g`. -/
@[simp]
theorem twist_single (χ : Multiplicative Γ →* R) (g : Γ) (a : A) :
    twist χ (single g a) = single g (χ (.ofAdd g) • a) :=
  twistFun_single χ g a

/-- Twisting by the trivial character is the identity. -/
@[simp]
theorem twist_one : twist (1 : Multiplicative Γ →* R) = AlgHom.id R (HahnSeries Γ A) := by
  ext x g
  rw [coeff_twist, MonoidHom.one_apply, one_smul, AlgHom.id_apply]

/-- Twisting by a product of characters is the composite of the twists. -/
theorem twist_mul (χ ψ : Multiplicative Γ →* R) :
    (twist (χ * ψ) : HahnSeries Γ A →ₐ[R] HahnSeries Γ A) = (twist χ).comp (twist ψ) := by
  ext x g
  rw [coeff_twist, AlgHom.comp_apply, coeff_twist, coeff_twist, MonoidHom.mul_apply, mul_smul]

/-- The twists by unit-valued characters, as a homomorphism to the `R`-algebra automorphisms of
`HahnSeries Γ A`: the automorphism attached to `χ` multiplies the coefficient of `t ^ g` by
`χ g`, and its inverse twists by `χ⁻¹` (`HahnSeries.twistEquiv_symm`). -/
noncomputable def twistEquiv :
    (Multiplicative Γ →* Rˣ) →* (HahnSeries Γ A ≃ₐ[R] HahnSeries Γ A) :=
  (AlgEquiv.algHomUnitsEquiv R (HahnSeries Γ A)).toMonoidHom.comp
    (({ toFun := twist
        map_one' := twist_one
        map_mul' := twist_mul } :
      (Multiplicative Γ →* R) →* (HahnSeries Γ A →ₐ[R] HahnSeries Γ A)).comp
        (MonoidHom.compHom (Units.coeHom R))).toHomUnits

/-- The automorphism attached to a unit-valued character `χ` is the twist by `χ`. -/
theorem twistEquiv_apply (χ : Multiplicative Γ →* Rˣ) (x : HahnSeries Γ A) :
    twistEquiv χ x = twist ((Units.coeHom R).comp χ) x := by
  rw [twistEquiv, AlgEquiv.algHomUnitsEquiv_comp_toHomUnits_apply, MonoidHom.comp_apply,
    MonoidHom.compHom_apply_apply, MonoidHom.coe_mk, OneHom.coe_mk]

/-- The automorphism attached to a unit-valued character `χ` multiplies the coefficient of `t ^ g`
by `χ g`. -/
@[simp]
theorem coeff_twistEquiv (χ : Multiplicative Γ →* Rˣ) (x : HahnSeries Γ A) (g : Γ) :
    (twistEquiv χ x).coeff g = (χ (.ofAdd g) : R) • x.coeff g := by
  rw [twistEquiv_apply, coeff_twist, MonoidHom.comp_apply, Units.coeHom_apply]

/-- The automorphism attached to a unit-valued character `χ` sends the monomial `a t ^ g` to
`χ g a t ^ g`. -/
@[simp]
theorem twistEquiv_single (χ : Multiplicative Γ →* Rˣ) (g : Γ) (a : A) :
    twistEquiv χ (single g a) = single g ((χ (.ofAdd g) : R) • a) := by
  rw [twistEquiv_apply, twist_single, MonoidHom.comp_apply, Units.coeHom_apply]

/-- The inverse of the automorphism attached to a unit-valued character `χ` is the automorphism
attached to `χ⁻¹`. -/
theorem twistEquiv_symm (χ : Multiplicative Γ →* Rˣ) :
    (twistEquiv χ).symm = (twistEquiv χ⁻¹ : HahnSeries Γ A ≃ₐ[R] HahnSeries Γ A) := by
  rw [← AlgEquiv.aut_inv, ← map_inv]

/-- The inverse of the automorphism attached to a unit-valued character `χ` multiplies the
coefficient of `t ^ g` by the inverse of `χ g`. -/
@[simp]
theorem coeff_twistEquiv_symm (χ : Multiplicative Γ →* Rˣ) (x : HahnSeries Γ A) (g : Γ) :
    ((twistEquiv χ).symm x).coeff g = (((χ (.ofAdd g))⁻¹ : Rˣ) : R) • x.coeff g := by
  rw [twistEquiv_symm, coeff_twistEquiv, MonoidHom.inv_apply]

/-- Twisting by a unit-valued character preserves the support. -/
@[simp]
theorem support_twistEquiv (χ : Multiplicative Γ →* Rˣ) (x : HahnSeries Γ A) :
    (twistEquiv χ x).support = x.support := by
  ext g
  simp only [mem_support, coeff_twistEquiv, ne_eq, Units.isUnit, IsUnit.smul_eq_zero]

/-- Twisting by a unit-valued character preserves the order. -/
@[simp]
theorem orderTop_twistEquiv (χ : Multiplicative Γ →* Rˣ) (x : HahnSeries Γ A) :
    (twistEquiv χ x).orderTop = x.orderTop := by
  by_cases hx : x = 0
  · rw [hx, map_zero]
  rw [orderTop_of_ne_zero hx,
    orderTop_of_ne_zero ((map_ne_zero_iff _ (twistEquiv χ).injective).mpr hx)]
  simp only [support_twistEquiv]

end HahnSeries
