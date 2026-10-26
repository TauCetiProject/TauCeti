/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.SkewPolynomial.Basic
public import TauCeti.Algebra.OreExtension.Basic

/-!
# Ore extensions without derivation are skew polynomial rings

Mathlib's `SkewPolynomial R` is the ring of left-coefficient polynomials `∑ aᵢ Xⁱ` with
`X * a = φ a * X`, where the twist `φ` is not a parameter: it is read off from an instance
`[MulSemiringAction (Multiplicative ℕ) R]` as the action of the generator `ofAdd 1`. The Ore
extension `OreExtension σ 0` with zero skew derivation has the same normal form and the same
commutation rule `X * C a = C (σ a) * X`, with `σ` an explicit parameter.

This file identifies the two, as rings and as `k`-algebras, for any action whose generator acts
by `σ`. The identification is the identity on left coefficients. Since the twist of an Ore
extension is a parameter, no instance depending on `σ` is declared globally. Instead,
`RingHom.powersMulSemiringAction f` is the action of `Multiplicative ℕ` in which `ofAdd n` acts by
the iterate `f^[n]`; installing it locally (for instance with `letI`) for `f = σ` puts
`SkewPolynomial R` in the form required here.

## Main definitions

* `RingHom.powersMulSemiringAction`: the action of `Multiplicative ℕ` through the powers of a ring
  endomorphism; for an algebra endomorphism it commutes with the scalars, by
  `AlgHom.smulCommClass_powersMulSemiringAction`.
* `TauCeti.OreExtension.skewPolynomialEquiv`: the ring isomorphism
  `OreExtension σ 0 ≃+* SkewPolynomial R`.
* `TauCeti.OreExtension.skewPolynomialAlgEquiv`: the same isomorphism as `k`-algebras.

## Main statements

* `TauCeti.OreExtension.coeff_skewPolynomialEquiv`: the isomorphism preserves left coefficients.
* `TauCeti.OreExtension.skewPolynomialEquiv_C` and `skewPolynomialEquiv_X`: it sends constants
  to constants and the Ore variable to the skew polynomial variable.

## References

* P. M. Cohn, *Free Rings and Their Relations*, second edition, Chapter 2, where skew polynomial
  rings are the Ore extensions with zero derivation.
-/

public section

noncomputable section

open Multiplicative

namespace RingHom

variable {R : Type*} [Semiring R]

/-- The action of `Multiplicative ℕ` on `R` in which `ofAdd n` acts by the `n`-th iterate of the
ring endomorphism `f`. This is the action through which `SkewPolynomial R` takes `f` as its twist.
It is not an instance, since it depends on `f`. -/
abbrev powersMulSemiringAction (f : R →+* R) : MulSemiringAction (Multiplicative ℕ) R :=
  MulSemiringAction.compHom R (powersHom (R →+* R) f)

/-- In `f.powersMulSemiringAction`, the element `ofAdd n` acts by the iterate `f^[n]`. -/
@[simp]
theorem powersMulSemiringAction_smul (f : R →+* R) (n : ℕ) (a : R) :
    letI := f.powersMulSemiringAction
    (ofAdd n : Multiplicative ℕ) • a = f^[n] a := by
  let := f.powersMulSemiringAction
  exact (MulAction.compHom_smul_def (powersHom (R →+* R) f) (ofAdd n) a).trans (by simp)

end RingHom

namespace AlgHom

variable {k R : Type*} [CommSemiring k] [Semiring R] [Algebra k R]

/-- The action of `Multiplicative ℕ` through the powers of an algebra endomorphism commutes with
the scalars. This is the hypothesis under which `SkewPolynomial R` is a `k`-algebra. -/
theorem smulCommClass_powersMulSemiringAction (σ : R →ₐ[k] R) :
    letI := (σ : R →+* R).powersMulSemiringAction
    SMulCommClass (Multiplicative ℕ) k R := by
  let := (σ : R →+* R).powersMulSemiringAction
  refine ⟨fun n c a => ?_⟩
  obtain ⟨n, rfl⟩ := ofAdd.surjective n
  rw [RingHom.powersMulSemiringAction_smul, RingHom.powersMulSemiringAction_smul, coe_toRingHom,
    ← coe_pow, map_smul]

end AlgHom

namespace TauCeti.OreExtension

variable {k R : Type*} [CommSemiring k] [Semiring R] [Algebra k R] {σ : R →ₐ[k] R}
  [MulSemiringAction (Multiplicative ℕ) R]

/-- The skew polynomial variable satisfies the Ore relation of `OreExtension σ 0` when the
generator of the action is `σ`. -/
private theorem skewPolynomial_X_mul_C (hσ : ∀ a : R, (ofAdd 1 : Multiplicative ℕ) • a = σ a)
    (a : R) :
    SkewPolynomial.X * SkewPolynomial.CRingHom a =
      SkewPolynomial.CRingHom (σ a) * SkewPolynomial.X +
        SkewPolynomial.CRingHom ((0 : SigmaDerivation σ) a) := by
  simp only [SigmaDerivation.coe_zero, Pi.zero_apply, map_zero, add_zero,
    SkewPolynomial.CRingHom_eq_C]
  calc
    SkewPolynomial.X * SkewPolynomial.C a =
        SkewPolynomial.monomial 1 ((ofAdd 1 : Multiplicative ℕ) • a) := by
      rw [← SkewPolynomial.monomial_zero_left, SkewPolynomial.X_mul_monomial,
        MulSemiringAction.toRingHom_apply]
    _ = SkewPolynomial.C (σ a) * SkewPolynomial.X := by
      rw [hσ, SkewPolynomial.C_mul_X_eq_monomial]

/-- The ring homomorphism `OreExtension σ 0 → SkewPolynomial R` fixing constants and the
variable. -/
private def toSkewPolynomial (hσ : ∀ a : R, (ofAdd 1 : Multiplicative ℕ) • a = σ a) :
    OreExtension σ 0 →+* SkewPolynomial R :=
  lift SkewPolynomial.CRingHom SkewPolynomial.X (skewPolynomial_X_mul_C hσ)

private theorem toSkewPolynomial_monomial
    (hσ : ∀ a : R, (ofAdd 1 : Multiplicative ℕ) • a = σ a) (n : ℕ) (a : R) :
    toSkewPolynomial hσ (monomial n a) = SkewPolynomial.monomial n a := by
  rw [toSkewPolynomial, lift_apply, eval₂_monomial, SkewPolynomial.CRingHom_eq_C,
    SkewPolynomial.C_mul_X_pow_eq_monomial]

private theorem coeff_toSkewPolynomial
    (hσ : ∀ a : R, (ofAdd 1 : Multiplicative ℕ) • a = σ a) (p : OreExtension σ 0) (n : ℕ) :
    (toSkewPolynomial hσ p).coeff n = p.coeff n := by
  induction p using induction_on with
  | zero => simp
  | add m a p _ _ ih =>
    rw [map_add, SkewPolynomial.coeff_add, coeff_add, ih, toSkewPolynomial_monomial,
      SkewPolynomial.coeff_monomial, coeff_monomial]

private theorem toSkewPolynomial_bijective
    (hσ : ∀ a : R, (ofAdd 1 : Multiplicative ℕ) • a = σ a) :
    Function.Bijective (toSkewPolynomial hσ) := by
  refine ⟨fun p p' h => ext fun n => ?_, fun p => ?_⟩
  · rw [← coeff_toSkewPolynomial hσ, h, coeff_toSkewPolynomial]
  · induction p using SkewPolynomial.induction with
    | h0 => exact ⟨0, map_zero _⟩
    | ha n a p _ _ ih =>
      obtain ⟨p', rfl⟩ := ih
      exact ⟨monomial n a + p', by rw [map_add, toSkewPolynomial_monomial]⟩

/-- An Ore extension with zero skew derivation is isomorphic to Mathlib's skew polynomial ring,
for any action of `Multiplicative ℕ` on the coefficients whose generator acts by `σ`. The
isomorphism preserves left coefficients; see `coeff_skewPolynomialEquiv`. -/
def skewPolynomialEquiv (hσ : ∀ a : R, (ofAdd 1 : Multiplicative ℕ) • a = σ a) :
    OreExtension σ 0 ≃+* SkewPolynomial R :=
  RingEquiv.ofBijective (toSkewPolynomial hσ) (toSkewPolynomial_bijective hσ)

variable (hσ : ∀ a : R, (ofAdd 1 : Multiplicative ℕ) • a = σ a)

/-- The isomorphism with skew polynomials preserves every left coefficient. -/
@[simp]
theorem coeff_skewPolynomialEquiv (p : OreExtension σ 0) (n : ℕ) :
    (skewPolynomialEquiv hσ p).coeff n = p.coeff n :=
  coeff_toSkewPolynomial hσ p n

/-- The inverse isomorphism preserves every left coefficient. -/
@[simp]
theorem coeff_skewPolynomialEquiv_symm (p : SkewPolynomial R) (n : ℕ) :
    ((skewPolynomialEquiv hσ).symm p).coeff n = p.coeff n := by
  rw [← coeff_skewPolynomialEquiv hσ, RingEquiv.apply_symm_apply]

/-- The isomorphism with skew polynomials sends the monomial `a Xⁿ` to the monomial `a Xⁿ`. -/
@[simp]
theorem skewPolynomialEquiv_monomial (n : ℕ) (a : R) :
    skewPolynomialEquiv hσ (monomial n a) = SkewPolynomial.monomial n a :=
  toSkewPolynomial_monomial hσ n a

/-- The inverse isomorphism sends the skew monomial `a Xⁿ` to the Ore monomial `a Xⁿ`. -/
@[simp]
theorem skewPolynomialEquiv_symm_monomial (n : ℕ) (a : R) :
    (skewPolynomialEquiv hσ).symm (SkewPolynomial.monomial n a) = monomial n a := by
  rw [RingEquiv.symm_apply_eq, skewPolynomialEquiv_monomial]

/-- The isomorphism with skew polynomials sends constants to constants. -/
@[simp]
theorem skewPolynomialEquiv_C (a : R) :
    skewPolynomialEquiv hσ (C a) = SkewPolynomial.C a := by
  rw [← monomial_zero_left, skewPolynomialEquiv_monomial, SkewPolynomial.monomial_zero_left]

/-- The inverse isomorphism sends constants to constants. -/
@[simp]
theorem skewPolynomialEquiv_symm_C (a : R) :
    (skewPolynomialEquiv hσ).symm (SkewPolynomial.C a) = C a := by
  rw [RingEquiv.symm_apply_eq, skewPolynomialEquiv_C]

/-- The isomorphism with skew polynomials sends the Ore variable to the skew variable. -/
@[simp]
theorem skewPolynomialEquiv_X : skewPolynomialEquiv hσ X = SkewPolynomial.X := by
  rw [X_eq_monomial, skewPolynomialEquiv_monomial, SkewPolynomial.monomial_one_one_eq_X]

/-- The inverse isomorphism sends the skew variable to the Ore variable. -/
@[simp]
theorem skewPolynomialEquiv_symm_X : (skewPolynomialEquiv hσ).symm SkewPolynomial.X = X := by
  rw [RingEquiv.symm_apply_eq, skewPolynomialEquiv_X]

/-- An Ore extension with zero skew derivation is isomorphic, as a `k`-algebra, to Mathlib's skew
polynomial ring, for any action of `Multiplicative ℕ` commuting with the scalars `k` whose
generator acts by `σ`. -/
def skewPolynomialAlgEquiv [SMulCommClass (Multiplicative ℕ) k R] :
    OreExtension σ 0 ≃ₐ[k] SkewPolynomial R where
  __ := skewPolynomialEquiv hσ
  commutes' c := by
    simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, algebraMap_apply,
      skewPolynomialEquiv_C, SkewMonoidAlgebra.coe_algebraMap, Function.comp_apply]
    rw [← SkewPolynomial.monomial_zero_left, SkewPolynomial.monomial_def, ofAdd_zero]

/-- The algebra isomorphism agrees with the ring isomorphism `skewPolynomialEquiv`. -/
@[simp]
theorem skewPolynomialAlgEquiv_apply [SMulCommClass (Multiplicative ℕ) k R]
    (p : OreExtension σ 0) : skewPolynomialAlgEquiv hσ p = skewPolynomialEquiv hσ p := (rfl)

/-- The inverse algebra isomorphism agrees with the inverse of `skewPolynomialEquiv`. -/
@[simp]
theorem skewPolynomialAlgEquiv_symm_apply [SMulCommClass (Multiplicative ℕ) k R]
    (p : SkewPolynomial R) :
    (skewPolynomialAlgEquiv hσ).symm p = (skewPolynomialEquiv hσ).symm p := (rfl)

end TauCeti.OreExtension
