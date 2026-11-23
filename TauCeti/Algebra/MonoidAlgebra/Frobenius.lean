/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.CharP.Algebra

/-!
# Frobenius on monoid algebras

Let `R` be a commutative semiring of exponential characteristic `p` and `M` a commutative monoid.
The `p`-th power map of the monoid algebra `R[M]` raises both the coefficients and the monomials
to the `p`-th power: `(∑ aₘ m) ^ p = ∑ aₘ ^ p m ^ p`. Hence it is injective as soon as the `p`-th
power maps of `R` and of `M` are injective.

Each statement has an additive form for `AddMonoidAlgebra`, where the `p`-th power map of the
monoid becomes multiplication by `p`.

## Main declarations

* `MonoidAlgebra.expChar`: a monoid algebra has the exponential characteristic of its
  coefficients.
* `MonoidAlgebra.mapRingHom_frobenius_mapDomainRingHom_powMonoidHom`: the `p`-th power map of
  `R[M]` in terms of the Frobenius of `R` and the `p`-th power map of `M`.
* `MonoidAlgebra.pow_expChar_injective`: the `p`-th power map of `R[M]` is injective when the
  `p`-th power maps of `R` and of `M` are injective.

## References

The formula for the `p`-th power map is the monoid-algebra form of Mathlib's
`Polynomial.map_frobenius_expand`.
-/

public section

open scoped MonoidAlgebra

namespace MonoidAlgebra

/-- A monoid algebra has the exponential characteristic of its coefficient semiring. -/
@[to_additive (dont_translate := R)
/-- An additive monoid algebra has the exponential characteristic of its coefficient semiring. -/]
instance expChar {R M : Type*} [Semiring R] [MulOneClass M] (p : ℕ) [ExpChar R p] :
    ExpChar R[M] p :=
  expChar_of_injective_ringHom (f := singleOneRingHom) single_right_injective p

variable {R M : Type*} [CommSemiring R] [CommMonoid M] (p : ℕ) [ExpChar R p]

/-- In exponential characteristic `p`, the `p`-th power of an element of a commutative monoid
algebra is obtained by raising its coefficients and its monomials to the `p`-th power. -/
@[to_additive (dont_translate := R)
/-- In exponential characteristic `p`, the `p`-th power of an element of a commutative additive
monoid algebra is obtained by raising its coefficients to the `p`-th power and multiplying its
exponents by `p`. -/]
theorem mapRingHom_frobenius_mapDomainRingHom_powMonoidHom (x : R[M]) :
    mapRingHom M (frobenius R p) (mapDomainRingHom R (powMonoidHom p) x) = x ^ p := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp [(expChar_pos R p).ne']
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_pow_expChar]
  | single m a => simp [frobenius_def]

/-- In exponential characteristic `p`, the `p`-th power map of a commutative monoid algebra is
injective when the `p`-th power maps of the coefficient semiring and of the monoid are
injective. -/
@[to_additive (dont_translate := R) pow_expChar_injective
/-- In exponential characteristic `p`, the `p`-th power map of a commutative additive monoid
algebra is injective when the `p`-th power map of the coefficient semiring and multiplication by
`p` on the monoid are injective. -/]
theorem pow_expChar_injective (hR : Function.Injective fun r : R ↦ r ^ p)
    (hM : Function.Injective fun m : M ↦ m ^ p) : Function.Injective fun x : R[M] ↦ x ^ p := by
  have hfrob : Function.Injective (frobenius R p) := fun a b hab ↦
    hR (by simpa only [frobenius_def] using hab)
  have hpow : ⇑(powMonoidHom p : M →* M) = fun m ↦ m ^ p := funext (powMonoidHom_apply p)
  intro x y hxy
  beta_reduce at hxy
  rw [← mapRingHom_frobenius_mapDomainRingHom_powMonoidHom p x,
    ← mapRingHom_frobenius_mapDomainRingHom_powMonoidHom p y, coe_mapRingHom,
    mapDomainRingHom_apply, mapDomainRingHom_apply, hpow] at hxy
  exact mapDomain_injective hM (map_injective _ hfrob hxy)

end MonoidAlgebra
