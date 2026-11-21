/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.Convolution
public import TauCeti.NumberTheory.ArithmeticFunction.BellSeries
import TauCeti.NumberTheory.DirichletCharacter.Polynomial

/-!
# Bell series of Dirichlet characters

Since a Dirichlet character `χ` is completely multiplicative on positive integers, its Bell series
at a prime `p` is the geometric series `∑ χ(p) ^ k X ^ k`, which is the formal reciprocal of
`1 - χ(p) X` in `PowerSeries R`.

Combining this with `DirichletCharacter.prod_one_sub_C_primitiveCharacter_prime_mul_X` identifies
the Bell series at `p` of the Dirichlet convolution
`∏ χ : DirichletCharacter R N, toArithmeticFunction (χ.primitiveCharacter ·)` as the formal
reciprocal of `(1 - X ^ f) ^ (φ(m) / f)`, where `m = ordCompl[p] N` and
`f = orderOf (p : ZMod m)`.

## Main results

* `DirichletCharacter.bellSeries_toArithmeticFunction_mul_one_sub_C_mul_X`:
  `bellSeries p hp (toArithmeticFunction (χ ·)) * (1 - PowerSeries.C (χ p) * PowerSeries.X) = 1`.
* `DirichletCharacter.bellSeries_prod_toArithmeticFunction_primitiveCharacter_mul_pow_one_sub`:
  the Bell series at `p` of the convolution of the primitive characters inducing the characters
  modulo `N` is the formal reciprocal of `(1 - X ^ f) ^ (φ(m) / f)`.

## References

* T. M. Apostol, *Introduction to Analytic Number Theory*, §2.16.
* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 4.3.
-/

public section

namespace DirichletCharacter

/-- The Bell series at a prime `p` of a Dirichlet character `χ` (regarded as an arithmetic
function) is the formal reciprocal of `1 - χ(p) X`. -/
theorem bellSeries_toArithmeticFunction_mul_one_sub_C_mul_X {R : Type*} [CommRing R] {N p : ℕ}
    (hp : p.Prime) (χ : DirichletCharacter R N) :
    ArithmeticFunction.bellSeries p hp (toArithmeticFunction (χ ·)) *
      (1 - PowerSeries.C (χ p) * PowerSeries.X) = 1 :=
  ArithmeticFunction.bellSeries_mul_one_sub_C_mul_X hp fun j ↦ by
    simp [toArithmeticFunction, hp.ne_zero]

/-- **Local Bell-series reciprocal of the primitive-character convolution.** For a prime `p` and a
nonzero level `N`, let `m = ordCompl[p] N` and `f = orderOf (p : ZMod m)`. Over any integral domain
`R` with enough roots of unity for `(ZMod m)ˣ`, the Bell series at `p` of
`∏ χ : DirichletCharacter R N, toArithmeticFunction (χ.primitiveCharacter ·)` is the formal inverse
of `(1 - X ^ f) ^ (φ(m) / f)`. -/
theorem bellSeries_prod_toArithmeticFunction_primitiveCharacter_mul_pow_one_sub
    {R : Type*} [CommRing R] [IsDomain R] {N p : ℕ} [NeZero N] (hp : p.Prime)
    [HasEnoughRootsOfUnity R (Monoid.exponent (ZMod (ordCompl[p] N))ˣ)] :
    ArithmeticFunction.bellSeries p hp
        (∏ χ : DirichletCharacter R N, toArithmeticFunction (χ.primitiveCharacter ·)) *
      (1 - PowerSeries.X ^ orderOf (p : ZMod (ordCompl[p] N))) ^
        ((ordCompl[p] N).totient / orderOf (p : ZMod (ordCompl[p] N))) = 1 := by
  have hpoly :
      (∏ χ : DirichletCharacter R N,
        (1 - PowerSeries.C (χ.primitiveCharacter (p : ZMod χ.conductor)) * PowerSeries.X)) =
        (1 - PowerSeries.X ^ orderOf (p : ZMod (ordCompl[p] N))) ^
          ((ordCompl[p] N).totient / orderOf (p : ZMod (ordCompl[p] N))) := by
    have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := R))
      (prod_one_sub_C_primitiveCharacter_prime_mul_X (R := R) hp
        (Nat.ordProj_mul_ordCompl_eq_self N p).symm (Nat.not_dvd_ordCompl hp (NeZero.ne N)))
    simpa [map_prod, map_pow, _root_.map_sub, _root_.map_one, _root_.map_mul] using h
  rw [map_prod, ← hpoly, ← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun χ _ ↦
    bellSeries_toArithmeticFunction_mul_one_sub_C_mul_X hp χ.primitiveCharacter

end DirichletCharacter
