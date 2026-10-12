/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import TauCeti.Algebra.Lie.UniversalEnveloping.Abelian

/-!
# The enveloping algebra of a line is a polynomial ring

For an abelian Lie algebra `L` over a commutative ring `R` with a basis `b`, the enveloping
algebra `U(L)` is the polynomial algebra on the `b i`
(`TauCeti.UniversalEnvelopingAlgebra.mvPolynomialEquiv`). This file reads off the **one-variable**
case, where a single basis vector makes `U(L)` the polynomial ring `R[X]` in the image of that
vector.

The one-variable case is where the Poincaré--Birkhoff--Witt theorem is first visible: its content
is that the powers `ι(b default) ^ n` are linearly independent, and here they are the ordinary
monomials of a polynomial ring, `TauCeti.UniversalEnvelopingAlgebra.basisPow`. Both the algebra
identification and the basis are stated for a basis indexed by an arbitrary `Unique` type rather
than by `PUnit`, since that is what `MvPolynomial.uniqueAlgEquiv` provides and a consumer holding
a `Basis (Fin 1) R L` should not have to reindex it.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.polynomialEquiv`: for a basis of an abelian `L` indexed by a
  `Unique` type, the identification `R[X] ≃ₐ[R] U(L)`.
* `TauCeti.UniversalEnvelopingAlgebra.basisPow`: the powers of the image of the basis vector, as
  an `R`-basis of `U(L)` indexed by `ℕ`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.polynomialEquiv_X` and
  `TauCeti.UniversalEnvelopingAlgebra.polynomialEquiv_X_pow`: **the variable goes to the canonical
  generator, and its powers to the powers of that generator** -- the normalization without which
  the identification says nothing about the Poincaré--Birkhoff--Witt monomials.
* `TauCeti.UniversalEnvelopingAlgebra.polynomialEquiv_toAlgHom`: the identification is evaluation
  at the canonical generator.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Chapter V,
  §17.2 (the abelian case of the Poincaré--Birkhoff--Witt theorem).
-/

public section

universe u v w

namespace TauCeti.UniversalEnvelopingAlgebra

open Module

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L] [IsLieAbelian L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-! ### The one-variable polynomial identification -/

variable {κ : Type w} [Unique κ]

/-- **The enveloping algebra of an abelian Lie algebra with a one-element basis is a polynomial
ring** in one variable, the variable going to the image of the basis vector
(`TauCeti.UniversalEnvelopingAlgebra.polynomialEquiv_X`).

This is the one-variable case of
`TauCeti.UniversalEnvelopingAlgebra.mvPolynomialEquiv`, composed with Mathlib's
`MvPolynomial.uniqueAlgEquiv`. -/
noncomputable def polynomialEquiv (b : Basis κ R L) : Polynomial R ≃ₐ[R] U :=
  (MvPolynomial.uniqueAlgEquiv R κ).symm.trans (mvPolynomialEquiv R L b)

/-- The polynomial identification sends the variable to the canonical generator `ι R (b default)`
of `U(L)`. Together with `TauCeti.UniversalEnvelopingAlgebra.polynomialEquiv_C` this pins
`polynomialEquiv` down, an algebra map out of `R[X]` being determined by the image of `X`. -/
@[simp]
theorem polynomialEquiv_X (b : Basis κ R L) :
    polynomialEquiv R L b Polynomial.X = _root_.UniversalEnvelopingAlgebra.ι R (b default) := by
  have hX : (MvPolynomial.uniqueAlgEquiv R κ) (MvPolynomial.X default) = Polynomial.X := by
    simp
  rw [polynomialEquiv, AlgEquiv.trans_apply, ← hX, AlgEquiv.symm_apply_apply, mvPolynomialEquiv_X]

/-- The polynomial identification is the algebra map on scalars. This is not a `simp` lemma: its
left-hand side is not in `simp`-normal form, `Polynomial.C_eq_algebraMap` rewriting `C r` to
`algebraMap R _ r`, which `AlgEquiv.commutes` then carries across. -/
theorem polynomialEquiv_C (b : Basis κ R L) (r : R) :
    polynomialEquiv R L b (Polynomial.C r) = algebraMap R U r := by
  rw [Polynomial.C_eq_algebraMap, AlgEquiv.commutes]

/-- **The `n`-th power of the variable goes to the `n`-th power of the canonical generator.** This
is the normalization the Poincaré--Birkhoff--Witt monomials of a one-dimensional Lie algebra are
asked for: the monomial basis of `R[X]` is carried to the powers of `ι R (b default)`, and not to
any other scaling of them. It is not a `simp` lemma: its left-hand side is not in `simp`-normal
form, `map_pow` distributing the identification over the power first. -/
theorem polynomialEquiv_X_pow (b : Basis κ R L) (n : ℕ) :
    polynomialEquiv R L b (Polynomial.X ^ n) =
      _root_.UniversalEnvelopingAlgebra.ι R (b default) ^ n := by
  rw [map_pow, polynomialEquiv_X]

/-- The polynomial identification sends a monomial to a scaled power of the canonical generator. -/
theorem polynomialEquiv_monomial (b : Basis κ R L) (n : ℕ) (r : R) :
    polynomialEquiv R L b (Polynomial.monomial n r) =
      r • _root_.UniversalEnvelopingAlgebra.ι R (b default) ^ n := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, map_mul, polynomialEquiv_C, polynomialEquiv_X_pow,
    Algebra.smul_def]

/-- **The polynomial identification is evaluation at the canonical generator.** -/
theorem polynomialEquiv_toAlgHom (b : Basis κ R L) :
    (polynomialEquiv R L b : Polynomial R →ₐ[R] U) =
      Polynomial.aeval (_root_.UniversalEnvelopingAlgebra.ι R (b default)) :=
  Polynomial.algHom_ext (by simp)

/-- The inverse of the polynomial identification sends the canonical generator `ι R (b default)`
of `U(L)` back to the variable. This is the form to quote by hand; the `simp`-normal form is
`TauCeti.UniversalEnvelopingAlgebra.polynomialEquiv_symm_ι'`, because `simp` rewrites `ι` to
`mkAlgHom` by `UniversalEnvelopingAlgebra.ι_apply`. -/
theorem polynomialEquiv_symm_ι (b : Basis κ R L) :
    (polynomialEquiv R L b).symm (_root_.UniversalEnvelopingAlgebra.ι R (b default)) =
      Polynomial.X :=
  (polynomialEquiv R L b).symm_apply_eq.mpr (polynomialEquiv_X R L b).symm

/-- `TauCeti.UniversalEnvelopingAlgebra.polynomialEquiv_symm_ι` with its left-hand side in
`simp`-normal form: the `simp` lemma `UniversalEnvelopingAlgebra.ι_apply` unfolds `ι R (b default)`
to `mkAlgHom R L (TensorAlgebra.ι R (b default))`, so this is the shape `simp` actually meets. -/
@[simp]
theorem polynomialEquiv_symm_ι' (b : Basis κ R L) :
    (polynomialEquiv R L b).symm
        (_root_.UniversalEnvelopingAlgebra.mkAlgHom R L (TensorAlgebra.ι R (b default))) =
      Polynomial.X := by
  simpa using polynomialEquiv_symm_ι R L b

/-- **The powers of the image of a one-element basis are a basis of the enveloping algebra.** This
is the Poincaré--Birkhoff--Witt ordered-monomial theorem for a Lie algebra of rank one: a monomial
in a single generator is recorded by its exponent, and the powers are linearly independent.

This is `TauCeti.UniversalEnvelopingAlgebra.basisMonomials` with its index changed from the
exponent functions `κ →₀ ℕ` to the exponent itself: a consumer of a rank-one enveloping algebra
reads off degrees, and would otherwise have to transport every statement along
`Finsupp.uniqueEquiv`. -/
noncomputable def basisPow (b : Basis κ R L) : Basis ℕ R U :=
  (basisMonomials R L b).reindex (Finsupp.uniqueEquiv default)

/-- The `n`-th vector of `TauCeti.UniversalEnvelopingAlgebra.basisPow` is the `n`-th power of the
canonical generator. -/
@[simp]
theorem basisPow_apply (b : Basis κ R L) (n : ℕ) :
    basisPow R L b n = _root_.UniversalEnvelopingAlgebra.ι R (b default) ^ n := by
  rw [basisPow, Basis.reindex_apply, Finsupp.uniqueEquiv_symm_apply, basisMonomials_apply]
  exact Finsupp.prod_single_index (pow_zero _)

end TauCeti.UniversalEnvelopingAlgebra
