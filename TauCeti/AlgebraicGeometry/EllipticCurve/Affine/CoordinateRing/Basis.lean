/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
-- Body-only: the monomial basis of the polynomial ring, used to define `basisMonomials`.
import Mathlib.Algebra.Polynomial.Basis

/-!
# The monomial basis of the coordinate ring of a Weierstrass curve

Let `W` be a Weierstrass curve over a commutative ring `R`, and let `x` and `y` be the coordinate
functions of its affine coordinate ring `R[W] = R[X, Y] ⧸ (W(X, Y))`. Mathlib provides the basis
`{1, y}` of `R[W]` over `R[X]`, `WeierstrassCurve.Affine.CoordinateRing.basis`. Together with the
monomial basis of `R[X]` over `R` it gives a basis of `R[W]` over `R` itself: the monomials `xⁱ`
and `xⁱy`.

## Main definitions

* `WeierstrassCurve.Affine.CoordinateRing.basisMonomials`: the basis of `R[W]` over `R` formed by
  the monomials `xⁱ` and `xⁱy`.

## Main results

* `WeierstrassCurve.Affine.CoordinateRing.basisMonomials_apply`: the basis vector at `(i, j)` is
  the monomial `xⁱyʲ`.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/PoleFiltration.lean`. `basisMonomials` is the
definition of the private `coordinateRingMonomialBasis` of that file; the source has no lemma for
its general value.
-/

public section

open Polynomial

namespace WeierstrassCurve.Affine.CoordinateRing

variable {R : Type*} [CommRing R] (W : Affine R)

/-- The monomials `xⁱ` and `xⁱy` in the coordinate functions `x` and `y` form a basis of the
coordinate ring `R[W]` over the base ring `R`: the basis vector at `(i, j) : ℕ × Fin 2` is `xⁱyʲ`.
See `WeierstrassCurve.Affine.CoordinateRing.basis` for the basis `{1, y}` of `R[W]` over `R[X]`. -/
protected noncomputable def basisMonomials : Module.Basis (ℕ × Fin 2) R W.CoordinateRing :=
  (Polynomial.basisMonomials R).smulTower (CoordinateRing.basis W)

/-- The basis vector of `CoordinateRing.basisMonomials` at `(i, j)` is the monomial `xⁱyʲ`. The
coordinate functions `x` and `y` are written `AdjoinRoot.of W.polynomial X` and
`AdjoinRoot.root W.polynomial`, the `simp` normal forms of `CoordinateRing.mk W (C X)` and
`CoordinateRing.mk W Y`. -/
@[simp]
theorem basisMonomials_apply (i : ℕ) (j : Fin 2) :
    CoordinateRing.basisMonomials W (i, j) =
      AdjoinRoot.of W.polynomial X ^ i * AdjoinRoot.root W.polynomial ^ (j : ℕ) := by
  simp only [CoordinateRing.basisMonomials, Module.Basis.smulTower_apply, coe_basisMonomials,
    ← X_pow_eq_monomial, basis_apply, AdjoinRoot.powerBasis'_gen, smul, map_pow, AdjoinRoot.mk_C]

end WeierstrassCurve.Affine.CoordinateRing

end
