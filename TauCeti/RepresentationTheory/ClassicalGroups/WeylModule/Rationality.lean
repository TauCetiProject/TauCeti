/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Rational
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Rational

/-!
# Rationality of Weyl representations

Weyl modules are images of Young symmetrizers acting on tensor powers of the standard
representation.  The tensor power is polynomial, and the canonical map from it onto the image is
a surjective intertwining map.  Since polynomiality passes to quotients, this realizes every Weyl
representation over `ℂ` as a polynomial representation.

A rational Weyl representation is a Weyl representation tensored with an integral determinant
power.  Determinant powers are rational and tensor products of rational representations are
rational, so the tensor-product presentation
`TauCeti.tprodEquivRationalWeylRep` proves rationality of every rational Weyl representation.

These facts provide the coordinate-regularity input for restricting rational Weyl representations
along inclusions of general linear groups.  They do not assert that rational Weyl representations
exhaust the rational representations; that requires the highest-weight classification.

## Main results

* `TauCeti.isPolynomialRep_weylRepOfShape`: a Weyl representation is polynomial.
* `TauCeti.isRationalRep_rationalWeylRep`: a rational Weyl representation is rational.
-/

public section

open scoped TensorProduct

namespace TauCeti

/-! ## Polynomial Weyl representations -/

/-- **A Weyl representation over `ℂ` is polynomial.**  It is the image of its Young symmetrizer
on a tensor power of the polynomial standard representation. -/
@[simp]
theorem isPolynomialRep_weylRepOfShape (n : ℕ) (μ : YoungDiagram) :
    IsPolynomialRep (weylRepOfShape ℂ n μ) :=
  (isPolynomialRep_tensorPowerRep n μ.card).of_surjective
    (weylRepOfShapeProjection ℂ n μ) (weylRepOfShapeProjection_surjective ℂ n μ)

/-! ## Rational Weyl representations -/

/-- **A rational Weyl representation over `ℂ` is rational.**  Its tensor-product presentation
is the product of a rational determinant power with a polynomial Weyl representation. -/
@[simp]
theorem isRationalRep_rationalWeylRep (n : ℕ) (l : DominantWeight n) :
    IsRationalRep (rationalWeylRep ℂ n l) := by
  have hweyl : IsRationalRep (weylRepOfShape ℂ n l.detShiftShape) :=
    (isPolynomialRep_weylRepOfShape n l.detShiftShape).isRationalRep
  have htprod : IsRationalRep
      ((detPowerRep ℂ n l.detShift).tprod (weylRepOfShape ℂ n l.detShiftShape)) :=
    (isRationalRep_detPowerRep (n := n) l.detShift).tprod hweyl
  apply htprod.of_surjective (tprodEquivRationalWeylRep ℂ n l).toIntertwiningMap
  exact (tprodEquivRationalWeylRep ℂ n l).surjective

end TauCeti
