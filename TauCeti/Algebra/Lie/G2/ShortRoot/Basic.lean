/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.Serre
public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.G2.ShortRootWeight

/-!
# The integral seven-dimensional representation of type G2

This file realizes the Chevalley generators of type `G₂` on the seven-element weight diagram of
the fundamental module `V(ϖ₁)`, whose weights are the six short roots together with zero. In the
fundamental-weight coordinates of `TauCeti.DynkinType.g2Root`, and with Bourbaki's numbering in
which the first simple root `α₁` is short and the second `α₂` is long, the weights are listed as

```text
2α₁ + α₂,  α₁ + α₂,  α₁,  0,  -α₁,  -(α₁ + α₂),  -(2α₁ + α₂),
```

the first being the highest weight `ϖ₁`. On the coordinate vector belonging to a weight, the
Cartan generator `H_i` acts by the `i`-th coordinate of that weight; the lowering generator `F_i`
moves each weight down by `α_i` along the diagram; and the raising generator `E_i` moves it up.
The three-term string `α₁, 0, -α₁` through the zero weight forces a coefficient `2` on one step of
`F₁` and one of `E₁`; it is placed on the step out of the zero weight in both cases, which is what
makes the divided squares `E₁² / 2` and `F₁² / 2` integral matrices.

The resulting integer matrices satisfy the Chevalley--Serre relations for the Cartan matrix
`CartanMatrix.G₂`, whose entry `(i, j)` is the value of the `j`-th simple root on the `i`-th simple
coroot. The universal property of the Serre presentation then gives an explicit integral
seven-dimensional representation of the type-`G₂` Serre Lie algebra. The generators of the short
simple root cube to zero and square to twice an integral matrix; those of the long simple root
square to zero.

No identification with the abstract irreducible highest-weight module is asserted, and nothing
here concerns the group scheme the representation will carry: the carrier built from these
matrices is not identified with the pinned simply connected group scheme of type `G₂`, and
constructions on it transfer to that scheme only along such an identification.

## Main definitions

* `TauCeti.G2ShortRoot.weight`: the seven weights in fundamental-weight coordinates.
* `TauCeti.G2ShortRoot.cartanMatrix`, `raisingMatrix`, and `loweringMatrix`: the integral Cartan,
  raising, and lowering matrices, with `TauCeti.G2ShortRoot.cartanMatrix_apply`,
  `TauCeti.G2ShortRoot.raisingMatrix_apply` and `TauCeti.G2ShortRoot.loweringMatrix_apply` giving
  their entries from the weights and from the step coefficients
  `TauCeti.G2ShortRoot.raisingCoefficient` and `TauCeti.G2ShortRoot.loweringCoefficient`.
* `TauCeti.G2ShortRoot.isSerreSystem`: the Chevalley--Serre relations between them over `ℤ`.
* `TauCeti.G2ShortRoot.serreRepresentation`: the induced representation of the type-`G₂` Serre
  Lie algebra.

## Main results

* `TauCeti.G2ShortRoot.range_weight`: the weights are exactly the short roots and zero, with
  `TauCeti.G2ShortRoot.weight_rev` and `TauCeti.G2ShortRoot.sum_weight` recording the symmetry of
  the diagram about the origin.
* `TauCeti.G2ShortRoot.span_range_weight_eq_top`: the weights span the character lattice.
* `TauCeti.G2ShortRoot.raisingMatrix_pow_three` and `loweringMatrix_pow_three`: every generator
  cubes to zero, with `raisingMatrix_one_mul_self` and `loweringMatrix_one_mul_self` recording
  that the long-root generators already square to zero.

## References

The numbering and coordinates follow N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*,
Plate IX. The seven-dimensional representation and its weight diagram follow J. E. Humphreys,
*Introduction to Lie Algebras and Representation Theory*, §19.3 and §21.3, and J. C. Jantzen,
*Representations of Algebraic Groups*, II.2. The generator API and declaration order use
`TauCeti.Algebra.Lie.E7.Minuscule.Basic` as a formal template.
-/

public section

open scoped Matrix

namespace TauCeti.G2ShortRoot

open LieAlgebra TauCeti.DynkinType

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The integral generator matrices -/

/-- The Cartan generator `H_i`, acting on each weight vector by the `i`-th coordinate of its
weight. -/
def cartanMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  Matrix.diagonal fun a => weight a i

/-- The nonzero entries of the raising generators, indexed by their row: the `i`-th raising
generator carries the `(a+1)`-st weight vector to `raisingCoefficient i a` times the `a`-th. -/
@[expose] def raisingCoefficient : Fin 2 → Fin 7 → ℤ :=
  ![![1, 0, 2, 1, 0, 1, 0], ![0, 1, 0, 0, 1, 0, 0]]

/-- The entrywise definition of the raising coefficients. -/
@[simp] theorem raisingCoefficient_apply (i : Fin 2) (a : Fin 7) : raisingCoefficient i a =
    ![![1, 0, 2, 1, 0, 1, 0], ![0, 1, 0, 0, 1, 0, 0]] i a := by
  rw [raisingCoefficient]

/-- The nonzero entries of the lowering generators, indexed by their row: the `i`-th lowering
generator carries the `(a-1)`-st weight vector to `loweringCoefficient i a` times the `a`-th. -/
@[expose] def loweringCoefficient : Fin 2 → Fin 7 → ℤ :=
  ![![0, 1, 0, 1, 2, 0, 1], ![0, 0, 1, 0, 0, 1, 0]]

/-- The entrywise definition of the lowering coefficients. -/
@[simp] theorem loweringCoefficient_apply (i : Fin 2) (a : Fin 7) : loweringCoefficient i a =
    ![![0, 1, 0, 1, 2, 0, 1], ![0, 0, 1, 0, 0, 1, 0]] i a := by
  rw [loweringCoefficient]

/-- The raising generators `E₁` and `E₂`. -/
@[expose]
def raisingMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  Matrix.of fun a b => if b.val = a.val + 1 then raisingCoefficient i a else 0

/-- The lowering generators `F₁` and `F₂`. -/
@[expose]
def loweringMatrix (i : Fin 2) : Matrix (Fin 7) (Fin 7) ℤ :=
  Matrix.of fun a b => if a.val = b.val + 1 then loweringCoefficient i a else 0

/-- **The entries of the raising generators.** They are supported on the superdiagonal: the
weights are listed in decreasing order, so a raising generator either moves a weight vector one
step up the list or kills it. -/
@[simp]
theorem raisingMatrix_apply (i : Fin 2) (a b : Fin 7) :
    raisingMatrix i a b = if b.val = a.val + 1 then raisingCoefficient i a else 0 := by
  rw [raisingMatrix, Matrix.of_apply]

/-- **The entries of the lowering generators.** They are supported on the subdiagonal: the
weights are listed in decreasing order, so a lowering generator either moves a weight vector one
step down the list or kills it. -/
@[simp]
theorem loweringMatrix_apply (i : Fin 2) (a b : Fin 7) :
    loweringMatrix i a b = if a.val = b.val + 1 then loweringCoefficient i a else 0 := by
  rw [loweringMatrix, Matrix.of_apply]

/-- The entrywise formula for the diagonal Cartan generator matrix. -/
@[simp]
theorem cartanMatrix_apply (i : Fin 2) (a b : Fin 7) :
    cartanMatrix i a b = if a = b then weight a i else 0 := by
  classical
  rw [cartanMatrix, Matrix.diagonal_apply]

/-! ## Chevalley--Serre relations -/

/-- The integral generator matrices satisfy the Chevalley--Serre relations of type `G₂`, for the
Cartan matrix whose entry `(i, j)` is the value of the `j`-th simple root on the `i`-th simple
coroot. -/
theorem isSerreSystem :
    IsSerreSystem ℤ CartanMatrix.G₂ cartanMatrix raisingMatrix loweringMatrix where
  lie_H_H := by decide +kernel
  lie_E_F_self := by decide +kernel
  lie_E_F_of_ne := by decide +kernel
  lie_H_E := by decide +kernel
  lie_H_F := by decide +kernel
  ad_pow_lie_E_E := by decide +kernel
  ad_pow_lie_F_F := by decide +kernel

/-- The explicit integral seven-dimensional representation of the type-`G₂` Serre Lie algebra. -/
noncomputable def serreRepresentation :
    Matrix.ToLieAlgebra ℤ CartanMatrix.G₂ →ₗ⁅ℤ⁆ Matrix (Fin 7) (Fin 7) ℤ :=
  serreLift isSerreSystem

/-- The integral Serre representation sends `H_i` to the Cartan generator matrix. -/
@[simp]
theorem serreRepresentation_serreH (i : Fin 2) :
    serreRepresentation (serreH ℤ CartanMatrix.G₂ i) = cartanMatrix i :=
  serreLift_serreH isSerreSystem i

/-- The integral Serre representation sends `E_i` to the raising generator matrix. -/
@[simp]
theorem serreRepresentation_serreE (i : Fin 2) :
    serreRepresentation (serreE ℤ CartanMatrix.G₂ i) = raisingMatrix i :=
  serreLift_serreE isSerreSystem i

/-- The integral Serre representation sends `F_i` to the lowering generator matrix. -/
@[simp]
theorem serreRepresentation_serreF (i : Fin 2) :
    serreRepresentation (serreF ℤ CartanMatrix.G₂ i) = loweringMatrix i :=
  serreLift_serreF isSerreSystem i

/-! ## Nilpotency of the generators -/

/-- Every raising generator cubes to zero. -/
@[simp]
theorem raisingMatrix_pow_three (i : Fin 2) : raisingMatrix i ^ 3 = 0 := by
  revert i; decide

/-- Every lowering generator cubes to zero. -/
@[simp]
theorem loweringMatrix_pow_three (i : Fin 2) : loweringMatrix i ^ 3 = 0 := by
  revert i; decide

/-- The long-root raising generator squares to zero. -/
@[simp]
theorem raisingMatrix_one_mul_self : raisingMatrix 1 * raisingMatrix 1 = 0 := by decide

/-- The long-root lowering generator squares to zero. -/
@[simp]
theorem loweringMatrix_one_mul_self : loweringMatrix 1 * loweringMatrix 1 = 0 := by decide

/-- The short-root raising generator squares to twice a single unit matrix. -/
@[simp]
theorem raisingMatrix_zero_mul_self :
    raisingMatrix 0 * raisingMatrix 0 = 2 • Matrix.single 2 4 1 := by decide

/-- The short-root lowering generator squares to twice a single unit matrix. -/
@[simp]
theorem loweringMatrix_zero_mul_self :
    loweringMatrix 0 * loweringMatrix 0 = 2 • Matrix.single 4 2 1 := by decide

end TauCeti.G2ShortRoot
